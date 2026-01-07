#!/usr/bin/env python3
# ======================================================================
# Mivi -- Ein MIDI-Synthesizer und -Visualizer
# ======================================================================
#
# Version vom 7. Januar 2026.
#
# BESCHREIBUNG:
# Dieses Programm liest Standard-MIDI-Dateien (.mid), parst deren
# binäre Event-Struktur und visualisiert die Noten in einem "Falling
# Notes"-Stil (ähnlich dem Spiel Synthesia). Gleichzeitig wird eine
# Audio-Spur generiert und synchron zur Grafik abgespielt.
#
# VERWENDUNG:
#   python3 mivi.py [dateiname.mid] [optionen]
#
# ARGUMENTE:
#   dateiname.mid   : Pfad zur MIDI-Datei (Standard: test.mid).
#   -tm, --timidity : Nutzt das externe Tool 'timidity' für die
#                     Audio-Erzeugung (bessere Qualität, erfordert
#                     Installation).
#   -b, --bpm       : Erzwingt eine feste BPM-Rate (überschreibt
#                     Tempo-Events der Datei).
#
# FUNKTIONSWEISE:
# 1. Parsing:
#    Die Datei wird Byte für Byte analysiert (MThd/MTrk Chunks).
#    Delta-Zeiten (Variable Length Quantities) werden unter Berück-
#    sichtigung von Tempo-Maps in absolute Sekunden umgerechnet.
#    Running-Status und Meta-Events werden verarbeitet.
#
# 2. Audio-Synthese:
#    a) Intern (Standard): Additive Synthese mittels NumPy. Erzeugt
#       Sinuswellen mit Obertönen basierend auf MIDI-Noten.
#    b) Extern (-tm): Ruft 'timidity' auf, um die MIDI-Datei in eine
#       temporäre WAV-Datei zu wandeln.
#
# 3. Visualisierung:
#    Pygame lädt das generierte Audio und zeichnet basierend auf der
#    aktuellen Abspielposition die Notenblöcke und eine aktive
#    Klaviatur in Echtzeit.
#
# ======================================================================

import pygame
import numpy as np
import os
import sys
import wave
import math
import struct
import subprocess
import argparse

# ======================================================================
# KLASSE: Minimaler MIDI-Parser
# Behält Channel-Informationen für den Synth bei.
# ======================================================================
class MidiParser:
    def __init__(self, filename, target_bpm=None):
        self.filename = filename
        self.target_bpm = target_bpm
        self.ticks_per_beat = 480
        self.tracks_data = []  # Liste von Listen mit Events
        self.tempo_map = []    # [(abs_tick, tempo_in_us_per_beat)]
        
        try:
            with open(self.filename, 'rb') as f:
                self._parse_file(f)
        except Exception as e:
            print(f"Fehler beim Parsen der MIDI-Datei: {e}")
            sys.exit(1)

    def _read_variable_length(self, f):
        value = 0
        while True:
            byte_s = f.read(1)
            if not byte_s: break
            byte = ord(byte_s)
            value = (value << 7) | (byte & 0x7F)
            if not (byte & 0x80):
                break
        return value

    def _read_int_be(self, f, size):
        return int.from_bytes(f.read(size), byteorder='big')

    def _parse_file(self, f):
        chunk_type = f.read(4)
        if chunk_type != b'MThd':
            raise ValueError("Kein gültiges MIDI-File (MThd fehlt)")
        
        _length = self._read_int_be(f, 4)
        _format = self._read_int_be(f, 2)
        num_tracks = self._read_int_be(f, 2)
        division = self._read_int_be(f, 2)

        if division & 0x8000:
            raise NotImplementedError(
                "SMPTE Timecode Format wird nicht unterstützt.")
        self.ticks_per_beat = division

        for _ in range(num_tracks):
            self._parse_track(f)

        if self.target_bpm is not None and self.target_bpm > 0:
            # Formel: 60.000.000 / BPM = Mikrosekunden pro Beat
            new_tempo = int(60000000 / self.target_bpm)
            # Wir setzen eine einzige Tempo-Anweisung ganz an
            # den Anfang (Tick 0)
            self.tempo_map = [(0, new_tempo)]
            print(f"BPM Override aktiv: {self.target_bpm} BPM")
        else:
            if not self.tempo_map:
                self.tempo_map.append((0, 500000)) # Default 120 BPM
            self.tempo_map.sort(key=lambda x: x[0])

    def _parse_track(self, f):
        while True:
            pos = f.tell()
            chunk_type = f.read(4)
            if chunk_type == b'MTrk':
                length = self._read_int_be(f, 4)
                track_end = f.tell() + length
                break
            elif chunk_type == b'':
                return # EOF
            else:
                pass # Padding ignorieren

        abs_tick = 0
        running_status = 0
        events = []
        
        while f.tell() < track_end:
            delta = self._read_variable_length(f)
            abs_tick += delta
            
            byte = ord(f.read(1))
            
            if byte >= 0x80:
                status = byte
                running_status = status
            else:
                status = running_status
                f.seek(-1, 1)

            # System Common Messages abfangen, die sonst den Stream zerstören
            if 0xF1 <= status <= 0xF3:
                # F1 (MTC Quarter Frame): 1 Datenbyte
                # F2 (Song Position): 2 Datenbytes
                # F3 (Song Select): 1 Datenbyte
                data_bytes = {0xF1: 1, 0xF2: 2, 0xF3: 1}
                f.read(data_bytes[status])
                # WICHTIG: System Messages löschen Running Status laut Spec nicht zwingend, 
                # aber Channel Messages erwarten Status im Bereich 0x80-0xEF.
                # Sicherheitshalber hier running_status ungültig machen, falls implementiert.
                running_status = 0 
            elif status >= 0xF8:
                # Realtime Messages (Clock, Start, Stop...) werden ignoriert
                # Sie haben KEINE Datenbytes. Nichts tun.
                pass

            if 0x80 <= status <= 0xEF:
                channel = status & 0x0F
                cmd = status & 0xF0
                
                if cmd == 0x80: # Note Off
                    note = ord(f.read(1))
                    vel = ord(f.read(1))
                    events.append({'tick': abs_tick, 'type': 'note_off', 'note': note, 'ch': channel})
                elif cmd == 0x90: # Note On
                    note = ord(f.read(1))
                    vel = ord(f.read(1))
                    if vel == 0:
                        events.append({'tick': abs_tick, 'type': 'note_off', 'note': note, 'ch': channel})
                    else:
                        events.append({'tick': abs_tick, 'type': 'note_on', 'note': note, 'ch': channel, 'vel': vel})
                elif cmd in [0xA0, 0xB0, 0xE0]: f.read(2)
                elif cmd in [0xC0, 0xD0]: f.read(1)

            elif status == 0xF0 or status == 0xF7:
                running_status = 0
                length = self._read_variable_length(f)
                f.read(length)

            elif status == 0xFF:
                running_status = 0
                type_code = ord(f.read(1))
                length = self._read_variable_length(f)
                data = f.read(length)
                
                if type_code == 0x51: # Tempo
                    microseconds = int.from_bytes(data, byteorder='big')
                    self.tempo_map.append((abs_tick, microseconds))
                elif type_code == 0x2F: # End of Track
                    break

        self.tracks_data.append(events)

    def _tick_to_seconds(self, target_tick):
        current_time = 0.0
        current_tick = 0
        current_micros_per_beat = 500000 
        
        for map_tick, tempo in self.tempo_map:
            if map_tick > target_tick: break
            tick_diff = map_tick - current_tick
            current_time += tick_diff * (current_micros_per_beat / 1000000.0) / self.ticks_per_beat
            current_tick = map_tick
            current_micros_per_beat = tempo
            
        tick_diff = target_tick - current_tick
        current_time += tick_diff * (current_micros_per_beat / 1000000.0) / self.ticks_per_beat
        return current_time

    def get_parsed_notes(self):
        """
        Gibt eine Liste von Dictionaries zurück (Notenliste, Farbe, Channel-ID).
        Format Note: {'midi': 60, 'start': 1.2, 'dur': 0.5, 'vel': 100}
        """
        processed_tracks = []
                
        channel_colors = {
            0: (0, 220, 220), 1: (255, 0, 200), 2: (255, 220, 0),
            3: (0, 200, 100), 9: (150, 150, 150) # Drums
        }
        
        for track_events in self.tracks_data:
            notes = []
            active_notes = {} # (channel, note) -> (start_tick, velocity)
            track_color = (200, 200, 200)
            track_channel = 0
            
            for event in track_events:
                evt_type = event['type']
                tick = event['tick']
                
                if evt_type == 'note_on':
                    key = (event['ch'], event['note'])
                    active_notes[key] = (tick, event['vel'])
                    
                    if track_color == (200, 200, 200):
                        track_channel = event['ch']
                        track_color = channel_colors.get(event['ch'], 
                            ((event['ch'] * 50) % 255, (event['ch'] * 80) % 255, 200))

                elif evt_type == 'note_off':
                    key = (event['ch'], event['note'])
                    if key in active_notes:
                        start_tick, vel = active_notes.pop(key)
                        start_sec = self._tick_to_seconds(start_tick)
                        end_sec = self._tick_to_seconds(tick)
                        duration = end_sec - start_sec

                        note_color = channel_colors.get(event['ch'], 
                            ((event['ch'] * 50) % 255, (event['ch'] * 80) % 255, 200))                        
                        notes.append({
                            'midi': event['note'],
                            'start': start_sec,
                            'dur': duration,
                            'vel': vel,
                            'ch': event['ch'],
                            'color': note_color
                        })
            
            if notes:
                processed_tracks.append({'notes': notes, 'color': track_color, 'channel': track_channel})
                
        return processed_tracks

# ======================================================================
# KLASSE: Python Software-Synthesizer
# ======================================================================
class MidiSynth:
    def __init__(self, sample_rate=44100):
        self.sample_rate = sample_rate
        # Standard Parameter
        self.base_overtones = [1.0, 0.5, 0.3, 0.1]
        self.attack_time = 0.05
        self.release_time = 0.1
    
    def _midi_to_freq(self, midi_note):
        return 440.0 * (2 ** ((midi_note - 69) / 12.0))

    def _generate_wave(self, freq, duration_sec, velocity=127, overtones=None):
        if freq <= 0: return None
        if overtones is None: overtones = self.base_overtones
        
        # Velocity als Lautstärke (0.0 bis 1.0)
        gain = (velocity / 127.0) * 0.5 # Headroom lassen
        
        total_time = duration_sec + self.release_time
        num_samples = int(total_time * self.sample_rate)
        
        # Zeitvektor
        t = np.linspace(0, total_time, num_samples, endpoint=False)
        signal = np.zeros(num_samples)
        
        # Additive Synthese
        for i, intensity in enumerate(overtones):
            harmonic_freq = freq * (i + 1)
            # Nyquist-Grenze beachten
            if harmonic_freq < self.sample_rate / 2:
                signal += intensity * np.sin(2 * np.pi * harmonic_freq * t)
        
        # Normalisieren durch Summe der Obertöne
        signal /= np.sum(overtones)
        signal *= gain
        
        # ADSR Envelope (simpel: Attack, Sustain, Release)
        envelope = np.ones(num_samples)
        
        # Attack
        n_attack = int(self.attack_time * self.sample_rate)
        if n_attack > num_samples: n_attack = num_samples
        envelope[:n_attack] = np.linspace(0, 1, n_attack)
        
        # Release (am Ende der Note)
        n_sustain_end = int(duration_sec * self.sample_rate)
        if n_sustain_end < num_samples:
            len_release = num_samples - n_sustain_end
            envelope[n_sustain_end:] = np.linspace(1, 0, len_release)
            
        return signal * envelope

    def generate_track_audio(self, notes, channel_id):
        """Erzeugt ein Numpy-Array für eine ganze Spur."""
        if not notes:
            return np.array([], dtype=np.float32)

        # Instrumentierung basierend auf Channel (einfach)
        current_overtones = self.base_overtones
        if channel_id == 9: # Drums
            # Sehr simple Drums: Nur Grundton, sehr kurzes Decay
            self.release_time = 0.05
            current_overtones = [1.0] # Eher wie ein Klick/Thump
        elif channel_id % 2 == 0:
            # "Piano"-ähnlich
            current_overtones = [1.0, 0.6, 0.3, 0.1, 0.05]
            self.release_time = 0.15
        else:
            # "Streicher/Orgel"-ähnlich
            current_overtones = [0.8, 0.8, 0.5, 0.2]
            self.release_time = 0.3
            
        # Gesamtlänge berechnen
        last_end = max(n['start'] + n['dur'] for n in notes)
        total_len_sec = last_end + self.release_time + 1.0
        total_samples = int(total_len_sec * self.sample_rate)
        
        buffer = np.zeros(total_samples, dtype=np.float32)
        
        # Performance Warnung bei vielen Noten
        
        for i, note in enumerate(notes):
            midi = note['midi']

            # Ignoriere Keyswitches und unhörbare Noten
            # if midi < 12: 
            #     continue

            actual_ch = note.get('ch', channel_id)
            if actual_ch == 9:
                # continue # Kann auch vollständig entfallen
                # Als kurzen Klick/Thump spielen (wie ursprünglich gedacht):
                freq = 100.0
                wave_data = self._generate_wave(freq, 0.05, note['vel'], [1.0])
            else:
                freq = self._midi_to_freq(midi)
                wave_data = self._generate_wave(freq, note['dur'], note['vel'], current_overtones)

            if wave_data is not None:
                start_s = int(note['start'] * self.sample_rate)
                end_s = start_s + len(wave_data)
                
                # Buffer erweitern falls nötig (sollte durch Vorberechnung selten passieren)
                if end_s > len(buffer):
                    buffer = np.pad(buffer, (0, end_s - len(buffer)))
                
                buffer[start_s:end_s] += wave_data

        return buffer

def save_mixed_audio(track_buffers, filename="output.wav", sample_rate=44100):
    if not track_buffers:
        print("Keine Audiodaten generiert.")
        return

    # Maximale Länge finden
    max_len = max(len(b) for b in track_buffers)
    mixed = np.zeros(max_len, dtype=np.float32)
    
    # Mischen
    print("Mische Spuren...")
    for b in track_buffers:
        mixed[:len(b)] += b
        
    # Normalisieren (Verhindern von Clipping)
    max_val = np.max(np.abs(mixed))
    if max_val > 0:
        mixed = mixed / max_val * 0.9 # 90% Pegel
        
    # Konvertieren zu 16-bit PCM
    audio_int16 = (np.clip(mixed, -1.0, 1.0) * 32767).astype(np.int16)
    
    with wave.open(filename, 'w') as f:
        f.setnchannels(1) # Mono
        f.setsampwidth(2) # 2 Bytes (16 bit)
        f.setframerate(sample_rate)
        f.writeframes(audio_int16.tobytes())
    print(f"WAV gespeichert: {filename}")

# ======================================================================
# AUDIO GENERIERUNG: Timidity
# ======================================================================
def generate_wav_with_timidity(midi_path, output_wav):
    print(f"Konvertiere MIDI zu WAV mit Timidity: {midi_path} -> {output_wav}")
    try:
        # -Ow: Output Mode Wav
        # -o: Output Filename
        cmd = ['timidity', midi_path, '-Ow', '-o', output_wav, '-A160', '--preserve-silence']
        subprocess.check_call(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.STDOUT)
        return True
    except FileNotFoundError:
        print("FEHLER: 'timidity' wurde nicht gefunden. Bitte "
            "installieren (sudo apt install timidity) oder den "
            "internen Synth nutzen (ohne -tm).")
        return False
    except subprocess.CalledProcessError as e:
        print(f"FEHLER bei der Ausführung von Timidity: {e}")
        return False

# ======================================================================
# KLASSE: Visualisierung
# Kombiniert: Init auf Stereo (für Timidity), Loop über Dict-Structure
# ======================================================================
class Visualizer:
    def __init__(self, width=1024, height=768):
        pygame.init()
        # Audio init: Channels=2 für Stereokompatibilität mit Timidity.
        # Interne Mono-WAVs werden von Pygame automatisch zentriert.
        pygame.mixer.init(frequency=44100, size=-16, channels=2, buffer=2048)
        
        self.width = width
        self.height = height
        self.screen = pygame.display.set_mode((width, height))
        pygame.display.set_caption("Mivi – MIDI visualizer")
        
        self.clock = pygame.time.Clock()
        self.is_running = True
        
        self.pixels_per_second = 150 
        self.keyboard_height = 120
        self.note_area_height = self.height - self.keyboard_height
        
        self.min_midi = 21  # A0
        self.max_midi = 108 # C8
        
        self._init_keyboard_layout()

    def _init_keyboard_layout(self):
        white_key_count = 0
        for m in range(self.min_midi, self.max_midi + 1):
            if not self._is_black_key(m):
                white_key_count += 1
        
        self.wk_width = self.width / white_key_count
        self.bk_width = self.wk_width * 0.65
        
    def _is_black_key(self, midi_note):
        return (midi_note % 12) in [1, 3, 6, 8, 10]

    def _get_x_pos(self, midi_note):
        current_wk_index = 0
        for m in range(self.min_midi, midi_note):
            if not self._is_black_key(m):
                current_wk_index += 1
        x = current_wk_index * self.wk_width
        if self._is_black_key(midi_note):
            return x - (self.bk_width / 2) 
        return x

    def run(self, tracks_data, wav_file):
        try:
            pygame.mixer.music.load(wav_file)
            pygame.mixer.music.play()
        except pygame.error as e:
            print(f"Konnte Audio nicht laden: {e}")
            return

        start_ticks = pygame.time.get_ticks()
        
        while self.is_running:
            for event in pygame.event.get():
                if event.type == pygame.QUIT:
                    self.is_running = False

            if pygame.mixer.music.get_busy():
                current_time = pygame.mixer.music.get_pos() / 1000.0
            else:
                current_time = (pygame.time.get_ticks() - start_ticks) / 1000.0

            self.screen.fill((30, 30, 35))
            active_midi_notes = {} 
            
            # Noten zeichnen. Erwartet das Dict-Format vom
            # Parser ('notes', 'color', 'channel')
            for track in tracks_data:
                # Fallunterscheidung falls durch Merge etwas
                # durcheinander geraten ist
                if isinstance(track, dict):
                    events = track['notes']
                    color = track['color']
                else: 
                    # Fallback falls jemand den Parser austauscht
                    # auf Tuple
                    events = track[0]
                    color = track[1]
                
                for note in events:
                    if note['start'] > current_time + 5.0: continue 
                    if (note['start'] + note['dur']) < current_time - 1.0: continue

                    time_diff = note['start'] - current_time
                    note_y = self.note_area_height - (time_diff * self.pixels_per_second)
                    note_h = note['dur'] * self.pixels_per_second
                    
                    draw_y = note_y - note_h
                    
                    if draw_y < self.height and (draw_y + note_h) > 0:
                        midi = note['midi']
                        if midi < self.min_midi or midi > self.max_midi: continue
                        
                        x = self._get_x_pos(midi)
                        w = self.bk_width if self._is_black_key(midi) else self.wk_width
                        
                        is_active = note['start'] <= current_time <= (note['start'] + note['dur'])
                        # draw_color = note.get('color', color)
                        base_note_color = note.get('color', color)
                        if is_active:
                            active_midi_notes[midi] = base_note_color
                            draw_color = tuple(min(255, c + 60) for c in base_note_color)
                        else:
                            draw_color = base_note_color
                        
                        pygame.draw.rect(self.screen, draw_color,
                            (x + 1, draw_y, w - 2, note_h), border_radius=4)

            self._draw_keyboard(active_midi_notes)
            pygame.display.flip()
            self.clock.tick(60)
        pygame.quit()

    def _draw_keyboard(self, active_notes):
        # Weiße Tasten
        wk_index = 0
        for m in range(self.min_midi, self.max_midi + 1):
            if not self._is_black_key(m):
                x = wk_index * self.wk_width
                fill_color = (220, 220, 220)
                if m in active_notes:
                    base_c = active_notes[m]
                    fill_color = tuple(min(255, c + 100) for c in base_c)
                
                pygame.draw.rect(self.screen, fill_color,
                    (x, self.note_area_height, self.wk_width - 1, self.keyboard_height),
                    border_radius=0, border_bottom_left_radius=5, border_bottom_right_radius=5)
                wk_index += 1
        
        # Schwarze Tasten
        for m in range(self.min_midi, self.max_midi + 1):
            if self._is_black_key(m):
                x = self._get_x_pos(m)
                fill_color = (20, 20, 20)
                if m in active_notes:
                    base_c = active_notes[m]
                    fill_color = tuple(min(255, c + 50) for c in base_c)
                pygame.draw.rect(self.screen, fill_color,
                    (x, self.note_area_height, self.bk_width, self.keyboard_height * 0.65),
                    border_radius=0, border_bottom_left_radius=3, border_bottom_right_radius=3)

# ======================================================================
# MAIN
# ======================================================================
if __name__ == "__main__":
    parser_args = argparse.ArgumentParser(description="Python MIDI Visualizer & Synth")
    parser_args.add_argument("filename", nargs="?", default="test.mid", help="Pfad zur MIDI-Datei")
    parser_args.add_argument("-tm", "--timidity", action="store_true", help="Benutze 'timidity' statt internem Synth")
    parser_args.add_argument("-b", "--bpm", type=float, help="Erzwinge eine feste BPM (überschreibt Tempo-Events)")
    
    args = parser_args.parse_args()
    midi_file = args.filename

    if not os.path.exists(midi_file):
        print(f"Datei nicht gefunden: {midi_file}")
        print("Verwendung: python3 mivi.py <datei.mid> [-tm]")
        sys.exit(1)

    # Vorsicht: Diese temporäre Datei wird sowohl überschrieben als
    # auch später wieder gelöscht.
    temp_wav = "temp_audio.wav"

    # 1. MIDI Parsen
    # Wir benutzen den Parser aus Datei 0, da er reichhaltigere
    # Daten (Channel) liefert.
    print(f"Lese MIDI: {midi_file}...")
    parser = MidiParser(midi_file, target_bpm=args.bpm)
    tracks_struct = parser.get_parsed_notes()
    print(f"{len(tracks_struct)} Spuren gefunden.")

    # 2. Audio Synthese
    audio_success = False

    if args.timidity:
        # Externer Timidity Aufruf
        if generate_wav_with_timidity(midi_file, temp_wav):
            audio_success = True
    else:
        # Interner Python Synth
        print("Synthetisiere Audio (Pure Python)... Bitte warten.")
        synth = MidiSynth()
        audio_buffers = []
        
        for i, track in enumerate(tracks_struct):
            notes = track['notes']
            channel = track['channel']
            if not notes: continue
            
            print(f"  Synthetisiere Spur {i+1}/{len(tracks_struct)} (Ch {channel}, {len(notes)} Noten)...")
            buf = synth.generate_track_audio(notes, channel)
            audio_buffers.append(buf)

        save_mixed_audio(audio_buffers, temp_wav)
        audio_success = True

    if not audio_success:
        print("Audio-Erstellung fehlgeschlagen. Abbruch.")
        sys.exit(1)

    # 3. Visualizer
    print("Starte Visualisierung...")
    # Etwas breiter als Standard, um Platz zu haben
    viz = Visualizer(width=1200, height=800)

    try:
        viz.run(tracks_struct, temp_wav)
    finally:
        if os.path.exists(temp_wav):
            try:
                os.remove(temp_wav)
            except: pass
