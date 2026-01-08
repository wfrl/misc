#!/usr/bin/env python3
# ======================================================================
# Lilysynth-Klangerzeuger
# ======================================================================
# Version vom 8. Jan. 2026.
#
# Wandelt einen vorgelegten Notentext (Lilypond-Syntax) in Klänge um,
# die als WAV-Datei gespeichert oder von einem Spielautomaten gespielt
# werden. Der Spielautomat ist an Synthesia angelehnt, das heißt, es
# wandern Balken nach unten zur Klaviatur.

import numpy as np
import wave
import re
import math
import os
import io

# ======================================================================
# KLASSE: Synth
# ======================================================================
# Diese Klasse ist das Herzstück des Synthesizers. Sie wandelt Text
# (Lilypond) in rohe Audio-Daten (NumPy-Arrays) um.
#
# Funktionsweise im Überblick:
# 1. Konfiguration: BPM, Sample-Rate und Klangfarbe (Obertöne).
# 2. Parsing: Zerlegen des Strings in Noten-Events
#    (Frequenz, Startzeit, Dauer).
# 3. Synthese: Generieren von Wellenformen für jedes Event mittels
#    additiver Synthese.
# ======================================================================

class Synth:
    def __init__(self, bpm=100, sample_rate=44100, transpose=0,
        time="4/4", validate=True, instrument = None):
        # BPM (Beats per Minute): Bestimmt die Geschwindigkeit des Stücks.
        self.bpm = bpm
        
        # Sample Rate: Standard ist 44100 Hz (CD-Qualität).
        # Das bedeutet, 1 Sekunde Audio besteht aus 44100 Werten.
        self.sample_rate = sample_rate
        
        # Transpose: Verschiebung in Halbtönen. 
        # +12 = eine Oktave höher, -12 = eine Oktave tiefer.
        self.transpose = transpose

        # Validierungs-Einstellung
        self.validate = validate
        
        # Taktart parsen (z.B. "3/4")
        try:
            num, den = map(int, time.split('/'))
            # Berechnung der Ziel-Länge in "Viertelnoten-Einheiten":
            # Viertel (4) = 1.0, Achtel (8) = 0.5
            self.target_bar_len = num * (4.0 / den)
        except ValueError:
            print(f"Fehler: Taktart '{time}' konnte nicht gelesen werden. Nutze 4/4.")
            self.target_bar_len = 4.0
        
        # --- KLANGSYNTHESE-PARAMETER ---
        
        # Additive Synthese basiert auf der Idee, dass jeder Klang aus
        # einer Summe von Sinuswellen besteht (Grundton + Obertöne).
        # self.overtones definiert die Lautstärke der Harmonischen:
        # Index 0: Grundton (1. Harmonische)
        # Index 1: 1. Oberton (2. Harmonische, doppelte Frequenz)
        # Index 2: 2. Oberton (3. Harmonische, dreifache Frequenz) usw.
        self.overtones = [1.0, 0.6, 0.3, 0.1, 0.05]
        
        # Hüllkurve (ADSR - Attack, Decay, Sustain, Release)
        # Hier vereinfacht implementiert:
        # Attack: Zeit bis zur vollen Lautstärke (verhindert "Knacken" am Anfang).
        # Release: Ausklingzeit nach dem Ende der Note.
        self.attack_time = 0.05
        self.release_time = 0.2
        
        # Referenzstimmung: Kammerton A ist 440 Hz.
        self.base_a4 = 440.0
        
        # Mapping von Notennamen zu Halbtonabständen relativ zu C.
        # Dies wird für die Frequenzberechnung benötigt.
        self.note_offsets = {
            'c': 0, 'd': 2, 'e': 4, 'f': 5, 'g': 7, 'a': 9, 'b': 11, 'r': None
        }

        # Ggf. Instrument auswählen
        if instrument is not None:
            preset_method = getattr(self, instrument, None)
            if callable(preset_method):
                preset_method()
            else:
                print(f"Instrument '{instrument}' nicht gefunden, nutze Default.")

    # ------------------------------------------------------------------
    # HILFSFUNKTION: Frequenzberechnung
    # ------------------------------------------------------------------
    # Berechnet die Frequenz in Hertz (Hz) für eine gegebene Note.
    # Verwendet die Formel für gleichstufige Stimmung (12-TET).
    #
    # Formel: f = f_ref * 2^(n / 12)
    # n ist der Abstand in Halbtönen zum Referenzton (A4).
    # ------------------------------------------------------------------
    def _get_freq(self, note_name, octave_shift, accidentals=0):
        # 'r' steht für Rest (Pause) -> 0 Hz
        if note_name == 'r': return 0.0
        
        # Basis-Abstand der Note (z.B. 'g' ist der 7. Halbton nach 'c')
        base_offset = self.note_offsets.get(note_name, 0)
        
        # MIDI-Berechnung:
        # Im MIDI-Standard ist C4 (Middle C) die Nummer 60.
        # Lilypond definiert 'c' (ohne Strich) oft als C3 (Kleines c).
        # Hier wurde 48 als Basis für C3 gewählt.
        #
        # Die Formel addiert:
        # 48 (Basis C3) + Notenabstand + Vorzeichen + (Oktavsprünge * 12) + globale Transposition
        midi_pitch = 48 + base_offset + accidentals + (octave_shift * 12) + self.transpose
        
        # Berechnung der Frequenz relativ zu A4 (MIDI 69)
        return self.base_a4 * (2 ** ((midi_pitch - 69) / 12.0))

    # ------------------------------------------------------------------
    # KERNSYSTEM: Wellenform-Generierung
    # ------------------------------------------------------------------
    # Erzeugt ein NumPy-Array mit den Samples für einen einzelnen Ton.
    # Hier passiert die eigentliche "Magie" der Tonerzeugung.
    # ------------------------------------------------------------------
    def _generate_wave(self, freq, duration_sec):
        # Pausen erzeugen kein Array (werden später im Puffer übersprungen)
        if freq == 0: return None
        
        # Die Gesamtlänge des Samples beinhaltet die Notendauer PLUS
        # die Ausklingzeit (Release)
        total_time = duration_sec + self.release_time
        num_samples = int(total_time * self.sample_rate)
        
        # Zeit-Achse erzeugen: Ein Array von 0 bis total_time
        t = np.linspace(0, total_time, num_samples, endpoint=False)
        
        # 1. Obertöne aufsummieren (Additive Synthese)
        signal = np.zeros(num_samples)
        for i, intensity in enumerate(self.overtones):
            # Frequenz des Obertons: Grundton * (Index + 1)
            harmonic_freq = freq * (i + 1)
            
            # Nyquist-Theorem: Wir dürfen keine Frequenzen erzeugen, die höher sind
            # als die halbe Samplerate, sonst entstehen hässliche Artefakte (Aliasing).
            if harmonic_freq < self.sample_rate / 2:
                # Sinuswelle addieren: Amplitude * sin(2 * pi * f * t)
                signal += intensity * np.sin(2 * np.pi * harmonic_freq * t)
        
        # Normalisieren: Damit die Summe der Amplituden nicht 1.0 überschreitet
        signal /= np.sum(self.overtones)
        
        # 2. Hüllkurve anwenden (Envelope)
        # Ohne Hüllkurve würde der Ton abrupt starten und enden (Klicken).
        envelope = np.ones(num_samples)
        
        # Fade-In (Attack)
        n_attack = int(self.attack_time * self.sample_rate)
        if n_attack > num_samples: n_attack = num_samples
        envelope[:n_attack] = np.linspace(0, 1, n_attack)
        
        # Fade-Out (Release)
        # Der Release beginnt erst NACH der musikalischen Dauer (Sustain).
        # Wir blenden den Ton sanft aus.
        n_sustain = int(duration_sec * self.sample_rate)
        if n_sustain < num_samples:
            # Linearer Abfall von 1 auf 0 für den Rest des Arrays
            envelope[n_sustain:] = np.linspace(1, 0, num_samples - n_sustain)
            
        # Modulation: Das rohe Signal wird mit der Hüllkurve multipliziert.
        return signal * envelope

    # ------------------------------------------------------------------
    # PARSER: Lilypond Syntax Interpretation
    # ------------------------------------------------------------------
    # Analysiert den String und extrahiert musikalische Events.
    # Rückgabe: Liste von Dictionaries {'freq', 'start', 'dur', 'tied'}
    # ------------------------------------------------------------------
    def parse(self, score):
        events = []
        
        # 1. Vorverarbeitung: Kommentare entfernen
        lines = score.split('\n')
        # Alles nach einem '%' wird ignoriert. Zeilenumbrüche werden
        # zu Leerzeichen.
        cleaned_score = "".join([line.split('%')[0] + " " for line in lines])
        
        # 2. Tokenisierung (Zerhacken des Strings)
        # Regex Erklärung:
        # < | > | \|        -> Erkennt Akkordklammern oder Taktstriche
        # [a-grs]           -> Notennamen (a-g) oder 'r' (rest/Pause) oder 's' (skip)
        # (?:is|es)?        -> Optional: Vorzeichen (is=kreuz, es=b)
        # (?:'|,)*          -> Optional: Oktavierung (' = hoch, , = tief)
        # (?:\d+)*          -> Optional: Dauer als Zahl (4, 8, 16...)
        # (?:\.)*           -> Optional: Punktierung (verlängert Note)
        # (?:~)?            -> Optional: Haltebogen (Tie)
        tokens = re.findall(
            r"<|>(?:\d+)*(?:\.)*(?:~)?|\||[a-grs](?:is|es)?(?:'|,)*(?:\d+)*(?:\.)*(?:~)?",
            cleaned_score)
        
        # Status-Variablen für den Parser-Durchlauf
        current_time = 0.0      # Aktuelle Zeitposition im Stück (in Sekunden)
        last_duration_val = 4   # Standard: Viertelnote, falls keine Zahl angegeben ist

        # --- Variablen der Takt-Validierung ---
        current_bar_duration = 0.0  # Summe der Beats im aktuellen Takt (4/4 = 4.0)
        bar_counter = 1             # In welchem Takt sind wir?
        # ---------------------------------------
        
        # Akkord-Logik:
        # In Lilypond laufen Noten innerhalb von < ... > gleichzeitig ab.
        # Die Zeit darf also innerhalb des Akkords nicht voranschreiten.
        in_chord = False
        chord_start_time = 0.0
        chord_max_duration = 0.0     # Für Audio-Zeit (Sekunden)
        chord_max_beat_len = 0.0     # Für Takt-Validierung (Notenwert)

        # Liste, um uns zu merken, welche Events zum aktuellen
        # Akkord gehören
        chord_event_indices = []
        
        raw_events = []
        
        for token in tokens:
            # Taktstriche: Validierung und Reset
            if token == '|': 
                # Wir prüfen nur, wenn wir NICHT im ersten Takt
                # sind (Auftakt gestatten)
                if self.validate and bar_counter > 1:
                    # Kleine Toleranz für Fließkomma-Ungenauigkeiten
                    if abs(current_bar_duration - self.target_bar_len) > 0.001:
                        print(f"WARNUNG in Takt {bar_counter}: Taktlänge ist {current_bar_duration:.2f} "
                              f"(erwartet {self.target_bar_len}).")
                
                # Reset für den nächsten Takt
                current_bar_duration = 0.0
                bar_counter += 1
                continue
            
            # Akkord-Beginn
            if token == '<':
                in_chord = True
                chord_start_time = current_time # Zeit einfrieren
                chord_max_duration = 0.0
                chord_max_beat_len = 0.0        # Reset: Beat-Länge im Akkord
                chord_event_indices = []        # Liste zurücksetzen für neuen Akkord
                continue
                
            # Akkord-Ende
            if token.startswith('>'):
                in_chord = False
                
                # Wir analysieren, ob am '>' eine Dauer oder ein Haltebogen hängt
                # Regex matcht z.B. bei ">4.~" -> dur='4', dots='.', tie='~'
                match_end = re.match(r">([\d]*)([\.]*)(~?)", token)
                dur_str, dots, tie_str = match_end.groups() if match_end else ("", "", "")
                
                # Variable für die Takt-Validierung dieses Akkords
                final_chord_beat_len = 0.0
                
                # Gibt es eine explizite Dauer am Akkord-Ende? (z.B. <...>4)
                has_explicit_duration = bool(dur_str or dots)
                
                if has_explicit_duration:
                    # Neue Dauer berechnen (ähnlich wie bei Einzelnoten)
                    if dur_str:
                        last_duration_val = int(dur_str)
                    
                    dq = 4.0 / last_duration_val
                    if dots:
                        factor = 1.0; add = 0.5
                        for _ in dots: 
                            factor += add
                            add /= 2
                        dq *= factor
                    
                    # Beat-Länge für Validierung setzen
                    final_chord_beat_len = dq
                    
                    dur_sec = dq * (60.0 / self.bpm)

                    # Wir gehen alle Noten durch, die in diesem Akkord gesammelt wurden,
                    # und überschreiben ihre Dauer mit der des Akkords.
                    for idx in chord_event_indices:
                        raw_events[idx]['dur'] = dur_sec
                    
                    # Die Zeit schreitet nun um diese Akkord-Dauer voran
                    current_time = chord_start_time + dur_sec
                else:
                    # Keine Dauer am '>' (z.B. nur <c e g>), also gilt die längste innere Note
                    final_chord_beat_len = chord_max_beat_len
                    current_time = chord_start_time + chord_max_duration

                # --- VALIDIERUNG: Akkord zum Takt addieren ---
                current_bar_duration += final_chord_beat_len

                # Haltebogen am Akkord? (z.B. <c e>~)
                # Diesen wenden wir auf alle Noten im Akkord an.
                if tie_str == '~':
                    for idx in chord_event_indices:
                        raw_events[idx]['tied'] = True
                        
                continue

            # 3. Noten-Details extrahieren
            # Wir zerlegen den Token (z.B. "cis'4.~") in seine Bestandteile
            match = re.match(r"([a-grs])(is|es)?(['+,]*)([\d]*)([\.]*)(~?)", token)
            if not match: continue
            
            note_base, acc, oct_str, dur_str, dots, tie_str = match.groups()
            
            # Dauer berechnen
            if dur_str:
                last_duration_val = int(dur_str)
                # 4.0 / 4 = 1.0 (Ganze Note), 4.0 / 8 = 0.5 (Achtel Note)
                dq = 4.0 / last_duration_val
            else:
                # Wenn keine Zahl steht, nimm die letzte verwendete
                dq = 4.0 / last_duration_val
            
            # Punktierungen verarbeiten
            # Ein Punkt verlängert die Note um die Hälfte ihres Wertes.
            # Zwei Punkte um die Hälfte + ein Viertel, etc.
            if dots:
                factor = 1.0; add = 0.5
                for _ in dots: 
                    factor += add
                    add /= 2
                dq *= factor
            
            # --- Takt-Zählung Update ---
            if in_chord:
                # Innerhalb eines Akkords addieren wir nicht sofort zum Takt,
                # sondern merken uns nur die längste Note.
                if dq > chord_max_beat_len:
                    chord_max_beat_len = dq
            else:
                # Normale Note: Addiere Wert zum Takt
                current_bar_duration += dq
            
            # Umrechnung von musikalischen Beats in Sekunden
            dur_sec = dq * (60.0 / self.bpm)
            
            # Tonhöhe bestimmen
            # Zähle ' für Oktaven nach oben, , für nach unten
            oct_shift = oct_str.count("'") - oct_str.count(",")
            
            # Vorzeichen auswerten
            acc_val = 1 if acc == 'is' else (-1 if acc == 'es' else 0)
            
            # Frequenz holen
            freq = self._get_freq(note_base, oct_shift, acc_val)
            
            # Startzeit festlegen
            start = chord_start_time if in_chord else current_time
            
            # Event speichern
            raw_events.append({
                'freq': freq, 
                'start': start, 
                'dur': dur_sec, 
                'tied': (tie_str == '~') # Merken, ob ein Haltebogen existiert
            })
            
            # Zeit fortschreiben
            if in_chord:
                # Index merken, falls wir die Dauer später überschreiben müssen (bei >4)
                chord_event_indices.append(len(raw_events) - 1)

                # Im Akkord merken wir uns nur die längste Dauer, addieren aber nicht
                chord_max_duration = max(chord_max_duration, dur_sec)
            else:
                # Normale Melodie: Zeit weiterschieben
                current_time += dur_sec

        # Nach dem Parsen: Haltebögen (Ties) verarbeiten
        return self._process_ties(raw_events)

    # ------------------------------------------------------------------
    # LOGIK: Haltebögen (Ties)
    # ------------------------------------------------------------------
    # Verbindet Noten, die durch '~' gebunden sind, zu einem langen Event.
    # Beispiel: c4~ c4 wird intern zu c2 (ohne neuen Anschlag dazwischen).
    # ------------------------------------------------------------------
    def _process_ties(self, events):
        if not events: return []
        
        # Sortieren nach Startzeit ist wichtig für die Logik
        events.sort(key=lambda x: x['start'])
        
        merged = []
        skip = set() # Indizes von Noten, die bereits in eine andere "hineingefressen" wurden
        
        for i, curr in enumerate(events):
            if i in skip: continue
            
            # Pausen müssen nicht gebunden werden
            if curr['freq'] == 0.0: continue
            
            # Wenn ein Tie-Symbol gefunden wurde...
            while curr['tied']:
                found = False
                # Erwarteter Start der nächsten Note ist das Ende der aktuellen
                exp_start = curr['start'] + curr['dur']
                
                # Suche nach der Fortsetzung
                for j in range(i + 1, len(events)):
                    if j in skip: continue
                    cand = events[j]
                    
                    # Check: Gleiche Frequenz? Startet sie genau jetzt?
                    if abs(cand['start'] - exp_start) < 0.001 and cand['freq'] == curr['freq']:
                        # Binden: Dauer addieren
                        curr['dur'] += cand['dur']
                        # Tie-Status übernehmen (falls die Kette weitergeht: c4~ c4~ c4)
                        curr['tied'] = cand['tied']
                        skip.add(j) # Die gefundene Note nicht mehr als eigenes Event behandeln
                        found = True
                        break
                
                # Wenn kein passender Nachfolger gefunden wurde, endet der Bogen hier
                if not found: break
                
            merged.append(curr)
        return merged

    # ------------------------------------------------------------------
    # AUDIO-EXPORT
    # ------------------------------------------------------------------
    # Erzeugt das fertige Audio-Array für eine Stimme.
    # Das ermöglicht Multitracking (Mischen mehrerer Stimmen).
    # ------------------------------------------------------------------
    def get_audio_data(self, score):
        print(f"Synthetisiere Stimme (Transpose: {self.transpose})...")
        events = self.parse(score)
        if not events: return np.array([], dtype=np.float32)

        # 1. Puffergröße berechnen
        last_end = max(e['start'] + e['dur'] for e in events)
        # Wir geben etwas Puffer für den Hall (Release) dazu
        total_dur = last_end + self.release_time + 0.5
        num_samples = int(total_dur * self.sample_rate)
        
        # Leerer Buffer (Float32 für präzises Mischen)
        buffer = np.zeros(num_samples, dtype=np.float32)
        
        # 2. Events in den Buffer schreiben
        for e in events:
            # Wellenform für dieses spezifische Event generieren
            wave_data = self._generate_wave(e['freq'], e['dur'])
            
            if wave_data is not None:
                # Startposition im Array berechnen
                start_s = int(e['start'] * self.sample_rate)
                end_s = start_s + len(wave_data)
                
                # Falls das Array zu kurz ist (sollte durch Puffer
                # nicht passieren), erweitern
                if end_s > len(buffer):
                    buffer = np.pad(buffer, (0, end_s - len(buffer)))
                
                # Addieren (Mixing im Zeitbereich)
                buffer[start_s:end_s] += wave_data
        
        return buffer

    def set_instrument(self, name):
        if name in self.PRESETS:
            self.PRESETS[name](self) # Wendet die Logik auf self an

    # ==================================================================
    # PRESETS (Klangfarben)
    # ==================================================================
    # Diese Methoden ändern die 'overtones' und Hüllkurven-Parameter, um
    # verschiedene Instrumente zu simulieren.
    # ==================================================================

    def pure_sine(self):
        # Nur der Grundton -> reiner Sinus
        self.overtones = [1.0]
        self.attack_time = 0.05
        self.release_time = 0.1

    def flute(self):
        # Flöte: Wenige Obertöne, weicher Klang.
        self.overtones = [1.0, 0.5, 0.2]
        self.attack_time = 0.1  # Luftstrom braucht Zeit
        self.release_time = 0.1

    def organ(self):
        # Orgel: Viele Obertöne, kräftig, statisch.
        self.overtones = [1.0, 0.5, 0.5, 0.3, 0.2, 0.1, 0.05, 0.05]
        self.attack_time = 0.08
        self.release_time = 0.2

    def clarinet(self):
        # Klarinette: Besonderheit sind dominierende UNGERADE Obertöne (1, 3, 5).
        # Das entsteht durch das zylindrische Rohr, das an einer Seite geschlossen ist.
        # Overtones-Index 0=1.Harm, 1=2.Harm(fehlt), 2=3.Harm, etc.
        self.overtones = [1.0, 0.0, 0.5, 0.0, 0.3, 0.0, 0.1]
        self.attack_time = 0.08
        self.release_time = 0.1

    def violin(self):
        # Violine: Sägezahn-ähnlich (Obertöne fallen mit 1/n ab).
        # Sehr obertonreich und "scharf".
        self.overtones = [1.0 / n for n in range(1, 16)]
        self.attack_time = 0.2  # Bogenstrich ist weich
        self.release_time = 0.3

    def piano(self):
        # Klavier: Perkussiv (Attack fast 0), komplexer Obertonabfall.
        # Besonderheit: Der 7. Oberton wird oft durch die Anschlagposition eliminiert.
        ot = []
        for n in range(1, 12):
            if n == 7:
                ot.append(0.0)
            else:
                ot.append(1.0 / (n ** 1.3)) # Exponentieller Abfall
        self.overtones = ot
        self.attack_time = 0.01 # Hammer schlägt sofort
        self.release_time = 0.4

    def harpsichord(self):
        # Cembalo: Zupfinstrument, sehr hell und kurz.
        self.overtones = [0.6 / (n**0.8) for n in range(1, 20)]
        self.attack_time = 0.02
        self.release_time = 0.1

    def chiptune(self):
        # 8-Bit Stil: Rechteckwelle.
        # Rechteck hat nur ungerade Obertöne, die mit 1/n abfallen.
        ot = []
        for n in range(1, 20):
            if n % 2 == 0:
                ot.append(0.0)
            else:
                ot.append(1.0 / n)
        self.overtones = ot
        self.attack_time = 0.005 # Digitaler Start
        self.release_time = 0.05

    def bell(self):
        # Glocke: Unharmonisches Spektrum (Frequenzen sind keine sauberen Vielfachen).
        # Da wir hier additive Synthese mit festen Harmonischen nutzen, simulieren wir
        # das durch "Lücken" und Betonung hoher, dissonanter Obertöne.
        self.overtones = [1.0, 0, 0, 0.5, 0, 0.8, 0, 0, 0.3]
        self.attack_time = 0.005
        self.release_time = 1.5


# ======================================================================
# EXTERNE FUNKTION: Mischen und Speichern
# ======================================================================
# Diese Funktion nimmt mehrere Audiospuren (numpy arrays), mischt sie
# zusammen und speichert das Ergebnis als WAV-Datei.
# ======================================================================
def save_mixed_wav(audio_tracks, output_target="output.wav", sample_rate=44100, gain=0.8):
    if not audio_tracks:
        print("Keine Audio-Tracks zum Speichern.")
        return

    # 1. Länge der längsten Spur finden
    max_len = max(len(track) for track in audio_tracks)
    
    # 2. Leeren Master-Buffer erstellen
    mixed = np.zeros(max_len, dtype=np.float32)
    
    # 3. Spuren addieren
    print("Mische Spuren...")
    for track in audio_tracks:
        length = len(track)
        # Spur auf den Master addieren. Wenn die Spur kürzer ist,
        # füllt Python nur den Bereich bis `length`.
        mixed[:length] += track

    # 4. Normalisieren und Gain
    # Clipping verhindern: Wenn Werte > 1.0 oder < -1.0 sind, verzerrt das Audio digital.
    # Wir skalieren alles so herunter, dass der lauteste Punkt genau 1.0 (bzw. gain) ist.
    max_val = np.max(np.abs(mixed))
    if max_val > 0:
        mixed = (mixed / max_val) * gain
        
    # 5. Konvertierung zu 16-bit PCM Integer
    # Audio-CDs nutzen 16 bit signed integer (-32768 bis 32767).
    # Float Bereich [-1.0, 1.0] wird auf diesen Bereich gemappt.
    audio_int16 = (np.clip(mixed, -1.0, 1.0) * 32767).astype(np.int16)
    
    # 6. Datei schreiben
    # wave.open akzeptiert Strings oder file-like objects wie BytesIO
    with wave.open(output_target, 'wb') as f:
        f.setnchannels(1) # Mono
        f.setsampwidth(2) # 2 Bytes = 16 bit
        f.setframerate(sample_rate)
        f.writeframes(audio_int16.tobytes())
    if isinstance(output_target, str):
        print(f"Datei '{output_target}' erfolgreich gespeichert.")
    else:
        print("Audio in Speicher-Puffer geschrieben.")

# ======================================================================
# ERGONOMISCHE BENUTZER-SCHNITTSTELLE
# ======================================================================

class Score:
    # Farbschema für verschiedene Spuren (die ersten vier barrierefrei,
    # IBM Design Library color-blind safe, ein wenig aufgehellt)
    COLORS = [
        (140, 183, 255), # Blau
        (255, 196,   0), # Gelb
        (240,  38, 127), # Magenta
        (120,  94, 240), # Violett
        (  0, 200, 100), # Grün
        (  0, 210, 210), # Cyan
        (160, 160, 160)  # Grau
    ]

    def __init__(self, bpm=100, time="4/4", base_a4=None, validate=True):
        self.bpm = bpm
        self.time = time
        self.base_a4 = base_a4
        self.validate = validate
        self.tracks = []
        self.viz_data = []

    def add(self, instrument, score_string, transpose=0):
        synth = Synth(bpm=self.bpm, time=self.time,
            instrument=instrument, transpose=transpose,
            validate=self.validate)
        if self.base_a4 is not None:
            synth.base_a4 = float(self.base_a4)

        # 1. Audio für Export generieren
        audio = synth.get_audio_data(score_string)
        self.tracks.append(audio)

        # 2. Events für Visualisierung parsen und speichern
        # Wir weisen eine Farbe basierend auf der Spur-Nummer zu
        color = self.COLORS[len(self.viz_data) % len(self.COLORS)]
        events = synth.parse(score_string)
        self.viz_data.append((events, color, synth.base_a4))

        return self

    def save(self, filename):
        save_mixed_wav(self.tracks, filename)


    # Generiert das Audio, speichert es temporär und startet die
    # Visualisierung
    def play(self):
        # Falls noch keine Spuren da sind, abbrechen
        if not self.tracks:
            print("Keine Spuren vorhanden.")
            return

        # In-Memory-Buffer statt temporärer Datei, damit die SSD nicht
        # mit verschleißenden Schreibzugriffen belastet wird
        wav_buffer = io.BytesIO()
        save_mixed_wav(self.tracks, output_target=wav_buffer)

        # Den Cursor des Buffers an den Anfang zurücksetzen, sonst liest
        # Pygame ab dem Ende der Datei (wo keine Daten mehr sind)
        wav_buffer.seek(0)

        # Visualizer starten
        viz = Visualizer(width=1200, height=800)
        viz.run(self.viz_data, wav_buffer)

# ======================================================================
# VISUALISIERUNG
# ======================================================================
class Visualizer:
    def __init__(self, width=1200, height=800):
        # Pygame spät laden, damit das Programm auch ohne
        # Installation läuft
        try:
            import pygame
            self.pg = pygame
        except ImportError:
            print("Fehler: 'pygame' ist nicht installiert. Visualisierung deaktiviert.")
            self.pg = None
            return

        self.pg.init()
        self.pg.mixer.init(frequency=44100, size=-16, channels=1)
        
        self.width = width
        self.height = height
        self.screen = self.pg.display.set_mode((width, height))
        self.pg.display.set_caption("Lilysynth")
        
        self.clock = self.pg.time.Clock()
        self.is_running = True
        
        # Konfiguration Ansicht
        self.pixels_per_second = 150 # Geschwindigkeit der fallenden Noten
        self.keyboard_height = 100
        self.note_area_height = self.height - self.keyboard_height
        
        # MIDI-Bereich für die Tastatur (Automatisch anpassen oder fixieren)
        self.min_midi = 36  # C2
        self.max_midi = 96  # C7
        self.white_keys = [] 
        self._init_keyboard_layout()

    def _init_keyboard_layout(self):
        if not self.pg: return
        # Berechne Positionen der Tasten
        total_keys = self.max_midi - self.min_midi + 1
        # Wir zählen nur die weißen Tasten für die Breite
        white_key_count = 0
        for m in range(self.min_midi, self.max_midi + 1):
            if not self._is_black_key(m):
                white_key_count += 1
        
        self.wk_width = self.width / white_key_count
        self.bk_width = self.wk_width * 0.7
        
    def _is_black_key(self, midi_note):
        # 0=C, 1=C#, 2=D, 3=D#, 4=E, 5=F, 6=F#, 7=G, 8=G#, 9=A, 10=A#, 11=B
        return (midi_note % 12) in [1, 3, 6, 8, 10]

    def _freq_to_midi(self, freq, ref_freq=440.0):
        if freq == 0: return 0
        return int(round(69 + 12 * math.log2(freq / float(ref_freq))))

    def _get_x_pos(self, midi_note):
        # X-Position basierend auf weißen Tasten berechnen
        current_wk_index = 0
        for m in range(self.min_midi, midi_note):
            if not self._is_black_key(m):
                current_wk_index += 1
        
        x = current_wk_index * self.wk_width
        
        # Wenn es eine schwarze Taste ist, leicht versetzt
        if self._is_black_key(midi_note):
            return x - (self.bk_width / 2) # Zentriert auf der Linie zwischen weißen Tasten
        return x

    def run(self, tracks_data, wav_file):
        if not self.pg: return

        # tracks_data ist eine Liste von Tupeln: (events_list, color)
        
        # 1. Audio laden
        self.pg.mixer.music.load(wav_file)
        self.pg.mixer.music.play()
        
        start_ticks = self.pg.time.get_ticks()
        
        while self.is_running:
            # Events abarbeiten (Quit, etc.)
            for event in self.pg.event.get():
                if event.type == self.pg.QUIT:
                    self.is_running = False

            # Zeit berechnen
            if self.pg.mixer.music.get_busy():
                # Music pos ist in ms
                current_time = self.pg.mixer.music.get_pos() / 1000.0
            else:
                # Fallback, wenn Audio zu Ende ist oder noch lädt
                current_time = (self.pg.time.get_ticks() - start_ticks) / 1000.0

            # --- ZEICHNEN ---
            self.screen.fill((20, 20, 25)) # Dunkler Hintergrund
            
            # 1. Fallende Noten
            # Wir iterieren durch alle Spuren
            active_midi_notes = {} # Welche Tasten sind gerade gedrückt?
            
            for events, color, ref_freq in tracks_data:
                for note in events:
                    if note['freq'] == 0: continue
                    
                    # Position berechnen
                    # y = Ziel_Linie - (Startzeit - Jetzt) * Speed
                    # Ziel_Linie ist oben an der Tastatur
                    
                    time_diff = note['start'] - current_time
                    note_y = self.note_area_height - (time_diff * self.pixels_per_second)
                    
                    # Höhe des Balkens entspricht der Dauer
                    note_h = note['dur'] * self.pixels_per_second
                    
                    # Tatsächliche Zeichenposition (Y-Achse wächst nach unten in Pygame)
                    # Der Balken 'kommt' von oben. Das untere Ende des Balkens ist bei note_y.
                    # Das obere Ende ist bei note_y - note_h.
                    
                    draw_y = note_y - note_h
                    
                    # Nur zeichnen, wenn im sichtbaren Bereich
                    if draw_y < self.height and (draw_y + note_h) > 0:
                        midi = self._freq_to_midi(note['freq'], ref_freq)
                        if midi < self.min_midi or midi > self.max_midi: continue
                        
                        x = self._get_x_pos(midi)
                        w = self.bk_width if self._is_black_key(midi) else self.wk_width
                        
                        # Farbe aufhellen, wenn Note gerade aktiv ist (trifft auf Tastatur)
                        # Note ist aktiv, wenn current_time zwischen start und start+dur liegt
                        is_active = note['start'] <= current_time <= (note['start'] + note['dur'])
                        
                        draw_color = color
                        if is_active:
                            active_midi_notes[midi] = color
                            draw_color = tuple(min(255, c + 50) for c in color)
                        
                        # Zeichnen (Rechteck mit abgerundeten Ecken sieht moderner aus)
                        self.pg.draw.rect(self.screen, draw_color, (x + 1, draw_y, w - 2, note_h), border_radius=6)

            # 2. Klaviertastatur zeichnen
            self._draw_keyboard(active_midi_notes)

            self.pg.display.flip()
            self.clock.tick(60) # 60 FPS

        self.pg.quit()

    def _draw_keyboard(self, active_notes):
        # Weiße Tasten zuerst
        wk_index = 0
        for m in range(self.min_midi, self.max_midi + 1):
            if not self._is_black_key(m):
                x = wk_index * self.wk_width
                
                # Standardfarbe (nicht gedrückt)
                fill_color = (200, 200, 200) 
                
                # Wenn gedrückt: Nimm die Farbe der Stimme (aus dem Dictionary)
                if m in active_notes:
                    # Wir hellen die Farbe der Stimme für die Taste etwas auf, damit es leuchtet
                    base_c = active_notes[m]
                    fill_color = tuple(min(255, c + 100) for c in base_c)
                
                self.pg.draw.rect(self.screen, fill_color,
                    (x, self.note_area_height, self.wk_width - 1, self.keyboard_height),
                    border_radius=2)
                
                wk_index += 1
        
        # Schwarze Tasten darüber
        for m in range(self.min_midi, self.max_midi + 1):
            if self._is_black_key(m):
                x = self._get_x_pos(m)
                
                # Standardfarbe Schwarz
                fill_color = (40, 40, 40) 
                
                if m in active_notes:
                    # Auch hier: Farbe der Stimme nutzen
                    base_c = active_notes[m]
                    fill_color = tuple(min(255, c + 50) for c in base_c)
                
                self.pg.draw.rect(self.screen, fill_color,
                    (x, self.note_area_height, self.bk_width, self.keyboard_height * 0.6),
                    border_radius=2)

# ======================================================================
# BEISPIEL: "Auld Lang Syne" in G-Dur im 4/4-Takt bei 100 BPM
# ======================================================================

lead_voice = """
d4 | g4. g8 g4 b4 | a4. g8 a4 b4 | g4. g8 b4 d'4 | e'2 r4
e'4 | d'4. b8 b4 g4 | a4. g8 a4 b4 | g4. e8 e4 d4 | g2 r4
e'4 | d'4. b8 b4 g4 | a4. g8 a4 e'4 | d'4. b8 b4 d'4 | e'2 r4
g'4 | d'4. b8 b4 g4 | a4. g8 a4 b8. a16 | g4. e8 e4 d4 | g2 r2 | 
"""

acc_voice = """
r4 | <g b d'>2 <b d'>2 | <e g c'>2 <d fis a>2 |
<b d'>2 <g b d'>2 | <e g c'>1

| <b d'>2 <e g b>2 | <e a c'>2 <d fis a>2 |
<e g b>2 <e g c'>4 <d fis a>4 | <g b d'>2 <e c'>

| <b d'>2 <e g b>2 | <e a c'>2 <d fis a>2 |
<b d'>2 <g b d'>2 | <e g c'>1

| <b d'>2 <e g b>2 | <e a c'>2 <d fis a>2 |
<e g b>2 <e g c'>4 <d d'>4 | <g b d'>2 r2 |
"""

if __name__ == "__main__":
    s = Score(bpm = 100)
    s.add("violin", lead_voice, transpose = 12)
    s.add("piano", acc_voice)
    s.play()
    # s.save("Auld Lang Syne.wav")

