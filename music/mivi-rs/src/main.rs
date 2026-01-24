// =====================================================================
// Mivi -- Ein MIDI-Synthesizer und -Visualizer (Portierung auf Rust)
// =====================================================================
// Version 2026-01-24

use sdl2::audio::{AudioCallback, AudioSpecDesired, AudioCVT};
use sdl2::event::Event;
use sdl2::keyboard::Keycode;
use sdl2::pixels::Color;
use sdl2::rect::{Point, Rect};
use sdl2::render::Canvas;
use sdl2::video::{Window, FullscreenType};

use std::cmp::Ordering;
use std::env;
use std::f64::consts::PI;
use std::fs::File;
use std::io::{Read, Seek, SeekFrom};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

// =====================================================================
// KONFIGURATION UND KONSTANTEN
// =====================================================================
const SAMPLE_RATE: i32 = 44100;
const AUDIO_CHANNELS: u8 = 1;
const WINDOW_WIDTH: u32 = 1200;
const WINDOW_HEIGHT: u32 = 800;
const KEYBOARD_HEIGHT: i32 = 100;
const PIXELS_PER_SECOND: f64 = 150.0;

const MIN_MIDI: i32 = 21;  // A0
const MAX_MIDI: i32 = 108; // C8

// =====================================================================
// DATENSTRUKTUREN
// =====================================================================

#[derive(Debug, Clone, Copy, PartialEq)]
enum EventType {
    NoteOn,
    NoteOff,
    SetTempo,
}

#[derive(Debug, Clone)]
struct MidiEvent {
    abs_tick: u32,
    event_type: EventType,
    channel: u8,
    note: u8,
    velocity: u8,
    tempo_micros: u32,
}

#[derive(Debug, Clone)]
struct Note {
    start_time: f64,
    duration: f64,
    midi_key: i32,
    _velocity: i32, // Wird nach der Synthese nicht mehr zwingend gebraucht
    _channel: i32,
    color: Color,
}

// =====================================================================
// AUDIO-CALLBACK
// =====================================================================

struct SoundProvider {
    samples: Vec<i16>,
    cursor: usize,
}

impl AudioCallback for SoundProvider {
    type Channel = i16;

    fn callback(&mut self, out: &mut [i16]) {
        for dst in out.iter_mut() {
            if self.cursor < self.samples.len() {
                *dst = self.samples[self.cursor];
                self.cursor += 1;
            } else {
                *dst = 0;
            }
        }
    }
}

// =====================================================================
// HELPER: FARBEN UND KEYBOARD
// =====================================================================

fn get_channel_color(channel: i32) -> Color {
    if channel == 9 {
        return Color::RGB(150, 150, 150);
    }
    match channel % 9 {
        0 => Color::RGB(0, 220, 220),
        1 => Color::RGB(255, 0, 200),
        2 => Color::RGB(255, 220, 0),
        3 => Color::RGB(0, 200, 100),
        4 => Color::RGB(100, 100, 255),
        5 => Color::RGB(255, 100, 100),
        6 => Color::RGB(200, 0, 255),
        7 => Color::RGB(0, 255, 100),
        8 => Color::RGB(255, 128, 0),
        _ => Color::RGB(255, 255, 255),
    }
}

fn is_black_key(midi: i32) -> bool {
    matches!(midi % 12, 1 | 3 | 6 | 8 | 10)
}

fn get_key_geometry(midi_note: i32, total_width: f32) -> (f32, f32, bool) {
    let mut white_keys_total = 0;
    for i in MIN_MIDI..=MAX_MIDI {
        if !is_black_key(i) {
            white_keys_total += 1;
        }
    }

    let wk_width = total_width / white_keys_total as f32;
    let bk_width = wk_width * 0.65;

    let mut current_wk_index = 0;
    for i in MIN_MIDI..midi_note {
        if !is_black_key(i) {
            current_wk_index += 1;
        }
    }

    let pos = current_wk_index as f32 * wk_width;
    let is_black = is_black_key(midi_note);

    if is_black {
        (pos - (bk_width / 2.0), bk_width, true)
    } else {
        (pos, wk_width, false)
    }
}

// =====================================================================
// MIDI-PARSER
// =====================================================================

// Hilfsfunktionen zum Lesen von Big-Endian Werten
fn read_be16(f: &mut File) -> std::io::Result<u16> {
    let mut buf = [0u8; 2];
    f.read_exact(&mut buf)?;
    Ok(u16::from_be_bytes(buf))
}

fn read_be32(f: &mut File) -> std::io::Result<u32> {
    let mut buf = [0u8; 4];
    f.read_exact(&mut buf)?;
    Ok(u32::from_be_bytes(buf))
}

fn read_varlen(f: &mut File) -> std::io::Result<u32> {
    let mut value: u32 = 0;
    let mut byte = [0u8; 1];
    loop {
        f.read_exact(&mut byte)?;
        value = (value << 7) | (byte[0] & 0x7F) as u32;
        if byte[0] & 0x80 == 0 {
            break;
        }
    }
    Ok(value)
}

fn parse_midi(filename: &str) -> Result<(Vec<MidiEvent>, u16), Box<dyn std::error::Error>> {
    let mut f = File::open(filename)?;

    // Header Check
    let mut chunk_id = [0u8; 4];
    f.read_exact(&mut chunk_id)?;
    if &chunk_id != b"MThd" {
        return Err("Kein gültiges MIDI".into());
    }

    read_be32(&mut f)?; // Header length (skip)
    read_be16(&mut f)?; // Format (skip)
    let num_tracks = read_be16(&mut f)?;
    let division = read_be16(&mut f)?;

    if division & 0x8000 != 0 {
        return Err("SMPTE nicht unterstützt".into());
    }

    let mut all_events = Vec::new();

    for _ in 0..num_tracks {
        f.read_exact(&mut chunk_id)?;
        while &chunk_id != b"MTrk" {
            let skip = read_be32(&mut f)?;
            f.seek(SeekFrom::Current(skip as i64))?;
            f.read_exact(&mut chunk_id)?;
        }

        let track_len = read_be32(&mut f)?;
        let start_pos = f.stream_position()?;
        let end_pos = start_pos + track_len as u64;

        let mut abs_tick = 0;
        let mut running_status = 0u8;

        while f.stream_position()? < end_pos {
            let delta = read_varlen(&mut f)?;
            abs_tick += delta;

            let mut byte = [0u8; 1];
            f.read_exact(&mut byte)?;
            let mut status = byte[0];

            if status < 0x80 {
                status = running_status;
                f.seek(SeekFrom::Current(-1))?;
            } else {
                running_status = status;
            }

            if status == 0xFF {
                // Meta Event
                f.read_exact(&mut byte)?; // Type
                let meta_type = byte[0];
                let len = read_varlen(&mut f)?;

                if meta_type == 0x51 && len == 3 {
                    let mut tb = [0u8; 3];
                    f.read_exact(&mut tb)?;
                    let micros = u32::from_be_bytes([0, tb[0], tb[1], tb[2]]);
                    all_events.push(MidiEvent {
                        abs_tick,
                        event_type: EventType::SetTempo,
                        channel: 0,
                        note: 0,
                        velocity: 0,
                        tempo_micros: micros,
                    });
                } else {
                    f.seek(SeekFrom::Current(len as i64))?;
                }
            } else if status == 0xF0 || status == 0xF7 {
                // SysEx
                let len = read_varlen(&mut f)?;
                f.seek(SeekFrom::Current(len as i64))?;
            } else {
                // Channel Event
                let cmd = status & 0xF0;
                let ch = status & 0x0F;

                if cmd == 0x90 || cmd == 0x80 {
                    let mut params = [0u8; 2];
                    f.read_exact(&mut params)?;
                    let note = params[0];
                    let vel = params[1];

                    let is_note_on = cmd == 0x90 && vel > 0;
                    all_events.push(MidiEvent {
                        abs_tick,
                        event_type: if is_note_on { EventType::NoteOn } else { EventType::NoteOff },
                        channel: ch,
                        note,
                        velocity: vel,
                        tempo_micros: 0,
                    });
                } else if cmd == 0xC0 || cmd == 0xD0 {
                    f.seek(SeekFrom::Current(1))?;
                } else {
                    f.seek(SeekFrom::Current(2))?;
                }
            }
        }
    }

    // Sortieren
    all_events.sort_by_key(|e| e.abs_tick);
    Ok((all_events, division))
}

fn convert_to_notes(events: &[MidiEvent], division: u16) -> (Vec<Note>, f64) {
    let mut notes = Vec::new();
    let mut cur_time = 0.0;
    let mut cur_tick = 0;
    let mut micros_per_beat = 500_000.0;

    // [Channel][Note] -> (Startzeit, Velocity)
    let mut active_notes: [[Option<(f64, u8)>; 128]; 16] = [[None; 128]; 16];

    for e in events {
        if e.abs_tick > cur_tick {
            let delta_ticks = e.abs_tick - cur_tick;
            cur_time += (delta_ticks as f64) * (micros_per_beat / 1_000_000.0) / (division as f64);
            cur_tick = e.abs_tick;
        }

        match e.event_type {
            EventType::SetTempo => micros_per_beat = e.tempo_micros as f64,
            EventType::NoteOn => {
                let ch = e.channel as usize;
                let n = e.note as usize;

                // Falls Note schon an, vorherige beenden (Retrigger)
                if let Some((start, vel)) = active_notes[ch][n] {
                    let dur = cur_time - start;
                    if dur > 0.0 {
                        notes.push(Note {
                            start_time: start,
                            duration: dur,
                            midi_key: e.note as i32,
                            _velocity: vel as i32,
                            _channel: e.channel as i32,
                            color: get_channel_color(e.channel as i32),
                        });
                    }
                }
                active_notes[ch][n] = Some((cur_time, e.velocity));
            },
            EventType::NoteOff => {
                let ch = e.channel as usize;
                let n = e.note as usize;
                if let Some((start, vel)) = active_notes[ch][n] {
                    let dur = cur_time - start;
                    if dur > 0.0 {
                        notes.push(Note {
                            start_time: start,
                            duration: dur,
                            midi_key: e.note as i32,
                            _velocity: vel as i32,
                            _channel: e.channel as i32,
                            color: get_channel_color(e.channel as i32),
                        });
                    }
                    active_notes[ch][n] = None;
                }
            },
        }
    }

    // Sortieren nach Startzeit (für Renderer)
    notes.sort_by(|a, b| a.start_time.partial_cmp(&b.start_time).unwrap_or(Ordering::Equal));

    (notes, cur_time + 1.0)
}

// =====================================================================
// AUDIO-SYNTHESE (Intern)
// =====================================================================

fn synthesize_to_ram(notes: &[Note], duration: f64) -> Vec<i16> {
    let total_samples = (duration * SAMPLE_RATE as f64) as usize;
    let mut mix_buf = vec![0.0f32; total_samples];

    println!("Synthetisiere {} Noten ({:.1} s)...", notes.len(), duration);

    let overtones = [1.0, 0.5, 0.3, 0.1];
    let release = 0.1;

    for n in notes {
        let is_drum = n._channel == 9;
        let freq = if is_drum { 100.0 } else {
            440.0 * 2.0f64.powf((n.midi_key as f64 - 69.0) / 12.0)
        };
        let dur = if is_drum { 0.05 } else { n.duration };
        let amp = (n._velocity as f64 / 127.0) * 0.3;

        let start_s = (n.start_time * SAMPLE_RATE as f64) as usize;
        let len_s = ((dur + release) * SAMPLE_RATE as f64) as usize;

        for t in 0..len_s {
            if start_s + t >= total_samples { break; }

            let time = t as f64 / SAMPLE_RATE as f64;
            let mut val = 0.0;

            if is_drum {
                val = (2.0 * PI * freq * time).sin();
            } else {
                for (i, ov) in overtones.iter().enumerate() {
                    let h = freq * (i as f64 + 1.0);
                    if h < SAMPLE_RATE as f64 / 2.0 {
                        val += ov * (2.0 * PI * h * time).sin();
                    }
                }
                val /= 1.9;
            }

            // Envelope
            let mut env = 1.0;
            if time < 0.05 {
                env = time / 0.05;
            } else if time > dur {
                env = 1.0 - ((time - dur) / release);
            }
            if env < 0.0 { env = 0.0; }

            mix_buf[start_s + t] += (val * amp * env) as f32;
        }
    }

    // Normalisieren und Konvertieren
    let max_val = mix_buf.iter().fold(0.0f32, |m, &x| m.max(x.abs()));
    let norm = if max_val > 0.0 { 32000.0 / max_val } else { 1.0 };
    let norm = norm.min(32000.0);

    mix_buf.into_iter().map(|v| (v * norm) as i16).collect()
}

// =====================================================================
// AUDIO-GENERIERUNG (Timidity-Pipe)
// =====================================================================

fn generate_audio_with_timidity(midifile: &str) -> Result<Vec<i16>, Box<dyn std::error::Error>> {
    println!("Starte Timidity via Pipe (Raw PCM)...");

    let output = Command::new("timidity")
        .args(&[
            midifile, "-Or", "-s", "44100", "-A160", "--preserve-silence", "-o", "-"
        ])
        .stdout(Stdio::piped())
        .output()?;

    if !output.status.success() {
        return Err("Timidity fehlgeschlagen (ist es installiert?)".into());
    }

    let raw_data = output.stdout;
    if raw_data.is_empty() {
        return Err("Keine Daten von Timidity empfangen".into());
    }

    // Timidity Raw ist Stereo S16SYS, wir wollen Mono S16SYS
    // Wir nutzen SDL AudioCVT für die Konvertierung
    let target_format = if cfg!(target_endian = "little") {
        sdl2::audio::AudioFormat::S16LSB
    } else {
        sdl2::audio::AudioFormat::S16MSB
    };

    let src_format = target_format;
    let dst_format = target_format;
    // Unser Zielformat (definiert im struct SoundProvider)
    // (i16 im RAM ist auch native endian)

    let cvt = AudioCVT::new(
        src_format, 2, 44100,
        dst_format, AUDIO_CHANNELS, SAMPLE_RATE
    ).map_err(|e| format!("CVT Build Error: {}", e))?;

    let output_samples = cvt.convert(raw_data);

    // Vec<u8> zu Vec<i16>
    // Sicherheitsannahme: System ist Little Endian, oder S16SYS passt.
    // Ein cast über slices ist in Rust unsafe oder benötigt byteorder.
    // Wir machen es sicher aber langsamer per chunks:
    let i16_samples: Vec<i16> = output_samples
        .chunks_exact(2)
        .map(|c| i16::from_ne_bytes([c[0], c[1]]))
        .collect();

    println!("Audio von Timidity geladen: {} Samples", i16_samples.len());
    Ok(i16_samples)
}

// =====================================================================
// RENDER HELPERS
// =====================================================================

const CORNER_TL: u8 = 1;
const CORNER_TR: u8 = 2;
const CORNER_BL: u8 = 4;
const CORNER_BR: u8 = 8;
const CORNER_ALL: u8 = 15;

fn fill_quarter_circle(
    canvas: &mut Canvas<Window>, cx: i32, cy: i32,
    r: i32, quadrant: u8
) -> Result<(), String> {
    for dy in 0..=r {
        let dx = ((r * r - dy * dy) as f64).sqrt() as i32;
        match quadrant {
            0 => canvas.draw_line(Point::new(cx - dx, cy - dy), Point::new(cx, cy - dy))?, // TL
            1 => canvas.draw_line(Point::new(cx, cy - dy), Point::new(cx + dx, cy - dy))?, // TR
            2 => canvas.draw_line(Point::new(cx - dx, cy + dy), Point::new(cx, cy + dy))?, // BL
            3 => canvas.draw_line(Point::new(cx, cy + dy), Point::new(cx + dx, cy + dy))?, // BR
            _ => {},
        }
    }
    Ok(())
}

fn render_fill_rounded_rect(
    canvas: &mut Canvas<Window>, x: i32, y: i32,
    mut w: i32, mut h: i32, mut r: i32, corners: u8
) -> Result<(), String> {
    if r * 2 > w { r = w / 2; }
    if r * 2 > h { r = h / 2; }

    // Sicherheit gegen negative Größen
    if w < 0 { w = 0; }
    if h < 0 { h = 0; }

    // 1. Vertikaler Mittelstreifen
    canvas.fill_rect(Rect::new(x + r, y, (w - 2 * r) as u32, h as u32))?;
    // 2. Seitenstreifen
    canvas.fill_rect(Rect::new(x, y + r, r as u32, (h - 2 * r) as u32))?;
    canvas.fill_rect(Rect::new(x + w - r, y + r, r as u32, (h - 2 * r) as u32))?;

    // 3. Ecken
    // TL
    if corners & CORNER_TL != 0 { fill_quarter_circle(canvas, x + r, y + r, r, 0)?; }
    else { canvas.fill_rect(Rect::new(x, y, r as u32, r as u32))?; }

    // TR
    if corners & CORNER_TR != 0 { fill_quarter_circle(canvas, x + w - r - 1, y + r, r, 1)?; }
    else { canvas.fill_rect(Rect::new(x + w - r, y, r as u32, r as u32))?; }

    // BL
    if corners & CORNER_BL != 0 { fill_quarter_circle(canvas, x + r, y + h - r - 1, r, 2)?; }
    else { canvas.fill_rect(Rect::new(x, y + h - r, r as u32, r as u32))?; }

    // BR
    if corners & CORNER_BR != 0 { fill_quarter_circle(canvas, x + w - r - 1, y + h - r - 1, r, 3)?; }
    else { canvas.fill_rect(Rect::new(x + w - r, y + h - r, r as u32, r as u32))?; }

    Ok(())
}


// =====================================================================
// MAIN
// =====================================================================

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = env::args().collect();
    let mut midifile = "";
    let mut use_timidity = false;
    let mut fullscreen = false;

    if args.len() < 2 {
        println!("Verwendung: {} <datei.mid> [-tm]", args[0]);
        return Ok(());
    }

    for arg in &args[1..] {
        if arg == "-tm" {
            use_timidity = true;
        } else {
            midifile = arg;
        }
    }

    // 1. MIDI Parsen
    let (events, division) = parse_midi(midifile)?;
    let (notes, duration) = convert_to_notes(&events, division);

    if notes.is_empty() {
        return Err("Keine Noten gefunden.".into());
    }

    // 2. Audio Generieren
    let pcm_buffer = if use_timidity {
        generate_audio_with_timidity(midifile)?
    } else {
        synthesize_to_ram(&notes, duration)
    };

    let audio_duration = pcm_buffer.len() as f64 / SAMPLE_RATE as f64;

    // 3. SDL Init
    let sdl_context = sdl2::init()?;
    let video_subsystem = sdl_context.video()?;
    let audio_subsystem = sdl_context.audio()?;

    let window = video_subsystem.window("Mivi", WINDOW_WIDTH, WINDOW_HEIGHT)
        .position_centered()
        .resizable()
        .build()?;

    let mut canvas = window.into_canvas()
        .accelerated()
        .present_vsync()
        .build()?;

    // Audio Setup
    let desired_spec = AudioSpecDesired {
        freq: Some(SAMPLE_RATE),
        channels: Some(AUDIO_CHANNELS),
        samples: Some(2048),
    };

    let mut device = audio_subsystem.open_playback(None, &desired_spec, |_spec| {
        SoundProvider {
            samples: pcm_buffer,
            cursor: 0,
        }
    })?;

    device.resume();

    // 4. Main Loop
    let mut event_pump = sdl_context.event_pump()?;

    // ZEITMESSUNG INITIALISIERUNG
    let mut start_instant = Instant::now();
    let mut paused = false;
    let mut pause_start_time = Instant::now(); // Merkt sich, wann Pause gedrückt wurde

    // Damit die Audio-Länge bestimmt wann Ende ist
    let loop_limit = if audio_duration > duration { audio_duration } else { duration };
    let end_limit = if use_timidity { loop_limit + 1.5 } else { duration + 1.0 };

    let mut active_keys = [false; 128];
    let mut active_colors = [Color::RGB(0,0,0); 128];

    'running: loop {
        // INPUT HANDLING
        for event in event_pump.poll_iter() {
            match event {
                Event::Quit {..} |
                Event::KeyDown { keycode: Some(Keycode::Escape), .. } => {
                    break 'running
                },
                Event::KeyDown { keycode: Some(k), .. } => {
                    match k {
                        // PAUSE / PLAY
                        Keycode::Space | Keycode::K => {
                            paused = !paused;
                            if paused {
                                pause_start_time = Instant::now();
                                device.pause();
                            } else {
                                // Die Zeit, die wir pausiert waren, auf den Start-Zeitpunkt addieren,
                                // damit der Song nicht visuell nach vorne springt.
                                let paused_duration = Instant::now().duration_since(pause_start_time);
                                start_instant += paused_duration;
                                device.resume();
                            }
                        },
                        // SPULEN
                        Keycode::Left | Keycode::J | Keycode::Right | Keycode::L |
                        Keycode::Comma | Keycode::Period => {
                            let jump = Duration::from_secs(
                                if k == Keycode::Comma || k == Keycode::Period {1}
                                else if k == Keycode::Left || k == Keycode::Right {4}
                                else {10});
                            let is_forward = k == Keycode::Right || k == Keycode::L || k == Keycode::Period;

                            if !is_forward {
                                // Zurückspulen: Startzeit in die Zukunft schieben -> Differenz wird kleiner
                                start_instant += jump;
                            } else {
                                // Vorspulen: Startzeit in die Vergangenheit schieben -> Differenz wird größer
                                // checked_sub verhindert Panic, falls wir vor den Programmstart kämen
                                if let Some(new_start) = start_instant.checked_sub(jump) {
                                    start_instant = new_start;
                                }
                            }

                            // AUDIO SYNCHRONISIEREN
                            // Berechnen, wo wir zeitlich jetzt wären
                            let ref_time = if paused { pause_start_time } else { Instant::now() };

                            // Clampen, falls über den Anfang hinaus
                            // zurückgesprungen wurde
                            if start_instant > ref_time { start_instant = ref_time; }

                            // Clampen gegen Ende (Zeit > end_limit)
                            let current_diff = ref_time.duration_since(start_instant).as_secs_f64();
                            if current_diff > end_limit {
                                // Wir sind zu weit gesprungen.
                                // Wir setzen start_instant so, dass die Differenz exakt 'end_limit' ist.
                                // Formel: start = jetzt - limit
                                start_instant = ref_time - Duration::from_secs_f64(end_limit);
                            }

                            // Schutz gegen negative Zeit (falls Startzeit in Zukunft liegt durch wildes Zurückspulen)
                            let new_time_secs = if ref_time > start_instant {
                                ref_time.duration_since(start_instant).as_secs_f64()
                            } else {
                                0.0
                            };

                            // Cursor berechnen
                            let mut new_cursor = (new_time_secs * SAMPLE_RATE as f64) as usize;

                            // Bounds Check
                            // Da pcm_buffer in 'device' gemoved wurde, kennen wir die Länge hier eigentlich nicht direkt,
                            // außer wir haben sie vorher gespeichert oder nutzen den Lock.
                            // Oben haben wir `pcm_buffer` an den SoundProvider übergeben.
                            // Lösung: Wir greifen über den Lock auf die Samples zu.
                            let mut lock = device.lock();
                            let total_len = lock.samples.len();

                            if new_cursor >= total_len { new_cursor = total_len.saturating_sub(1); }

                            // Cursor setzen
                            lock.cursor = new_cursor;
                        }
                        Keycode::F => {
                            let res = canvas.window_mut().set_fullscreen(if fullscreen {
                                FullscreenType::Off
                            } else {
                                FullscreenType::Desktop
                            });
                            if let Err(_) = res {
                                println!("Wechsel in den Vollbildmodus nicht möglich.");
                            } else {
                                fullscreen = !fullscreen;
                            }
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        }

        // ZEIT BERECHNEN
        // Wenn pausiert, ist die "aktuelle Zeit" fixiert auf den Start der Pause.
        // Wenn nicht pausiert, ist es Jetzt minus Startzeitpunkt.
        let current_now = if paused { pause_start_time } else { Instant::now() };

        // Falls durch Zurückspulen start_instant in der Zukunft liegt, ist Zeit = 0
        let current_time = if current_now > start_instant {
            current_now.duration_since(start_instant).as_secs_f64()
        } else {
            0.0
        };

        // Auto-Quit-Bedingung
        // if current_time > end_limit { break 'running; }

        // Parken statt Beenden
        // Wenn das Ende erreicht ist und wir noch nicht pausiert sind
        if !paused && current_time >= end_limit {
            paused = true;
            device.pause(); // Audio stoppen

            // Trick: Wir setzen 'pause_start_time' so, dass die verstrichene Zeit
            // relativ zu 'start_instant' exakt dem 'end_limit' entspricht.
            // Formel: pause_start_time = start_instant + end_limit
            pause_start_time = start_instant + Duration::from_secs_f64(end_limit);

            // Audio-Cursor sicherheitshalber ans Ende schieben (Stille)
            let mut lock = device.lock();
            let total_len = lock.samples.len();
            lock.cursor = total_len;
        }
        // Visuelle Zeit clampen, damit wir in diesem Frame nicht über das Ziel hinausschießen
        // (Schattenvariable für current_time erstellen)
        let current_time = if current_time > end_limit { end_limit } else { current_time };

        // Größen holen
        let (w_u32, h_u32) = canvas.output_size()?;
        let w = w_u32 as i32;
        let h = h_u32 as i32;
        let keyboard_height = KEYBOARD_HEIGHT * w / (WINDOW_WIDTH as i32);
        let note_area_h = h - keyboard_height;

        let visible_time_range = note_area_h as f64 / PIXELS_PER_SECOND;
        let lookahead_time = visible_time_range + 1.0;

        // Zeichnen
        canvas.set_draw_color(Color::RGB(30, 30, 35));
        canvas.clear();

        // Reset Keys
        active_keys.fill(false);

        // Noten Zeichnen
        for n in &notes {
            if n.start_time > current_time + lookahead_time { break; }
            if (n.start_time + n.duration) < current_time - 1.0 { continue; }

            let time_diff = (n.start_time - current_time) as f32;
            let note_y = note_area_h as f32 - (time_diff * PIXELS_PER_SECOND as f32);
            let note_h = (n.duration * PIXELS_PER_SECOND) as f32;
            let draw_y = note_y - note_h;

            let is_playing = current_time >= n.start_time && current_time < (n.start_time + n.duration);
            if is_playing {
                active_keys[n.midi_key as usize] = true;
                active_colors[n.midi_key as usize] = n.color;
            }

            if n.midi_key >= MIN_MIDI && n.midi_key <= MAX_MIDI {
                let (x, width, _) = get_key_geometry(n.midi_key, w as f32);

                let mut c = n.color;
                if is_playing {
                    c.r = c.r.saturating_add(60);
                    c.g = c.g.saturating_add(60);
                    c.b = c.b.saturating_add(60);
                }

                canvas.set_draw_color(c);
                render_fill_rounded_rect(&mut canvas,
                    x as i32 + 1, draw_y as i32,
                    width as i32 - 2, note_h as i32,
                    4, CORNER_ALL).unwrap_or(());
            }
        }

        // Tastatur Zeichnen
        // 1. Weiße Tasten
        for m in MIN_MIDI..=MAX_MIDI {
            if !is_black_key(m) {
                let (x, width, _) = get_key_geometry(m, w as f32);
                let mut c = Color::RGB(220, 220, 220);

                if active_keys[m as usize] {
                    let ac = active_colors[m as usize];
                    c.r = ((ac.r as u16 + 255) / 2) as u8;
                    c.g = ((ac.g as u16 + 255) / 2) as u8;
                    c.b = ((ac.b as u16 + 255) / 2) as u8;
                }

                canvas.set_draw_color(c);
                render_fill_rounded_rect(&mut canvas,
                    x as i32, note_area_h,
                    width as i32 - 1, keyboard_height,
                    5, CORNER_BL | CORNER_BR).unwrap_or(());
            }
        }

        // 2. Schwarze Tasten
        for m in MIN_MIDI..=MAX_MIDI {
            if is_black_key(m) {
                let (x, width, _) = get_key_geometry(m, w as f32);
                let mut c = Color::RGB(20, 20, 20);

                if active_keys[m as usize] {
                    let ac = active_colors[m as usize];
                    c.r = ((ac.r as u16 + 100) / 2) as u8;
                    c.g = ((ac.g as u16 + 100) / 2) as u8;
                    c.b = ((ac.b as u16 + 100) / 2) as u8;
                }

                canvas.set_draw_color(c);
                render_fill_rounded_rect(&mut canvas,
                    x as i32, note_area_h,
                    width as i32, (keyboard_height as f32 * 0.65) as i32,
                    3, CORNER_BL | CORNER_BR).unwrap_or(());
            }
        }

        canvas.present();
    }
    Ok(())
}
