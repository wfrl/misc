// =====================================================================
// Midisynth, version 2026-01-13
// =====================================================================
// A very simple synthesizer for MIDI files, written in Rust. It gene-
// rates the sound for each note using additive synthesis of sine waves
// (fundamental and harmonics) enveloped in an ADSR curve. The audio
// signal is then encoded as PCM and packaged as a WAV file. The pro-
// gram requires no dependencies.
//
// The code was created and ported using Gemini 3, so take everything
// with a grain of salt. There may be subtle bugs that are not notice-
// able, or the specifications may not be followed in detail.
//
// Usage:
//   ./midisynth input.mid output.wav
//
// =====================================================================

use std::env;
use std::f64::consts::PI;
use std::fs::File;
use std::io::{self, Read, Seek, SeekFrom, Write};

// =====================================================================
// CONSTANTS AND TYPES
// =====================================================================

const SAMPLE_RATE: u32 = 44100;

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
    midi_key: u8,
    velocity: u8,
    channel: u8,
}

// =====================================================================
// HELPER: BINARY READING (Big Endian for MIDI)
// =====================================================================

fn read_u16_be(f: &mut File) -> io::Result<u16> {
    let mut buf = [0u8; 2];
    f.read_exact(&mut buf)?;
    Ok(u16::from_be_bytes(buf))
}

fn read_u32_be(f: &mut File) -> io::Result<u32> {
    let mut buf = [0u8; 4];
    f.read_exact(&mut buf)?;
    Ok(u32::from_be_bytes(buf))
}

fn read_varlen(f: &mut File) -> io::Result<u32> {
    let mut value: u32 = 0;
    let mut buf = [0u8; 1];
    loop {
        f.read_exact(&mut buf)?;
        let c = buf[0];
        value = (value << 7) | (c & 0x7F) as u32;
        if (c & 0x80) == 0 {
            break;
        }
    }
    Ok(value)
}

// =====================================================================
// MIDI PARSING LOGIC
// =====================================================================

fn parse_midi(filename: &str) -> io::Result<(Vec<MidiEvent>, u16)> {
    let mut f = File::open(filename).map_err(|_| {
        io::Error::new(io::ErrorKind::NotFound, "Could not open file")
    })?;

    // Header Chunk
    let mut chunk_id = [0u8; 4];
    f.read_exact(&mut chunk_id)?;
    if &chunk_id != b"MThd" {
        panic!("Invalid MIDI file (Missing MThd header).");
    }

    let _header_len = read_u32_be(&mut f)?;
    let _format = read_u16_be(&mut f)?;
    let num_tracks = read_u16_be(&mut f)?;
    let division = read_u16_be(&mut f)?;

    if (division & 0x8000) != 0 {
        panic!("Error: SMPTE timecode not supported.");
    }

    println!("MIDI Info: {} tracks, division {}", num_tracks, division);

    let mut events = Vec::new();

    // Read tracks
    for _ in 0..num_tracks {
        f.read_exact(&mut chunk_id)?;
        while &chunk_id != b"MTrk" {
            // Skip unknown chunks
            let skip = read_u32_be(&mut f)?;
            f.seek(SeekFrom::Current(skip as i64))?;
            f.read_exact(&mut chunk_id)?;
        }

        let track_len = read_u32_be(&mut f)?;
        let start_pos = f.stream_position()?;
        let end_pos = start_pos + track_len as u64;

        let mut abs_tick = 0;
        let mut running_status = 0u8;

        while f.stream_position()? < end_pos {
            let delta = read_varlen(&mut f)?;
            abs_tick += delta;

            let mut buf = [0u8; 1];
            f.read_exact(&mut buf)?;
            let byte = buf[0];
            let status;

            if byte >= 0x80 {
                status = byte;
                running_status = status;
            } else {
                status = running_status;
                // Rewind 1 byte, as the read byte was data (note, etc.)
                f.seek(SeekFrom::Current(-1))?;
            }

            if status == 0xFF {
                // Meta Event
                let mut type_buf = [0u8; 1];
                f.read_exact(&mut type_buf)?;
                let meta_type = type_buf[0];
                let len = read_varlen(&mut f)?;

                if meta_type == 0x51 && len == 3 {
                    // Set Tempo
                    let mut tbytes = [0u8; 3];
                    f.read_exact(&mut tbytes)?;
                    let micros = ((tbytes[0] as u32) << 16)
                        | ((tbytes[1] as u32) << 8)
                        | (tbytes[2] as u32);
                    events.push(MidiEvent {
                        abs_tick,
                        event_type: EventType::SetTempo,
                        channel: 0,
                        note: 0,
                        velocity: 0,
                        tempo_micros: micros,
                    });
                } else if meta_type == 0x2F {
                    // End of Track
                    f.seek(SeekFrom::Start(end_pos))?;
                    break;
                } else {
                    f.seek(SeekFrom::Current(len as i64))?;
                }
            } else if status == 0xF0 || status == 0xF7 {
                // SysEx
                let len = read_varlen(&mut f)?;
                f.seek(SeekFrom::Current(len as i64))?;
            } else {
                let cmd = status & 0xF0;

                if cmd == 0x90 { // Note On
                    let mut data = [0u8; 2];
                    f.read_exact(&mut data)?;
                    let note = data[0];
                    let vel = data[1];
                    events.push(MidiEvent {
                        abs_tick,
                        event_type: if vel > 0 { EventType::NoteOn } else { EventType::NoteOff },
                        channel: status & 0x0F,
                        note,
                        velocity: vel,
                        tempo_micros: 0,
                    });
                } else if cmd == 0x80 { // Note Off
                    let mut data = [0u8; 2];
                    f.read_exact(&mut data)?;
                    let note = data[0];
                    let vel = data[1];
                    events.push(MidiEvent {
                        abs_tick,
                        event_type: EventType::NoteOff,
                        channel: status & 0x0F,
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

    // Sort (stable sort is often safer for MIDI)
    events.sort_by_key(|e| e.abs_tick);

    Ok((events, division))
}

// =====================================================================
// CONVERSION TO NOTES
// =====================================================================

fn convert_events_to_notes(
    events: &[MidiEvent],
    division: u16,
) -> (Vec<Note>, f64) {
    let mut notes = Vec::new();
    let mut current_time = 0.0;
    let mut current_tick = 0;
    let mut micros_per_beat = 500000.0; // Default 120 BPM

    // active_notes[channel][pitch] = start_time
    // We use f64::NEG_INFINITY as "not active" marker
    let mut active_notes = [[f64::NEG_INFINITY; 128]; 16];
    let mut active_velocities = [[0u8; 128]; 16];

    for e in events {
        let delta_ticks = e.abs_tick - current_tick;
        if delta_ticks > 0 {
            let seconds_per_tick = (micros_per_beat / 1_000_000.0) / (division as f64);
            current_time += (delta_ticks as f64) * seconds_per_tick;
            current_tick = e.abs_tick;
        }

        match e.event_type {
            EventType::SetTempo => {
                micros_per_beat = e.tempo_micros as f64;
            }
            EventType::NoteOn => {
                let ch = e.channel as usize;
                let n = e.note as usize;

                // Retrigger check
                if active_notes[ch][n] != f64::NEG_INFINITY {
                    let duration = current_time - active_notes[ch][n];
                    if duration > 0.0 {
                        notes.push(Note {
                            start_time: active_notes[ch][n],
                            duration,
                            midi_key: e.note,
                            velocity: active_velocities[ch][n],
                            channel: e.channel,
                        });
                    }
                }
                active_notes[ch][n] = current_time;
                active_velocities[ch][n] = e.velocity;
            }
            EventType::NoteOff => {
                let ch = e.channel as usize;
                let n = e.note as usize;

                if active_notes[ch][n] != f64::NEG_INFINITY {
                    let duration = current_time - active_notes[ch][n];
                    if duration > 0.0 {
                        notes.push(Note {
                            start_time: active_notes[ch][n],
                            duration,
                            midi_key: e.note,
                            velocity: active_velocities[ch][n],
                            channel: e.channel,
                        });
                    }
                    active_notes[ch][n] = f64::NEG_INFINITY;
                }
            }
        }
    }

    let total_duration = current_time + 1.0; // +1 second reverb tail
    (notes, total_duration)
}

// =====================================================================
// SYNTHESIS AND WAV WRITING
// =====================================================================

fn write_wav_header(f: &mut File, total_samples: u32) -> io::Result<()> {
    let byte_rate = SAMPLE_RATE * 2; // 16 bit mono
    let data_chunk_size = total_samples * 2;
    let file_size = 36 + data_chunk_size;

    // RIFF Header
    f.write_all(b"RIFF")?;
    f.write_all(&file_size.to_le_bytes())?;
    f.write_all(b"WAVE")?;
    f.write_all(b"fmt ")?;

    let subchunk1_size = 16u32;
    let audio_format = 1u16; // PCM
    let num_channels = 1u16; // Mono
    let sample_rate = SAMPLE_RATE;
    let block_align = 2u16;
    let bits_per_sample = 16u16;

    // fmt chunk
    f.write_all(&subchunk1_size.to_le_bytes())?;
    f.write_all(&audio_format.to_le_bytes())?;
    f.write_all(&num_channels.to_le_bytes())?;
    f.write_all(&sample_rate.to_le_bytes())?;
    f.write_all(&byte_rate.to_le_bytes())?;
    f.write_all(&block_align.to_le_bytes())?;
    f.write_all(&bits_per_sample.to_le_bytes())?;

    // data chunk
    f.write_all(b"data")?;
    f.write_all(&data_chunk_size.to_le_bytes())?;

    Ok(())
}

fn midi_to_freq(key: u8) -> f64 {
    440.0 * 2.0_f64.powf((key as f64 - 69.0) / 12.0)
}

fn synthesize_and_write(
    filename: &str,
    notes: &[Note],
    total_duration: f64,
) -> io::Result<()> {
    let total_samples = (total_duration * SAMPLE_RATE as f64) as usize;

    println!("Synthesizing {} notes in {} samples...", notes.len(), total_samples);

    // Buffer initialized with 0.0
    let mut buffer: Vec<f32> = vec![0.0; total_samples];

    let overtones = [1.0, 0.5, 0.3, 0.1];
    let attack = 0.05;
    let release = 0.1;

    for n in notes {
        let is_drum = n.channel == 9; // Channel 10 in MIDI is index 9
        let freq = if is_drum { 100.0 } else { midi_to_freq(n.midi_key) };
        let duration = if is_drum { 0.05 } else { n.duration };
        let amp = (n.velocity as f64 / 127.0) * 0.3;

        let start_s = (n.start_time * SAMPLE_RATE as f64) as usize;
        let len_s = ((duration + release) * SAMPLE_RATE as f64) as usize;

        let end_loop = (start_s + len_s).min(total_samples);

        // To minimize slice checking in the loop
        if start_s >= total_samples { continue; }

        for t in 0..(end_loop - start_s) {
            let time_in_note = t as f64 / SAMPLE_RATE as f64;
            let mut sample_val = 0.0;

            if is_drum {
                sample_val = (2.0 * PI * freq * time_in_note).sin();
            } else {
                for (ov_idx, &ov_amp) in overtones.iter().enumerate() {
                    let h_freq = freq * (ov_idx as f64 + 1.0);
                    if h_freq < (SAMPLE_RATE as f64 / 2.0) {
                        sample_val += ov_amp * (2.0 * PI * h_freq * time_in_note).sin();
                    }
                }
                sample_val /= 1.9; // Normalize overtones
            }

            // Envelope
            let mut env = 1.0;
            if time_in_note < attack {
                env = time_in_note / attack;
            } else if time_in_note > duration {
                let rel_phase = time_in_note - duration;
                env = 1.0 - (rel_phase / release);
                if env < 0.0 { env = 0.0; }
            }

            buffer[start_s + t] += (sample_val * amp * env) as f32;
        }
    }

    // Normalization and writing
    let mut f = File::create(filename)?;
    write_wav_header(&mut f, total_samples as u32)?;

    // Peak Finding
    let mut max_val = 0.0f32;
    for &sample in &buffer {
        let abs_val = sample.abs();
        if abs_val > max_val {
            max_val = abs_val;
        }
    }

    let mut norm_factor = 32000.0;
    if max_val > 0.0 {
        norm_factor = 32000.0 / max_val;
    }
    if norm_factor > 32000.0 {
        norm_factor = 32000.0;
    }

    // Buffer for block-wise writing (efficiency)
    let mut out_buffer = Vec::with_capacity(total_samples);

    for sample in buffer {
        let val = (sample * norm_factor) as i32;
        let clamped = val.clamp(-32768, 32767) as i16;
        out_buffer.extend_from_slice(&clamped.to_le_bytes());
    }

    f.write_all(&out_buffer)?;

    println!("WAV written to: {}", filename);
    Ok(())
}

// =====================================================================
// MAIN
// =====================================================================

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        println!("Usage: {} <input.mid> <output.wav>", args[0]);
        return;
    }

    let (events, division) = match parse_midi(&args[1]) {
        Ok(res) => res,
        Err(e) => {
            eprintln!("Error parsing MIDI file: {}", e);
            std::process::exit(1);
        }
    };

    let (notes, total_duration) = convert_events_to_notes(&events, division);

    if notes.is_empty() {
        println!("No notes found!");
    } else if let Err(e) = synthesize_and_write(&args[2], &notes, total_duration) {
        eprintln!("Error writing WAV file: {}", e);
        std::process::exit(1);
    }
}
