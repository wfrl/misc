// =====================================================================
// Midisynth, version 2026-01-13
// =====================================================================
// A very simple synthesizer for MIDI files, written in C#. It gene-
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
//    ./midisynth input.mid output.wav
// =====================================================================

using System;
using System.Collections.Generic;
using System.IO;
using System.Text;

namespace MidisynthPort {

// Data structures
public enum EventType {
    NoteOn,
    NoteOff,
    SetTempo,
    Other
}

public class MidiEvent {
    public uint AbsTick;
    public EventType Type;
    public int Channel;
    public int Note;
    public int Velocity;
    public int TempoMicros;
}

public class Note {
    public double StartTime;
    public double Duration;
    public int MidiKey;
    public int Velocity;
    public int Channel;
}

class Program {
    const int SampleRate = 44100;
    const double PI = 3.14159265358979323846;

    static void Main(string[] args) {
        if (args.Length < 2) {
            Console.WriteLine("Usage: midisynth <input.mid> <output.wav>");
            return;
        }
        try {
            string inputFile = args[0];
            string outputFile = args[1];

            ushort division;
            List<MidiEvent> events = ParseMidi(inputFile, out division);

            double totalDuration;
            List<Note> notes = ConvertEventsToNotes(events, division, out totalDuration);

            if (notes.Count == 0) {
                Console.WriteLine("No notes found!");
            } else {
                SynthesizeAndWrite(outputFile, notes, totalDuration);
            }
        } catch (Exception ex) {
            Console.Error.WriteLine("Error: " + ex.Message);
        }
    }

    // =================================================================
    // HELPER: BIG ENDIAN READING
    // =================================================================

    static ushort ReadBe16(BinaryReader br) {
        byte[] bytes = br.ReadBytes(2);
        if (bytes.Length < 2) throw new EndOfStreamException();
        return (ushort)((bytes[0] << 8) | bytes[1]);
    }

    static uint ReadBe32(BinaryReader br) {
        byte[] bytes = br.ReadBytes(4);
        if (bytes.Length < 4) throw new EndOfStreamException();
        return (uint)((bytes[0] << 24) | (bytes[1] << 16) | (bytes[2] << 8) | bytes[3]);
    }

    static uint ReadVarLen(BinaryReader br) {
        uint value = 0;
        byte c;
        do {
            c = br.ReadByte();
            value = (value << 7) | (uint)(c & 0x7F);
        } while ((c & 0x80) != 0);
        return value;
    }

    // =================================================================
    // MIDI PARSING LOGIC
    // =================================================================

    static List<MidiEvent> ParseMidi(string filename, out ushort division) {
        List<MidiEvent> allEvents = new List<MidiEvent>();

        using (FileStream fs = File.OpenRead(filename))
        using (BinaryReader br = new BinaryReader(fs))
        {
            // Header Chunk
            byte[] chunkId = br.ReadBytes(4);
            if (Encoding.ASCII.GetString(chunkId) != "MThd")
                throw new Exception("Not a valid MIDI file.");

            ReadBe32(br); // Header length (skip)
            ReadBe16(br); // Format (skip)
            ushort numTracks = ReadBe16(br);
            division = ReadBe16(br);

            if ((division & 0x8000) != 0)
                throw new Exception("SMPTE timecode is not supported.");

            Console.WriteLine($"MIDI Info: {numTracks} Tracks, Division {division}");

            // Read tracks
            for (int t = 0; t < numTracks; t++) {
                chunkId = br.ReadBytes(4);
                while (Encoding.ASCII.GetString(chunkId) != "MTrk") {
                    uint skip = ReadBe32(br);
                    fs.Seek(skip, SeekOrigin.Current);
                    chunkId = br.ReadBytes(4);
                }

                uint trackLen = ReadBe32(br);
                long trackEnd = fs.Position + trackLen;
                uint absTick = 0;
                byte runningStatus = 0;

                while (fs.Position < trackEnd) {
                    uint delta = ReadVarLen(br);
                    absTick += delta;

                    byte status;
                    byte b = br.ReadByte();

                    if (b >= 0x80) {
                        status = b;
                        runningStatus = status;
                    } else {
                        status = runningStatus;
                        fs.Seek(-1, SeekOrigin.Current); // Rewind 1 byte
                    }

                    if (status == 0xFF) // Meta event
                    {
                        byte type = br.ReadByte();
                        uint len = ReadVarLen(br);

                        if (type == 0x51 && len == 3) // Set tempo
                        {
                            byte[] tbytes = br.ReadBytes(3);
                            int micros = (tbytes[0] << 16) | (tbytes[1] << 8) | tbytes[2];

                            allEvents.Add(new MidiEvent {
                                AbsTick = absTick,
                                Type = EventType.SetTempo,
                                TempoMicros = micros
                            });
                        }
                        else if (type == 0x2F) // End of track
                        {
                            fs.Seek(trackEnd, SeekOrigin.Begin);
                            break;
                        } else {
                            fs.Seek(len, SeekOrigin.Current); // Skip meta data
                        }
                    }
                    else if (status == 0xF0 || status == 0xF7) // SysEx
                    {
                        uint len = ReadVarLen(br);
                        fs.Seek(len, SeekOrigin.Current);
                    }
                    else if ((status & 0xF0) == 0x90) // Note On
                    {
                        byte note = br.ReadByte();
                        byte vel = br.ReadByte();
                        allEvents.Add(new MidiEvent
                        {
                            AbsTick = absTick,
                            Type = (vel > 0 ? EventType.NoteOn : EventType.NoteOff),
                            Channel = status & 0x0F,
                            Note = note,
                            Velocity = vel
                        });
                    }
                    else if ((status & 0xF0) == 0x80) // Note Off
                    {
                        byte note = br.ReadByte();
                        byte vel = br.ReadByte();
                        allEvents.Add(new MidiEvent
                        {
                            AbsTick = absTick,
                            Type = EventType.NoteOff,
                            Channel = status & 0x0F,
                            Note = note,
                            Velocity = vel
                        });
                    }
                    else // Other (Control Change, etc.)
                    {
                        byte cmd = (byte)(status & 0xF0);
                        if (cmd == 0xC0 || cmd == 0xD0)
                            fs.Seek(1, SeekOrigin.Current);
                        else
                            fs.Seek(2, SeekOrigin.Current);
                    }
                }
            }
        }

        // Sort all events by time
        allEvents.Sort((a, b) => a.AbsTick.CompareTo(b.AbsTick));
        return allEvents;
    }

    // =================================================================
    // CONVERSION TO NOTES (Ticks -> Seconds)
    // =================================================================

    static List<Note> ConvertEventsToNotes(
        List<MidiEvent> events,
        ushort division,
        out double totalDuration
    ) {
        List<Note> notes = new List<Note>();
        double currentTime = 0.0;
        uint currentTick = 0;
        double microsPerBeat = 500000.0; // Default 120 BPM

        // -1.0 means note is inactive
        double[,] activeNotes = new double[16, 128];
        int[,] activeVelocities = new int[16, 128];

        for (int c = 0; c < 16; c++)
            for (int n = 0; n < 128; n++)
                activeNotes[c, n] = -1.0;

        foreach (var e in events) {
            // Calculate time progress
            uint deltaTicks = e.AbsTick - currentTick;
            if (deltaTicks > 0) {
                double secondsPerTick = (microsPerBeat / 1000000.0) / (double)division;
                currentTime += deltaTicks * secondsPerTick;
                currentTick = e.AbsTick;
            }

            if (e.Type == EventType.SetTempo) {
                microsPerBeat = e.TempoMicros;
            }
            else if (e.Type == EventType.NoteOn) {
                // If note is already on, finish it first (retrigger),
                // then restart
                if (activeNotes[e.Channel, e.Note] >= 0.0) {
                    Note newNote = new Note {
                        StartTime = activeNotes[e.Channel, e.Note],
                        Duration = currentTime - activeNotes[e.Channel, e.Note],
                        MidiKey = e.Note,
                        Velocity = activeVelocities[e.Channel, e.Note],
                        Channel = e.Channel
                    };
                    if (newNote.Duration > 0) notes.Add(newNote);
                }
                activeNotes[e.Channel, e.Note] = currentTime;
                activeVelocities[e.Channel, e.Note] = e.Velocity;
            } else if (e.Type == EventType.NoteOff) {
                if (activeNotes[e.Channel, e.Note] >= 0.0) {
                    Note newNote = new Note {
                        StartTime = activeNotes[e.Channel, e.Note],
                        Duration = currentTime - activeNotes[e.Channel, e.Note],
                        MidiKey = e.Note,
                        Velocity = activeVelocities[e.Channel, e.Note],
                        Channel = e.Channel
                    };
                    activeNotes[e.Channel, e.Note] = -1.0;
                    if (newNote.Duration > 0) notes.Add(newNote);
                }
            }
        }

        // Total duration + some reverb tail
        totalDuration = currentTime + 1.0;
        return notes;
    }

    // =================================================================
    // SYNTHESIS AND WAV WRITING
    // =================================================================

    static double MidiToFreq(int key) {
        return 440.0 * Math.Pow(2.0, (key - 69) / 12.0);
    }

    static void WriteWavHeader(BinaryWriter bw, int totalSamples) {
        int byteRate = SampleRate * 2; // 16 bit mono
        int dataChunkSize = totalSamples * 2;
        int fileSize = 36 + dataChunkSize;
        int subchunk1Size = 16;
        short audioFormat = 1; // PCM
        short numChannels = 1; // Mono
        int sampleRate = SampleRate;
        short blockAlign = 2;
        short bitsPerSample = 16;

        bw.Write(Encoding.ASCII.GetBytes("RIFF"));
        bw.Write(fileSize);
        bw.Write(Encoding.ASCII.GetBytes("WAVE"));
        bw.Write(Encoding.ASCII.GetBytes("fmt "));

        bw.Write(subchunk1Size);
        bw.Write(audioFormat);
        bw.Write(numChannels);
        bw.Write(sampleRate);
        bw.Write(byteRate);
        bw.Write(blockAlign);
        bw.Write(bitsPerSample);

        bw.Write(Encoding.ASCII.GetBytes("data"));
        bw.Write(dataChunkSize);
    }

    static void SynthesizeAndWrite(
        string filename,
        List<Note> notes,
        double totalDuration
    ) {
        long totalSamples = (long)(totalDuration * SampleRate);
        float[] buffer = new float[totalSamples];

        // Additive synthesis parameters
        double[] overtones = {1.0, 0.5, 0.3, 0.1};
        int numOvertones = 4;
        double attack = 0.05;
        double release = 0.1;

        Console.WriteLine($"Synthesizing {notes.Count} notes in {totalSamples} samples...");

        foreach (var n in notes) {
            bool isDrum = (n.Channel == 9); // Channel 10 (index 9) is percussion
            double freq = isDrum ? 100.0 : MidiToFreq(n.MidiKey);
            double duration = isDrum ? 0.05 : n.Duration;
            double amp = (n.Velocity / 127.0) * 0.3; // 0.3 as headroom

            long startS = (long)(n.StartTime * SampleRate);
            long lenS = (long)((duration + release) * SampleRate);
            long endS = startS + lenS;

            if (endS > totalSamples) endS = totalSamples;

            for (long t = 0; t < lenS && (startS + t) < totalSamples; t++) {
                double timeInNote = (double)t / SampleRate;
                double sampleVal = 0.0;
                double env = 1.0;

                // Add up overtones
                if (isDrum) {
                    sampleVal = Math.Sin(2 * PI * freq * timeInNote);
                } else {
                    for (int ov = 0; ov < numOvertones; ov++) {
                        double hFreq = freq * (ov + 1);
                        if (hFreq < SampleRate / 2) {
                            sampleVal += overtones[ov] * Math.Sin(2 * PI * hFreq * timeInNote);
                        }
                    }
                    // Normalize overtones (sum approx 1.9)
                    sampleVal /= 1.9;
                }

                // Envelope (ADSR - simple: Attack & Release)
                if (timeInNote < attack) {
                    env = timeInNote / attack;
                } else if (timeInNote > duration) {
                    double relPhase = timeInNote - duration;
                    env = 1.0 - (relPhase / release);
                    if (env < 0) env = 0;
                }

                buffer[startS + t] += (float)(sampleVal * amp * env);
            }
        }

        // Normalize and convert to int16
        using (FileStream fs = File.Create(filename))
        using (BinaryWriter bw = new BinaryWriter(fs))
        {
            WriteWavHeader(bw, (int)totalSamples);

            // Peak finding for normalization
            float maxVal = 0.0f;
            for (long i = 0; i < totalSamples; i++) {
                if (Math.Abs(buffer[i]) > maxVal) maxVal = Math.Abs(buffer[i]);
            }

            float normFactor = 32000.0f;
            if (maxVal > 0.0f) normFactor = 32000.0f / maxVal;
            // Limit to avoid extreme volume boost on silence
            if (normFactor > 32000.0f) normFactor = 32000.0f;

            for (long i = 0; i < totalSamples; i++) {
                int val = (int)(buffer[i] * normFactor);
                if (val > 32767) val = 32767;
                if (val < -32768) val = -32768;
                bw.Write((short)val);
            }
        }

        Console.WriteLine($"WAV written to: {filename}");
    }
}

} // namespace
