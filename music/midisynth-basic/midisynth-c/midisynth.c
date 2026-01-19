/* ==================================================================
 * Midisynth, version 2026-01-13 
 * ==================================================================
 * A very simple synthesizer for MIDI files, written in C90. It gene-
 * rates the sound for each note using additive synthesis of sine waves
 * (fundamental and harmonics) enveloped in an ADSR curve. The audio
 * signal is then encoded as PCM and packaged as a WAV file. The pro-
 * gram requires no dependencies.
 *
 * The code was created and ported using Gemini 3, so take everything
 * with a grain of salt. There may be subtle bugs that are not notice-
 * able, or the specifications may not be followed in detail.
 *
 * Compile:
 *    gcc midisynth.c -o midisynth -lm
 *
 * Usage:
 *    ./midisynth input.mid output.wav
 * ================================================================== */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

/* 
 * Note: <stdint.h> is technically C99. Many C90 compilers still provide
 * it. If the compiler doesn't find it, the types must be defined manu-
 * ally (e.g., typedef unsigned short uint16_t;).
 */
#include <stdint.h>

#define SAMPLE_RATE 44100
#define PI 3.14159265358979323846

/* ==================================================================
   DATA STRUCTURES
   ================================================================== */

typedef enum {
    EVENT_NOTE_ON,
    EVENT_NOTE_OFF,
    EVENT_SET_TEMPO,
    EVENT_OTHER
} EventType;

/* A raw MIDI event after initial parsing */
typedef struct {
    uint32_t abs_tick;  /* Absolute time in ticks */
    EventType type;
    int channel;
    int note;
    int velocity;
    int tempo_micros;   /* Only relevant for tempo events */
} MidiEvent;

/* A processed note with time in seconds */
typedef struct {
    double start_time;
    double duration;
    int midi_key;
    int velocity;
    int channel;
} Note;

/* ==================================================================
   HELPER: FILE READING (BIG ENDIAN PARSING)
   ================================================================== */

/* Wrapper for fread, aborts immediately on error */
void safe_fread(void *ptr, size_t size, size_t nmemb, FILE *stream) {
    size_t ret = fread(ptr, size, nmemb, stream);
    if (ret != nmemb) {
        fprintf(stderr, "Error: Unexpected end of file or read error.\n");
        exit(1);
    }
}

uint16_t read_be16(FILE *f) {
    uint8_t bytes[2];
    safe_fread(bytes, 1, 2, f);
    return (uint16_t)((bytes[0] << 8) | bytes[1]);
}

uint32_t read_be32(FILE *f) {
    uint8_t bytes[4];
    safe_fread(bytes, 1, 4, f);
    return ((uint32_t)bytes[0] << 24) | ((uint32_t)bytes[1] << 16) |
        ((uint32_t)bytes[2] << 8) | bytes[3];
}

uint32_t read_varlen(FILE *f) {
    uint32_t value = 0;
    uint8_t c;
    do {
        safe_fread(&c, 1, 1, f);
        value = (value << 7) | (c & 0x7F);
    } while (c & 0x80);
    return value;
}

/* ==================================================================
   MIDI PARSING LOGIC
   ================================================================== */

/* Dynamic array for events */
MidiEvent *events = NULL;
size_t event_count = 0;
size_t event_capacity = 0;

void add_event(MidiEvent e) {
    if (event_count >= event_capacity) {
        size_t new_capacity = (event_capacity == 0) ? 1024 : event_capacity * 2;
        MidiEvent *temp = realloc(events, new_capacity * sizeof(MidiEvent));
        if (temp == NULL) {
            fprintf(stderr, "Error: Out of memory reallocating events.\n");
            free(events);
            exit(1);
        }
        events = temp;
        event_capacity = new_capacity;
    }
    events[event_count++] = e;
}

/* Sorting function for qsort (by ticks) */
int compare_events(const void *a, const void *b) {
    const MidiEvent *ea = (const MidiEvent *)a;
    const MidiEvent *eb = (const MidiEvent *)b;
    if (ea->abs_tick < eb->abs_tick) return -1;
    if (ea->abs_tick > eb->abs_tick) return 1;
    return 0;
}

void parse_midi(const char *filename, uint16_t *division) {
    FILE *f;
    char chunk_id[5] = {0};
    uint16_t num_tracks;
    int t;

    f = fopen(filename, "rb");
    if (!f) {
        fprintf(stderr, "Error: Could not open file.\n");
        exit(1);
    }

    /* Header Chunk */
    safe_fread(chunk_id, 1, 4, f);
    if (strcmp(chunk_id, "MThd") != 0) {
        fprintf(stderr, "Error: Not a valid MIDI file.\n");
        exit(1);
    }

    read_be32(f); /* Header length (skip) */
    read_be16(f); /* Format (skip) */
    num_tracks = read_be16(f);
    *division = read_be16(f);

    if (*division & 0x8000) {
        fprintf(stderr, "Error: SMPTE timecode is not supported.\n");
        exit(1);
    }

    printf("MIDI Info: %d Tracks, Division %d\n", num_tracks, *division);

    /* Read Tracks */
    for (t = 0; t < num_tracks; t++) {
        uint32_t track_len;
        long track_start;
        long track_end;
        uint32_t abs_tick = 0;
        uint8_t running_status = 0;

        safe_fread(chunk_id, 1, 4, f);
        while (strcmp(chunk_id, "MTrk") != 0) {
            /* Skip unknown chunks */
            uint32_t skip = read_be32(f);
            fseek(f, skip, SEEK_CUR);
            safe_fread(chunk_id, 1, 4, f);
        }

        track_len = read_be32(f);
        track_start = ftell(f);
        track_end = track_start + track_len;

        while (ftell(f) < track_end) {
            uint32_t delta = read_varlen(f);
            uint8_t status;
            uint8_t byte;

            abs_tick += delta;
            safe_fread(&byte, 1, 1, f);

            if (byte >= 0x80) {
                status = byte;
                running_status = status;
            } else {
                status = running_status;
                fseek(f, -1, SEEK_CUR); /* Rewind 1 byte */
            }

            /* Process Events */
            if (status == 0xFF) { /* Meta Event */
                uint8_t type;
                uint32_t len;
                safe_fread(&type, 1, 1, f);
                len = read_varlen(f);

                if (type == 0x51 && len == 3) { /* Set Tempo */
                    uint8_t tbytes[3];
                    int micros;
                    MidiEvent e;

                    safe_fread(tbytes, 1, 3, f);
                    micros = (tbytes[0] << 16) | (tbytes[1] << 8) | tbytes[2];

                    e.abs_tick = abs_tick;
                    e.type = EVENT_SET_TEMPO;
                    e.channel = 0;
                    e.note = 0;
                    e.velocity = 0;
                    e.tempo_micros = micros;
                    add_event(e);
                } else if (type == 0x2F) {
                    /* End of Track -> End loop for this track */
                    fseek(f, track_end, SEEK_SET);
                    break;
                } else {
                    fseek(f, len, SEEK_CUR); /* Skip meta data */
                }
            } else if (status == 0xF0 || status == 0xF7) { /* SysEx */
                uint32_t len = read_varlen(f);
                fseek(f, len, SEEK_CUR);
            } else if ((status & 0xF0) == 0x90) { /* Note On */
                uint8_t note, vel;
                MidiEvent e;
                safe_fread(&note, 1, 1, f);
                safe_fread(&vel, 1, 1, f);

                e.abs_tick = abs_tick;
                e.type = (vel > 0 ? EVENT_NOTE_ON : EVENT_NOTE_OFF);
                e.channel = status & 0x0F;
                e.note = note;
                e.velocity = vel;
                e.tempo_micros = 0;
                add_event(e);
            } else if ((status & 0xF0) == 0x80) { /* Note Off */
                uint8_t note, vel;
                MidiEvent e;
                safe_fread(&note, 1, 1, f);
                safe_fread(&vel, 1, 1, f);

                e.abs_tick = abs_tick;
                e.type = EVENT_NOTE_OFF;
                e.channel = status & 0x0F;
                e.note = note;
                e.velocity = vel;
                e.tempo_micros = 0;
                add_event(e);
            } else {
                /* Other Channel Messages (Control Change etc.) */
                uint8_t cmd = status & 0xF0;
                if (cmd == 0xC0 || cmd == 0xD0) {
                    fseek(f, 1, SEEK_CUR);
                } else {
                    fseek(f, 2, SEEK_CUR);
                }
            }
        }
    }
    fclose(f);

    /* Sort all events by time */
    qsort(events, event_count, sizeof(MidiEvent), compare_events);
}

/* ==================================================================
   CONVERSION TO NOTES (Ticks -> Seconds)
   ================================================================== */

Note* convert_events_to_notes(
    uint16_t division,
    size_t *out_note_count,
    double *out_total_duration
) {
    Note *notes;
    size_t note_idx = 0;
    size_t i;
    int c, n;

    double current_time = 0.0;
    uint32_t current_tick = 0;
    double micros_per_beat = 500000.0; /* Default 120 BPM */

    /* Temporary storage for active notes */
    double active_notes[16][128];
    int active_velocities[16][128];

    notes = malloc(sizeof(Note) * event_count); /* Max possible count */

    for(c=0; c<16; c++)
        for(n=0; n<128; n++)
            active_notes[c][n] = -1.0;

    for (i = 0; i < event_count; i++) {
        MidiEvent e = events[i];

        /* Calculate time progress */
        uint32_t delta_ticks = e.abs_tick - current_tick;
        if (delta_ticks > 0) {
            double seconds_per_tick = (micros_per_beat / 1000000.0) / (double)division;
            current_time += delta_ticks * seconds_per_tick;
            current_tick = e.abs_tick;
        }

        if (e.type == EVENT_SET_TEMPO) {
            micros_per_beat = (double)e.tempo_micros;
        }
        else if (e.type == EVENT_NOTE_ON) {
            /* If note is already on, finish it first (retrigger), then restart */
            if (active_notes[e.channel][e.note] >= 0.0) {
                 Note note_obj;
                 note_obj.start_time = active_notes[e.channel][e.note];
                 note_obj.duration = current_time - note_obj.start_time;
                 note_obj.midi_key = e.note;
                 note_obj.velocity = active_velocities[e.channel][e.note];
                 note_obj.channel = e.channel;
                 if (note_obj.duration > 0) notes[note_idx++] = note_obj;
            }
            active_notes[e.channel][e.note] = current_time;
            active_velocities[e.channel][e.note] = e.velocity;
        }
        else if (e.type == EVENT_NOTE_OFF) {
            if (active_notes[e.channel][e.note] >= 0.0) {
                Note note_obj;
                note_obj.start_time = active_notes[e.channel][e.note];
                note_obj.duration = current_time - note_obj.start_time;
                note_obj.midi_key = e.note;
                note_obj.velocity = active_velocities[e.channel][e.note];
                note_obj.channel = e.channel;
                active_notes[e.channel][e.note] = -1.0;
                if (note_obj.duration > 0) notes[note_idx++] = note_obj;
            }
        }
    }

    *out_note_count = note_idx;
    /* Total duration + some reverb tail */
    *out_total_duration = current_time + 1.0;
    return notes;
}

/* ==================================================================
   SYNTHESIS AND WAV WRITING
   ================================================================== */

void write_wav_header(FILE *f, int total_samples) {
    int byte_rate = SAMPLE_RATE * 2; /* 16 bit mono */
    int data_chunk_size = total_samples * 2;
    int file_size = 36 + data_chunk_size;
    int subchunk1_size = 16;
    short audio_format = 1; /* PCM */
    short num_channels = 1; /* Mono */
    int sample_rate = SAMPLE_RATE;
    short block_align = 2;
    short bits_per_sample = 16;

    fwrite("RIFF", 1, 4, f);
    fwrite(&file_size, 4, 1, f);
    fwrite("WAVE", 1, 4, f);
    fwrite("fmt ", 1, 4, f);

    fwrite(&subchunk1_size, 4, 1, f);
    fwrite(&audio_format, 2, 1, f);
    fwrite(&num_channels, 2, 1, f);
    fwrite(&sample_rate, 4, 1, f);
    fwrite(&byte_rate, 4, 1, f);
    fwrite(&block_align, 2, 1, f);
    fwrite(&bits_per_sample, 2, 1, f);

    fwrite("data", 1, 4, f);
    fwrite(&data_chunk_size, 4, 1, f);
}

/* Frequency formula */
double midi_to_freq(int key) {
    return 440.0 * pow(2.0, (key - 69) / 12.0);
}

void synthesize_and_write(
    const char *filename,
    const Note *notes,
    size_t note_count,
    double total_duration
) {
    size_t total_samples = (size_t)(total_duration * SAMPLE_RATE);
    float *buffer;
    size_t i;

    /* Additive synthesis parameters */
    const double overtones[] = {1.0, 0.5, 0.3, 0.1};
    int num_overtones = 4;
    double attack = 0.05;
    double release = 0.1;

    /* File and helper variables for output */
    FILE *f;
    int16_t *pcm_buffer;
    float max_val = 0.0f;
    float norm_factor;

    /* We use float for mixing to avoid clipping before normalization */
    buffer = calloc(total_samples, sizeof(float));
    if (!buffer) {
        fprintf(stderr, "Error: Not enough memory for audio buffer.\n");
        exit(1);
    }

    printf("Synthesizing %lu notes in %lu samples...\n",
        (unsigned long)note_count, (unsigned long)total_samples);

    for (i = 0; i < note_count; i++) {
        Note n = notes[i];
        int is_drum = (n.channel == 9);
        double freq = is_drum ? 100.0 : midi_to_freq(n.midi_key);
        double duration = is_drum ? 0.05 : n.duration;
        double amp = (n.velocity / 127.0) * 0.3; /* 0.3 as headroom */

        const size_t start_s = (size_t)(n.start_time * SAMPLE_RATE);
        const size_t len_s = (size_t)((duration + release) * SAMPLE_RATE);
        size_t end_s = start_s + len_s;
        size_t t;

        if (end_s > total_samples) end_s = total_samples;

        for (t = 0; start_s + t < end_s; t++) {
            double time_in_note = (double)t / SAMPLE_RATE;
            double sample_val = 0.0;
            double env = 1.0;

            /* Add up overtones */
            if (is_drum) {
                sample_val = sin(2 * PI * freq * time_in_note);
            } else {
                int ov;
                for (ov = 0; ov < num_overtones; ov++) {
                    double h_freq = freq * (ov + 1);
                    if (h_freq < SAMPLE_RATE / 2) {
                        sample_val += overtones[ov] * sin(2 * PI * h_freq * time_in_note);
                    }
                }
                /* Normalize overtones (sum approx 1.9) */
                sample_val /= 1.9;
            }

            /* Envelope (ADSR - simple: Attack & Release) */
            if (time_in_note < attack) {
                env = time_in_note / attack;
            } else if (time_in_note > duration) {
                double rel_phase = time_in_note - duration;
                env = 1.0 - (rel_phase / release);
                if (env < 0) env = 0;
            }

            buffer[start_s + t] += (float)(sample_val * amp * env);
        }
    }

    /* Normalize and convert to int16 */
    f = fopen(filename, "wb");
    if (!f) {
        fprintf(stderr, "Error: Could not write output file.\n");
        free(buffer);
        exit(1);
    }

    write_wav_header(f, total_samples);

    pcm_buffer = malloc(total_samples * sizeof(int16_t));

    /* Peak finding for normalization */
    for (i = 0; i < total_samples; i++) {
        /* fabs instead of fabsf for C90 (returns double, buffer is float -> ok) */
        if (fabs(buffer[i]) > max_val) max_val = (float)fabs(buffer[i]);
    }

    norm_factor = 32000.0f;
    if (max_val > 0.0f) norm_factor = 32000.0f / max_val;
    /* Limit to avoid extreme volume boost on silence */
    if (norm_factor > 32000.0f) norm_factor = 32000.0f;

    for (i = 0; i < total_samples; i++) {
        int32_t val = (int32_t)(buffer[i] * norm_factor);
        if (val > 32767) val = 32767;
        if (val < -32768) val = -32768;
        pcm_buffer[i] = (int16_t)val;
    }

    fwrite(pcm_buffer, sizeof(int16_t), total_samples, f);

    fclose(f);
    free(buffer);
    free(pcm_buffer);
    printf("WAV written to: %s\n", filename);
}

/* ==================================================================
   MAIN
   ================================================================== */

int main(int argc, char **argv) {
    uint16_t division;
    size_t note_count;
    double total_duration;
    Note *notes;

    if (argc < 3) {
        printf("Usage: %s <input.mid> <output.wav>\n", argv[0]);
        return 1;
    }

    parse_midi(argv[1], &division);

    notes = convert_events_to_notes(division, &note_count, &total_duration);

    if (note_count == 0) {
        printf("No notes found!\n");
    } else {
        synthesize_and_write(argv[2], notes, note_count, total_duration);
    }

    /* Cleanup */
    if (events) free(events);
    if (notes) free(notes);

    return 0;
}
