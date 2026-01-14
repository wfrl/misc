/* ==================================================================
 * Mivi -- Ein MIDI-Visualizer und Synthesizer (Portierung auf C)
 * Version 2026-01-14
 * ================================================================== */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <SDL2/SDL.h>

/* Für popen/pclose auf POSIX-Systemen (Linux/Mac) */
#ifndef _WIN32
#include <unistd.h>
#endif

/* ==================================================================
   KONFIGURATION UND KONSTANTEN
   ================================================================== */
#define SAMPLE_RATE 44100
#define AUDIO_CHANNELS 1
#define AUDIO_FORMAT AUDIO_S16SYS
#define PI 3.14159265358979323846

#define WINDOW_WIDTH 1200
#define WINDOW_HEIGHT 800
#define KEYBOARD_HEIGHT 100
#define PIXELS_PER_SECOND 150

/* Midi-Bereich für Visualisierung (wie im Python-Skript) */
#define MIN_MIDI 21  /* A0 */
#define MAX_MIDI 108 /* C8 */

/* ==================================================================
   DATENSTRUKTUREN
   ================================================================== */

typedef enum {
    EVENT_NOTE_ON,
    EVENT_NOTE_OFF,
    EVENT_SET_TEMPO,
    EVENT_OTHER
} EventType;

typedef struct {
    uint32_t abs_tick;
    EventType type;
    int channel;
    int note;
    int velocity;
    int tempo_micros;
} MidiEvent;

typedef struct {
    double start_time;
    double duration;
    int midi_key;
    int velocity;
    int channel;
    SDL_Color color; /* Neu: Farbe direkt speichern */
} Note;

/* Globale Struktur für Audio-Wiedergabe */
typedef struct {
    int16_t *pcm_buffer;    /* Der gesamte Song im RAM */
    size_t total_samples;
    volatile size_t play_cursor; /* Aktuelle Abspielposition */
} AudioContext;

/* ==================================================================
   HELPER: FARBEN UND KEYBOARD
   ================================================================== */

SDL_Color get_channel_color(int channel) {
    /* Einfache Mapping-Tabelle ähnlich dem Python-Skript */
    SDL_Color colors[] = {
        {0, 220, 220, 255}, {255, 0, 200, 255}, {255, 220, 0, 255},
        {0, 200, 100, 255}, {100, 100, 255, 255}, {255, 100, 100, 255},
        {200, 0, 255, 255}, {0, 255, 100, 255}, {255, 128, 0, 255}
    };
    if (channel == 9) return (SDL_Color){150, 150, 150, 255}; /* Drums */
    return colors[channel % 9];
}

int is_black_key(int midi) {
    int note_in_octave = midi % 12;
    return (note_in_octave == 1 || note_in_octave == 3 ||
            note_in_octave == 6 || note_in_octave == 8 ||
            note_in_octave == 10);
}

/* Berechnet X-Position und Breite für Tasten */
void get_key_geometry(
    int midi_note, float total_width,
    float *x, float *w, int *is_black
) {
    /* Zähle weiße Tasten im Bereich */
    int white_keys_total = 0;
    int i;
    for (i = MIN_MIDI; i <= MAX_MIDI; i++) {
        if (!is_black_key(i)) white_keys_total++;
    }

    float wk_width = total_width / (float)white_keys_total;
    float bk_width = wk_width * 0.65f;

    /* Zähle weiße Tasten bis zur aktuellen Note */
    int current_wk_index = 0;
    for (i = MIN_MIDI; i < midi_note; i++) {
        if (!is_black_key(i)) current_wk_index++;
    }

    float pos = current_wk_index * wk_width;

    *is_black = is_black_key(midi_note);
    if (*is_black) {
        *x = pos - (bk_width / 2.0f);
        *w = bk_width;
    } else {
        *x = pos;
        *w = wk_width;
    }
}

/* ==================================================================
   MIDI-PARSER
   ================================================================== */
/* Wrapper für fread */
void safe_fread(void *ptr, size_t size, size_t nmemb, FILE *stream) {
    if (fread(ptr, size, nmemb, stream) != nmemb) {
        fprintf(stderr, "Fehler: Unerwartetes Dateiende.\n");
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

MidiEvent *events = NULL;
size_t event_count = 0;
size_t event_capacity = 0;

void add_event(MidiEvent e) {
    if (event_count >= event_capacity) {
        event_capacity = (event_capacity == 0) ? 1024 : event_capacity * 2;
        events = realloc(events, event_capacity * sizeof(MidiEvent));
    }
    events[event_count++] = e;
}

int compare_events(const void *a, const void *b) {
    const MidiEvent *ea = (const MidiEvent *)a;
    const MidiEvent *eb = (const MidiEvent *)b;
    if (ea->abs_tick < eb->abs_tick) return -1;
    if (ea->abs_tick > eb->abs_tick) return 1;
    return 0;
}

void parse_midi(const char *filename, uint16_t *division) {
    FILE *f = fopen(filename, "rb");
    if (!f) {
        fprintf(stderr, "Kann Datei nicht öffnen: %s\n", filename);
        exit(1);
    }

    char chunk_id[5] = {0};
    safe_fread(chunk_id, 1, 4, f);
    if (strcmp(chunk_id, "MThd") != 0) {
        fprintf(stderr, "Kein gültiges MIDI.\n");
        exit(1);
    }

    read_be32(f); read_be16(f); /* Skip len/fmt */
    uint16_t num_tracks = read_be16(f);
    *division = read_be16(f);

    if (*division & 0x8000) {
        fprintf(stderr, "SMPTE nicht unterstützt.\n");
        exit(1);
    }

    for (int t = 0; t < num_tracks; t++) {
        safe_fread(chunk_id, 1, 4, f);
        while (strcmp(chunk_id, "MTrk") != 0) {
            uint32_t skip = read_be32(f);
            fseek(f, skip, SEEK_CUR);
            safe_fread(chunk_id, 1, 4, f);
        }
        uint32_t track_len = read_be32(f);
        long track_end = ftell(f) + track_len;
        uint32_t abs_tick = 0;
        uint8_t running_status = 0;

        while (ftell(f) < track_end) {
            abs_tick += read_varlen(f);
            uint8_t byte;
            safe_fread(&byte, 1, 1, f);
            uint8_t status = (byte >= 0x80) ? (running_status = byte) : running_status;
            if (byte < 0x80) fseek(f, -1, SEEK_CUR);

            if (status == 0xFF) {
                uint8_t type; safe_fread(&type, 1, 1, f);
                uint32_t len = read_varlen(f);
                if (type == 0x51 && len == 3) {
                    uint8_t tb[3]; safe_fread(tb, 1, 3, f);
                    int micros = (tb[0]<<16) | (tb[1]<<8) | tb[2];
                    MidiEvent e = {abs_tick, EVENT_SET_TEMPO, 0, 0, 0, micros};
                    add_event(e);
                } else fseek(f, len, SEEK_CUR);
            } else if (status == 0xF0 || status == 0xF7) {
                fseek(f, read_varlen(f), SEEK_CUR);
            } else if ((status & 0xF0) == 0x90 || (status & 0xF0) == 0x80) {
                uint8_t n, v; safe_fread(&n, 1, 1, f); safe_fread(&v, 1, 1, f);
                int is_on = ((status & 0xF0) == 0x90) && (v > 0);
                MidiEvent e = {
                    abs_tick,
                    is_on ? EVENT_NOTE_ON : EVENT_NOTE_OFF,
                    status & 0x0F, n, v, 0
                };
                add_event(e);
            } else {
                fseek(f, ((status & 0xF0) == 0xC0 || (status & 0xF0) == 0xD0) ? 1 : 2, SEEK_CUR);
            }
        }
    }
    fclose(f);
    qsort(events, event_count, sizeof(MidiEvent), compare_events);
}

Note* convert_to_notes(uint16_t division, size_t *count, double *duration) {
    Note *notes = malloc(sizeof(Note) * event_count);
    size_t idx = 0;
    double cur_time = 0.0, micros_per_beat = 500000.0;
    uint32_t cur_tick = 0;

    /* Tracking aktiver Noten: [Channel][Note] -> StartTime. -1 = inaktiv */
    double active_times[16][128];
    int active_vels[16][128];
    for(int c=0; c<16; c++) for(int n=0; n<128; n++) active_times[c][n] = -1.0;

    for (size_t i = 0; i < event_count; i++) {
        MidiEvent e = events[i];
        if (e.abs_tick > cur_tick) {
            cur_time += (e.abs_tick - cur_tick) * (micros_per_beat / 1000000.0) / division;
            cur_tick = e.abs_tick;
        }
        if (e.type == EVENT_SET_TEMPO) micros_per_beat = e.tempo_micros;
        else if (e.type == EVENT_NOTE_ON) {
            if (active_times[e.channel][e.note] >= 0) { /* Retrigger */
                Note n = {active_times[e.channel][e.note], cur_time - active_times[e.channel][e.note],
                          e.note, active_vels[e.channel][e.note], e.channel, get_channel_color(e.channel)};
                if(n.duration > 0) notes[idx++] = n;
            }
            active_times[e.channel][e.note] = cur_time;
            active_vels[e.channel][e.note] = e.velocity;
        } else if (e.type == EVENT_NOTE_OFF) {
            if (active_times[e.channel][e.note] >= 0) {
                Note n = {active_times[e.channel][e.note], cur_time - active_times[e.channel][e.note],
                          e.note, active_vels[e.channel][e.note], e.channel, get_channel_color(e.channel)};
                active_times[e.channel][e.note] = -1.0;
                if(n.duration > 0) notes[idx++] = n;
            }
        }
    }
    *count = idx;
    *duration = cur_time + 1.0;
    return notes;
}

/* ==================================================================
   AUDIO-SYNTHESE (Memory Buffer)
   ================================================================== */
double midi_to_freq(int key) { return 440.0 * pow(2.0, (key - 69) / 12.0); }

void synthesize_to_ram(Note *notes, size_t count, double duration, AudioContext *ctx) {
    size_t total_samples = (size_t)(duration * SAMPLE_RATE);
    ctx->total_samples = total_samples;
    ctx->play_cursor = 0;

    /* Mix-Buffer in Float für Präzision */
    float *mix_buf = calloc(total_samples, sizeof(float));
    if(!mix_buf) { fprintf(stderr, "Out of Memory (Audio).\n"); exit(1); }

    printf("Synthetisiere %lu Noten (%.1f s)...\n", count, duration);

    double overtones[] = {1.0, 0.5, 0.3, 0.1};
    int num_overtones = 4;
    double release = 0.1;

    for (size_t i = 0; i < count; i++) {
        Note n = notes[i];
        int is_drum = (n.channel == 9);
        double freq = is_drum ? 100.0 : midi_to_freq(n.midi_key);
        double dur = is_drum ? 0.05 : n.duration;
        double amp = (n.velocity / 127.0) * 0.3;

        size_t start_s = (size_t)(n.start_time * SAMPLE_RATE);
        size_t len_s = (size_t)((dur + release) * SAMPLE_RATE);

        for (size_t t = 0; t < len_s && (start_s + t) < total_samples; t++) {
            double time = (double)t / SAMPLE_RATE;
            double val = 0.0;

            if (is_drum) val = sin(2 * PI * freq * time);
            else {
                for(int ov=0; ov<num_overtones; ov++) {
                    double h = freq * (ov + 1);
                    if (h < SAMPLE_RATE/2) val += overtones[ov] * sin(2 * PI * h * time);
                }
                val /= 1.9;
            }

            /* Envelope */
            double env = 1.0;
            if (time < 0.05) env = time / 0.05;
            else if (time > dur) env = 1.0 - ((time - dur) / release);
            if (env < 0) env = 0;

            mix_buf[start_s + t] += (float)(val * amp * env);
        }
    }

    /* Normalisierung und Konvertierung zu int16 */
    float max_val = 0.0f;
    for (size_t i = 0; i < total_samples; i++)
        if (fabs(mix_buf[i]) > max_val) max_val = fabsf(mix_buf[i]);

    float norm = (max_val > 0) ? (32000.0f / max_val) : 1.0f;
    if (norm > 32000.0f) norm = 32000.0f;

    ctx->pcm_buffer = malloc(total_samples * sizeof(int16_t));
    for (size_t i = 0; i < total_samples; i++) {
        int32_t v = (int32_t)(mix_buf[i] * norm);
        if(v > 32767) v = 32767;
        if(v < -32768) v = -32768;
        ctx->pcm_buffer[i] = (int16_t)v;
    }
    free(mix_buf);
}

/* ==================================================================
   AUDIO-GENERIERUNG (Timidity Pipe - RAW PCM Mode)
   ================================================================== */
void generate_audio_with_timidity(const char *midifile, AudioContext *ctx) {
    printf("Starte Timidity via Pipe (Raw PCM)...\n");

    char cmd[1024];
    /*
       Erklärung der Timidity-Flags:
       -Or  : Output Raw (Headerless PCM) -> Keine Seek-Fehler mehr!
       -s 44100 : Samplingrate festlegen (wichtig, da kein Header info liefert)
       -A160 : Lautstärke-Boost
       --preserve-silence : Stille am Anfang nicht abschneiden
       -o - : Ausgabe in stdout
    */
    snprintf(cmd, sizeof(cmd),
        "timidity \"%s\" -Or -s 44100 -A160 --preserve-silence -o -",
        midifile);

    FILE *pipe = popen(cmd, "r");
    if (!pipe) {
        fprintf(stderr, "FEHLER: Konnte Timidity nicht starten.\n");
        exit(1);
    }

    /* 1. Pipe-Stream in RAM lesen */
    size_t cap = 1024 * 1024;
    size_t size = 0;
    uint8_t *raw_data = malloc(cap);
    if (!raw_data) { fprintf(stderr, "Out of Memory.\n"); exit(1); }

    uint8_t buf[4096];
    size_t n;
    while ((n = fread(buf, 1, sizeof(buf), pipe)) > 0) {
        if (size + n > cap) {
            cap *= 2;
            raw_data = realloc(raw_data, cap);
            if (!raw_data) { fprintf(stderr, "Out of Memory.\n"); exit(1); }
        }
        memcpy(raw_data + size, buf, n);
        size += n;
    }
    pclose(pipe);

    if (size == 0) {
        fprintf(stderr, "FEHLER: Keine Daten von Timidity empfangen.\n");
        free(raw_data);
        exit(1);
    }

    /*
       2. Manuelle Konvertierung
       Da wir Raw Data haben, müssen wir SDL sagen, was das Format ist.
       Timidity Output Default: S16 (Signed 16 bit), System Endian, Stereo (2 Channels).
    */
    SDL_AudioCVT cvt;
    int src_channels = 2; /* Timidity erzeugt Stereo */
    int src_rate = 44100;

    /* Wir bauen einen Konverter: Timidity Stereo -> Unser Mono Format */
    if (SDL_BuildAudioCVT(&cvt, AUDIO_S16SYS, src_channels, src_rate,
            AUDIO_FORMAT, AUDIO_CHANNELS, SAMPLE_RATE) < 0)
    {
        fprintf(stderr, "FEHLER: Konnte Audio-Converter nicht bauen: %s\n", SDL_GetError());
        exit(1);
    }

    /* Puffer für Konvertierung vorbereiten */
    cvt.len = (int)size;
    /* SDL benötigt Puffer mit Puffergröße len * len_mult für In-Place-Konvertierung */
    cvt.buf = malloc(cvt.len * cvt.len_mult);

    /* Rohdaten in den Konverter-Puffer kopieren */
    memcpy(cvt.buf, raw_data, size);

    /* Konvertieren */
    SDL_ConvertAudio(&cvt);

    /* Daten in den AudioContext übernehmen */
    ctx->total_samples = cvt.len_cvt / sizeof(int16_t);
    ctx->pcm_buffer = (int16_t*)cvt.buf; /* Konvertierten Puffer übernehmen */
    ctx->play_cursor = 0;

    /* Cleanup */
    free(raw_data); /* Den ursprünglichen Roh-Puffer brauchen wir nicht mehr */

    printf("Audio von Timidity geladen (RAW): %lu Samples (%.2fs)\n",
           ctx->total_samples, (double)ctx->total_samples / SAMPLE_RATE);
}

/* ==================================================================
   SDL-CALLBACK UND VISUALISIERUNG
   ================================================================== */

void audio_callback(void *userdata, Uint8 *stream, int len) {
    AudioContext *ctx = (AudioContext *)userdata;
    int samples_needed = len / sizeof(int16_t);
    int samples_left = ctx->total_samples - ctx->play_cursor;

    if (samples_left <= 0) {
        memset(stream, 0, len);
        return;
    }

    int to_copy = (samples_needed < samples_left) ? samples_needed : samples_left;
    memcpy(stream, &ctx->pcm_buffer[ctx->play_cursor], to_copy * sizeof(int16_t));

    ctx->play_cursor += to_copy;

    if (to_copy < samples_needed) {
        memset(stream + to_copy * sizeof(int16_t), 0, (samples_needed - to_copy) * sizeof(int16_t));
    }
}

/*
 * Hilfsfunktionen für Rechtecke mit abgerundeten Ecken
 */

/* Flags für die abgerundeten Ecken */
#define CORNER_TL 1  /* Oben Links */
#define CORNER_TR 2  /* Oben Rechts */
#define CORNER_BL 4  /* Unten Links */
#define CORNER_BR 8  /* Unten Rechts */
#define CORNER_ALL 15

/*
 * Hilfsfunktion: Zeichnet einen ausgefüllten Viertelkreis.
 * cx, cy: Mittelpunkt des Kreises (nicht der Ecke!)
 * r: Radius
 * quadrant: 0=TL, 1=TR, 2=BL, 3=BR
 */
void FillQuarterCircle(SDL_Renderer *renderer, int cx, int cy, int r, int quadrant) {
    for (int dy = 0; dy <= r; dy++) {
        /* Pythagoras: x = sqrt(r^2 - dy^2) */
        int dx = (int)sqrt(r * r - dy * dy);

        /* Wir zeichnen horizontale Linien für jeden Y-Schritt */
        if (quadrant == 0) { /* Oben Links */
            SDL_RenderDrawLine(renderer, cx - dx, cy - dy, cx, cy - dy);
        } else if (quadrant == 1) { /* Oben Rechts */
            SDL_RenderDrawLine(renderer, cx, cy - dy, cx + dx, cy - dy);
        } else if (quadrant == 2) { /* Unten Links */
            SDL_RenderDrawLine(renderer, cx - dx, cy + dy, cx, cy + dy);
        } else if (quadrant == 3) { /* Unten Rechts */
            SDL_RenderDrawLine(renderer, cx, cy + dy, cx + dx, cy + dy);
        }
    }
}

/*
 * Hauptfunktion: Zeichnet ein Rechteck mit wählbaren runden Ecken.
 */
void RenderFillRoundedRect(SDL_Renderer *renderer, int x, int y, int w, int h, int r, int corners) {
    /* Sicherheitscheck: Radius darf nicht größer als die halbe Breite/Höhe sein */
    if (r * 2 > w) r = w / 2;
    if (r * 2 > h) r = h / 2;

    /*
     * Strategie: Wir zeichnen ein Kreuz aus zwei Rechtecken,
     * die den Großteil der Fläche füllen, und behandeln die 4 Ecken separat.
     */

    /* 1. Vertikaler Mittelstreifen (deckt oben und unten die geraden Kanten ab) */
    SDL_Rect vRect = {x + r, y, w - 2 * r, h};
    SDL_RenderFillRect(renderer, &vRect);

    /* 2. Linker und rechter Seitenstreifen (zwischen den Ecken) */
    SDL_Rect lRect = {x, y + r, r, h - 2 * r};
    SDL_Rect rRect = {x + w - r, y + r, r, h - 2 * r};
    SDL_RenderFillRect(renderer, &lRect);
    SDL_RenderFillRect(renderer, &rRect);

    /* 3. Die 4 Ecken bearbeiten */

    /* Oben Links */
    if (corners & CORNER_TL) {
        FillQuarterCircle(renderer, x + r, y + r, r, 0);
    } else {
        SDL_Rect c = {x, y, r, r}; SDL_RenderFillRect(renderer, &c);
    }

    /* Oben Rechts */
    if (corners & CORNER_TR) {
        FillQuarterCircle(renderer, x + w - r - 1, y + r, r, 1);
    } else {
        SDL_Rect c = {x + w - r, y, r, r}; SDL_RenderFillRect(renderer, &c);
    }

    /* Unten Links */
    if (corners & CORNER_BL) {
        FillQuarterCircle(renderer, x + r, y + h - r - 1, r, 2);
    } else {
        SDL_Rect c = {x, y + h - r, r, r}; SDL_RenderFillRect(renderer, &c);
    }

    /* Unten Rechts */
    if (corners & CORNER_BR) {
        FillQuarterCircle(renderer, x + w - r - 1, y + h - r - 1, r, 3);
    } else {
        SDL_Rect c = {x + w - r, y + h - r, r, r}; SDL_RenderFillRect(renderer, &c);
    }
}

/* Vergleichsfunktion für qsort: Sortieren nach Startzeit */
int compare_notes_start(const void *a, const void *b) {
    const Note *na = (const Note *)a;
    const Note *nb = (const Note *)b;
    if (na->start_time < nb->start_time) return -1;
    if (na->start_time > nb->start_time) return 1;
    return 0;
}

int main(int argc, char **argv) {
    char *midifile = NULL;
    int use_timidity = 0;

    /* Argumente parsen */
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-tm") == 0) {
            use_timidity = 1;
        } else if (argv[i][0] != '-') {
            midifile = argv[i];
        }
    }

    if (!midifile) {
        printf("Verwendung: %s <datei.mid> [-tm]\n", argv[0]);
        printf("  -tm : Benutze 'timidity' für bessere Audioqualität\n");
        return 1;
    }

    /* 1. MIDI parsen */
    uint16_t division;
    parse_midi(midifile, &division);
    size_t note_count;
    double duration;
    Note *notes = convert_to_notes(division, &note_count, &duration);
    if (!notes) { printf("Keine Noten gefunden.\n"); return 1; }

    /* Array nach Startzeit sortieren, damit das break bei
     * start > limit im Render-Loop korrekt funktioniert;
     * andernfalls kann es passieren, dass der Balken ein wenig zu spät
     * auftaucht. Nämlich wird in der Funktion convert_to_notes
     * eine Note erst dann in das Array geschrieben, wenn das
     * Note-Off-Event im MIDI-Stream auftaucht (also wenn die Note zu
     * Ende ist). Dadurch ist die Notenliste effektiv nach Endzeitpunkt
     * sortiert, nicht nach Startzeitpunkt. */
    qsort(notes, note_count, sizeof(Note), compare_notes_start);

    /* 2. Audio synthetisieren */
    AudioContext ctx;
    if (use_timidity) {
        memset(&ctx, 0, sizeof(ctx)); /* Sicherstellen, dass alles 0 ist */
        generate_audio_with_timidity(midifile, &ctx);
    } else {
        synthesize_to_ram(notes, note_count, duration, &ctx);
    }


    /* 3. SDL Init */
    if (SDL_Init(SDL_INIT_VIDEO | SDL_INIT_AUDIO) < 0) {
        fprintf(stderr, "SDL Init Fehler: %s\n", SDL_GetError());
        return 1;
    }

    SDL_Window *win = SDL_CreateWindow("Mivi",
        SDL_WINDOWPOS_CENTERED, SDL_WINDOWPOS_CENTERED,
        WINDOW_WIDTH, WINDOW_HEIGHT,
        SDL_WINDOW_SHOWN | SDL_WINDOW_RESIZABLE);
    SDL_Renderer *rend = SDL_CreateRenderer(win, -1,
        SDL_RENDERER_ACCELERATED | SDL_RENDERER_PRESENTVSYNC);

    SDL_AudioSpec want, have;
    memset(&want, 0, sizeof(want));
    want.freq = SAMPLE_RATE;
    want.format = AUDIO_FORMAT;
    want.channels = AUDIO_CHANNELS;
    want.samples = 2048;
    want.callback = audio_callback;
    want.userdata = &ctx;

    SDL_AudioDeviceID dev = SDL_OpenAudioDevice(NULL, 0, &want, &have, 0);
    if (dev == 0) {
        fprintf(stderr, "Audio Device Fehler: %s\n", SDL_GetError());
        return 1;
    }

    SDL_PauseAudioDevice(dev, 0); /* Start Audio */

    /* 4. Main Loop */
    int running = 1;
    SDL_Event ev;

    /* Aktive Tasten merken für Visualisierung */
    int active_keys[128];
    SDL_Color active_colors[128];

    /* ZEITMESSUNG: Wir nutzen den High-Res Timer für flüssige Grafik */
    Uint64 start_counter = SDL_GetPerformanceCounter();
    Uint64 frequency = SDL_GetPerformanceFrequency();

    /* Timidity liefert manchmal etwas mehr oder weniger Audio als die
     * MIDI Zeit berechnet. Wir nutzen die Länge des Audiobuffers als
     * Obergrenze für den Loop. */
    double actual_audio_duration = (double)ctx.total_samples / SAMPLE_RATE;
    double loop_limit = (actual_audio_duration > duration) ? actual_audio_duration : duration;

    while (running) {
        while (SDL_PollEvent(&ev)) {
            if (ev.type == SDL_QUIT) running = 0;
        }

        /* Zeit berechnen */
        Uint64 current_counter = SDL_GetPerformanceCounter();
        double current_time = (double)(current_counter - start_counter) / frequency;
        if (use_timidity) {
            if (current_time > loop_limit + 1.5) running = 0;
        } else {
            if (current_time > duration + 1.0) running = 0; /* Auto-Quit am Ende */
        }

        int w, h;
        SDL_GetWindowSize(win, &w, &h);
        int note_area_h = h - KEYBOARD_HEIGHT;

        /* BERECHNUNG: Wie viele Sekunden passen vertikal auf den Schirm? */
        /* Wir addieren einen Puffer (z.B. 1.0s), damit Noten sanft reinkommen */
        double visible_time_range = (double)note_area_h / PIXELS_PER_SECOND;
        double lookahead_time = visible_time_range + 1.0;

        /* Zeichnen */
        SDL_SetRenderDrawColor(rend, 30, 30, 35, 255);
        SDL_RenderClear(rend);

        /* Tasten Status Reset */
        for(int i=0; i<128; i++) active_keys[i] = 0;

        /* NOTEN (Falling Blocks) */
        for (size_t i = 0; i < note_count; i++) {
            Note *n = &notes[i];

            /* Clipping: Nur Noten zeichnen, die im sichtbaren Bereich sind */
            /* Note ist sichtbar wenn: (start <= t + 5.0) UND (end >= t - 1.0) */
            if (n->start_time > current_time + lookahead_time) break;

            if ((n->start_time + n->duration) < current_time - 1.0) continue;

            float time_diff = (float)(n->start_time - current_time);
            float note_y = note_area_h - (time_diff * PIXELS_PER_SECOND);
            float note_h = (float)(n->duration * PIXELS_PER_SECOND);
            float draw_y = note_y - note_h;

            /* Check ob Note "aktiv" ist (wird gerade gespielt) */
            int is_playing = (current_time >= n->start_time &&
                current_time < (n->start_time + n->duration));
            if (is_playing) {
                active_keys[n->midi_key] = 1;
                active_colors[n->midi_key] = n->color;
            }

            if (n->midi_key >= MIN_MIDI && n->midi_key <= MAX_MIDI) {
                float x, width;
                int is_bk;
                get_key_geometry(n->midi_key, (float)w, &x, &width, &is_bk);

                /* Farbe aufhellen wenn aktiv */
                SDL_Color c = n->color;
                if(is_playing) {
                    c.r = (c.r > 195) ? 255 : c.r + 60;
                    c.g = (c.g > 195) ? 255 : c.g + 60;
                    c.b = (c.b > 195) ? 255 : c.b + 60;
                }

                SDL_SetRenderDrawColor(rend, c.r, c.g, c.b, 255);
                RenderFillRoundedRect(rend, (int)x + 1, (int)draw_y,
                    (int)width - 2, (int)note_h, 4, CORNER_ALL);
            }
        }

        /* KLAVIATUR */
        /* 1. Weiße Tasten */
        for (int m = MIN_MIDI; m <= MAX_MIDI; m++) {
            if (!is_black_key(m)) {
                float x, width; int bk;
                get_key_geometry(m, (float)w, &x, &width, &bk);

                SDL_Color c = {220, 220, 220, 255};
                if (active_keys[m]) {
                    /* Mix mit Notenfarbe */
                    c.r = (active_colors[m].r + 255) / 2;
                    c.g = (active_colors[m].g + 255) / 2;
                    c.b = (active_colors[m].b + 255) / 2;
                }

                SDL_SetRenderDrawColor(rend, c.r, c.g, c.b, 255);
                RenderFillRoundedRect(rend, (int)x, note_area_h,
                    (int)width - 1, KEYBOARD_HEIGHT, 5,
                    CORNER_BL | CORNER_BR);
            }
        }
        /* 2. Schwarze Tasten (oben drüber) */
        for (int m = MIN_MIDI; m <= MAX_MIDI; m++) {
            if (is_black_key(m)) {
                float x, width; int bk;
                get_key_geometry(m, (float)w, &x, &width, &bk);

                SDL_Color c = {20, 20, 20, 255};
                if (active_keys[m]) {
                    c.r = (active_colors[m].r + 100) / 2;
                    c.g = (active_colors[m].g + 100) / 2;
                    c.b = (active_colors[m].b + 100) / 2;
                }

                SDL_SetRenderDrawColor(rend, c.r, c.g, c.b, 255);
                RenderFillRoundedRect(rend,
                    (int)x, note_area_h, (int)width,
                    (int)(KEYBOARD_HEIGHT * 0.65), 3,
                    CORNER_BL | CORNER_BR);
            }
        }

        SDL_RenderPresent(rend);
    }

    /* Cleanup */
    SDL_CloseAudioDevice(dev);
    SDL_DestroyRenderer(rend);
    SDL_DestroyWindow(win);
    SDL_Quit();
    free(ctx.pcm_buffer);
    free(notes);
    if(events) free(events);

    return 0;
}
