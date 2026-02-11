// =====================================================================
// ZEICHNEN (Klavier-Akkolade, horizontal)
// =====================================================================

use sdl2::pixels::Color;
use sdl2::render::Canvas;
use sdl2::video::Window;
use sdl2::rect::Rect;
use crate::{Env, RenderView, Note};
use crate::PIXELS_PER_SECOND;

#[cfg(feature = "image")]
use sdl2::{
    image::{LoadTexture, InitFlag},
    render::{Texture, TextureCreator},
    video::WindowContext
};

// =====================================================================
// VISUALISIERUNGS-PARAMETER (Grand Staff)
// =====================================================================
const STAFF_LINE_THICKNESS: u32 = 2;       // Dicke der Notenlinien
const STAFF_LINE_SPACING: i32 = 14;        // Abstand zwischen Linien (halbe Notenhöhe)
const STAFF_COLOR: Color = Color::RGB(60, 60, 60);

const PLAYHEAD_X: i32 = 200;               // X-Position der "Jetzt"-Linie
const PLAYHEAD_WIDTH: u32 = 3;             // Dicke der "Jetzt"-Linie
const PLAYHEAD_COLOR: Color = Color::RGB(160, 160, 160);

const NOTE_HEAD_WIDTH: i32 = 18;           // Breite des Notenkopfs
const NOTE_HEAD_HEIGHT: i32 = 14;          // Höhe des Notenkopfs (meist == Spacing)
const NOTE_TRAIL_ALPHA: u8 = 100;          // Transparenz der Schweif-Spur (0-255)

// Konfiguration für Liniensystem und Hilfslinien
const SHOW_BASS_STAFF: bool = true; // "false" blendet das untere System aus
const LEDGER_LINE_WIDTH: u32 = 26;   // Etwas breiter als der Notenkopf (18)

pub struct ImageSystem {
    #[cfg(feature = "image")]
    texture_creator: TextureCreator<WindowContext>
}

impl ImageSystem {
    // Image-Subsystem starten
    #[cfg(feature = "image")]
    pub fn init(env: &Env) -> Self {
        let _image_context = sdl2::image::init(InitFlag::PNG | InitFlag::JPG).unwrap();
        let texture_creator = env.canvas.texture_creator();
        Self {texture_creator}
    }

    #[cfg(not(feature = "image"))]
    pub fn init(_env: &Env) -> Self {
        Self {}
    }
}

#[cfg(feature = "image")]
pub struct Textures<'a> {
    treble_key: Texture<'a>,
    bass_key: Texture<'a>,
    sharp: Texture<'a>,
    flat: Texture<'a>,
    natural: Texture<'a>,
    head: Texture<'a>
}

#[cfg(feature = "image")]
impl<'a> Textures<'a> {
    const SHARP_W: u32 = 14;
    const SHARP_H: u32 = 38;
    const FLAT_W: u32 = 12;
    const FLAT_H: u32 = 33;
    const NATURAL_W: u32 = 9;
    const NATURAL_H: u32 = 37;

    pub fn load(img_sys: &'a ImageSystem) -> Self {
        // Den Font "Bravura" in Inkscape verwenden. Die Glyphen
        // 𝄞, 𝄢 jeweils als PNG-Datei in der genutzten Auflösung
        // mit transparentem Hintergrund exportieren.
        const  TREBLE_PNG_BYTES: &[u8] = include_bytes!("../assets/treble-clef.png");
        const    BASS_PNG_BYTES: &[u8] = include_bytes!("../assets/bass-clef.png");

        // Die Glyphen ♯, ♭, ♮.
        const   SHARP_PNG_BYTES: &[u8] = include_bytes!("../assets/sharp.png");
        const    FLAT_PNG_BYTES: &[u8] = include_bytes!("../assets/flat.png");
        const NATURAL_PNG_BYTES: &[u8] = include_bytes!("../assets/natural.png");

        // Die Glyphe 𝅝 (ganze Note) ausfüllen und stauchen.
        const    HEAD_PNG_BYTES: &[u8] = include_bytes!("../assets/notehead.png");

        let treble_key = img_sys.texture_creator.load_texture_bytes(TREBLE_PNG_BYTES)
            .expect("Konnte Treble-PNG nicht laden");
        let bass_key = img_sys.texture_creator.load_texture_bytes(BASS_PNG_BYTES)
            .expect("Konnte Bass-PNG nicht laden");
        let sharp = img_sys.texture_creator.load_texture_bytes(SHARP_PNG_BYTES)
            .expect("Konnte Sharp-PNG nicht laden");
        let flat = img_sys.texture_creator.load_texture_bytes(FLAT_PNG_BYTES)
            .expect("Konnte Flat-PNG nicht laden");
        let natural = img_sys.texture_creator.load_texture_bytes(NATURAL_PNG_BYTES)
            .expect("Konnte Natural-PNG nicht laden");
        let head = img_sys.texture_creator.load_texture_bytes(HEAD_PNG_BYTES)
            .expect("Konnte Natural-PNG nicht laden");
        Self {treble_key, bass_key, sharp, flat, natural, head}
    }
}

#[cfg(not(feature = "image"))]
pub struct Textures {}

#[cfg(not(feature = "image"))]
impl Textures {
    pub fn load(_img_sys: &ImageSystem) -> Self {
        Self {}
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum Accidental {
    None,    // Kein Vorzeichen an der Note nötig
    Natural, // ♮ Auflösungszeichen
    Sharp,   // # Kreuz
    Flat,    // b Be
}

fn is_flat_root(root: i32) -> bool {
    // F(5), Bes(10), Es(3), As(8), Des(1), Ges(6)
    matches!(root, 5 | 10 | 3 | 8 | 1 | 6)
}

fn determine_accidental(midi_key: i32, root: i32) -> Accidental {
    let n = midi_key.rem_euclid(12);
    let major_intervals = [0, 2, 4, 5, 7, 9, 11];

    for &interval in &major_intervals {
        if (root + interval) % 12 == n {
            return Accidental::None;
        }
    }

    // Ist der Ton physikalisch eine weiße Taste (C, D, E, F, G, A, B)?
    // Wenn ja, aber nicht in der Skala (siehe oben), muss er aufgelöst werden.
    let is_white_key = matches!(n, 0 | 2 | 4 | 5 | 7 | 9 | 11);

    if is_white_key {
        return Accidental::Natural;
    }

    // Chromatische Anpassung (# oder b)
    // Der Ton ist eine schwarze Taste und nicht in der Skala.
    // Entscheidung anhand des Quintenzirkels (Flat Roots vs Sharp Roots).
    if is_flat_root(root) {
        Accidental::Flat
    } else {
        Accidental::Sharp
    }
}

#[allow(dead_code)]
pub struct KeyInfo(pub i32, pub u8);

impl KeyInfo {
    pub fn from_name(key: &str) -> KeyInfo {
        match key {
            "C" | "a" | "Am"  => KeyInfo(0, 0),
            "D" | "b" | "Bm" | "h" | "Hm" => KeyInfo(2, 2),
            "E" | "c#" | "cis" | "C#m" => KeyInfo(4, 4),
            "G" | "e" | "Em" => KeyInfo(7, 1),
            "A" | "f#" | "fis" | "F#m" => KeyInfo(9, 3),
            "B" | "H" => KeyInfo(11, 5),
            "F" | "d" | "Dm" => KeyInfo(5, 1),
            "Bes" | "Bb" | "g" | "Gm" => KeyInfo(10, 2),
            "Es" | "Eb" | "c" | "Cm" => KeyInfo(3, 3),
            "As" | "Ab" | "f" | "Fm" => KeyInfo(8, 4),
            "Des" | "Db" | "bes" | "bb" | "Besm" | "Bbm" => KeyInfo(1, 5),
            "Ges" | "Gb" | "es" | "eb" | "Esm" | "Ebm" => KeyInfo(6, 6),
            _ => unimplemented!()
        }
    }
}

// Berechnet den vertikalen "Step" im Notensystem relativ zu C4 (Midi 60)
// C4 = 0, D4 = 1, E4 = 2 ...
fn get_staff_step(midi: i32, flat: bool) -> i32 {
    let octave = (midi / 12) - 1; // MIDI Oktave (-1 für interne Berechnung)
    let note_in_octave = midi % 12;

    // Mapping: Semitone Index -> Staff Step Index (C=0, D=1, E=2, F=3, G=4, A=5, B=6)
    // Schwarze Tasten (Sharps) landen auf der gleichen Höhe wie die Note darunter
    let step_in_octave = if flat {
        match note_in_octave {
            0 => 0,      // C
            1 | 2 => 1,  // Db, D
            3 | 4 => 2,  // Eb, E
            5 => 3,      // F
            6 | 7 => 4,  // Gb, G
            8 | 9 => 5,  // Ab, A
            10 | 11 => 6,// Bb, B
            _ => 0
        }
    } else {
        match note_in_octave {
            0 | 1 => 0, // C, C#
            2 | 3 => 1, // D, D#
            4 => 2,     // E
            5 | 6 => 3, // F, F#
            7 | 8 => 4, // G, G#
            9 | 10 => 5,// A, A#
            11 => 6,    // B
            _ => 0
        }
    };

    (octave * 7) + step_in_octave
}

#[cfg(feature = "image")]
fn render_accidentals(env: &mut Env, textures: &mut Textures, x: i32, y: i32, flat: bool) {
    const X_SCALE: i32 = 100;
    const Y_SCALE: i32 = 100;
    const XS_SPACE: i32 = 1500 / X_SCALE;
    const YS_F: i32 = 0 / Y_SCALE;
    const YS_C: i32 = 2100 / Y_SCALE;
    const YS_G: i32 = -700 / Y_SCALE;
    const YS_D: i32 = 1400 / Y_SCALE;
    const YS_A: i32 = 3500 / Y_SCALE;
    const YS: [i32; 5] = [YS_F, YS_C, YS_G, YS_D, YS_A];

    const XF_SPACE: i32 = 1300 / X_SCALE;
    const YF_SHIFT: i32 = -5;
    const YF_H: i32 = 2800 / Y_SCALE;
    const YF_E: i32 = 700 / Y_SCALE;
    const YF_A: i32 = 3500 / Y_SCALE;
    const YF_D: i32 = 1400 / Y_SCALE;
    const YF_G: i32 = 4200 / Y_SCALE;
    const YF_C: i32 = 2100 / Y_SCALE;
    const YF: [i32; 6] = [YF_H, YF_E, YF_A, YF_D, YF_G, YF_C];

    if flat {
        textures.flat.set_color_mod(0, 0, 0);
        for i in 0..env.root_key.1 {
            let dx = i32::from(i)*XF_SPACE;
            let dy = YF_SHIFT + YF[usize::from(i)];
            let rect_flat = Rect::new(x + dx, y + dy, Textures::FLAT_W, Textures::FLAT_H);
            env.canvas.copy(&textures.flat, None, rect_flat).unwrap();
        }
    } else {
        textures.sharp.set_color_mod(0, 0, 0);
        for i in 0..env.root_key.1 {
            let dx = i32::from(i)*XS_SPACE;
            let dy = YS[usize::from(i)];
            let rect_sharp = Rect::new(x + dx, y + dy, Textures::SHARP_W, Textures::SHARP_H);
            env.canvas.copy(&textures.sharp, None, rect_sharp).unwrap();
        }
    }
}

#[cfg(feature = "image")]
fn render_keys(env: &mut Env, textures: &mut Textures, center_y: i32, flat: bool) {
    // -----------------------------------------------------------------
    // 2. Notenschlüssel (Assets oder Dummies)
    // -----------------------------------------------------------------

    // --- KONFIGURATION FÜR FEINTUNING ---
    // Violinschlüssel:
    // Ein Violinschlüssel ist ca. 7.5 Linienabstände hoch (vom unteren Haken bis zur Spitze).
    // Bei Spacing 14px * 8 = ca. 112px visuelle Höhe.
    // Wir nehmen etwas mehr für Padding im Bild.
    let treble_h = 96;
    // Aspect Ratio des Bildes beachten! Wenn das PNG 100x200 ist, sollte width = height / 2 sein.
    // Angenommen, das PNG ist schlank (ca 1:2.5):
    let treble_w = 37;

    // Offset Y: Verschiebt den Schlüssel nach oben/unten.
    // Ziel: Die Spirale (Kringel) muss sich um die G-Linie (2. Linie von unten) drehen.
    let treble_offset_y = -11;

    // Bassschlüssel:
    let bass_h = 43;
    let bass_w = 38;

    // Ziel: Die zwei Punkte müssen die F-Linie (2. Linie von oben im Bass-System) umschließen.
    let bass_offset_y = 8;

    // --- BERECHNUNG & ZEICHNEN ---

    // Treble Center ist G4 (Step 4).
    // Wir berechnen die Y-Position der G-Linie:
    let g4_y = center_y - (4 * STAFF_LINE_SPACING / 2);

    // Wir zeichnen das Bild zentriert um diese Linie und addieren den Offset
    let rect_treble = Rect::new(
        20,
        g4_y - (treble_h / 2) + treble_offset_y,
        treble_w,
        treble_h as u32
    );

    // Textur kopieren (das 'None' bedeutet: ganzes Quellbild nutzen)
    env.canvas.copy(&textures.treble_key, None, rect_treble).unwrap();

    const X_ACCI: i32 = 68;
    if env.root_key.0 != 0 {
        render_accidentals(env, textures, X_ACCI, g4_y - 60, flat);
    }

    if SHOW_BASS_STAFF {
        // Bass Reference ist F3 (Step -4)
        let f3_y = center_y - (-4 * STAFF_LINE_SPACING / 2);

        let rect_bass = Rect::new(
            20,
            f3_y - (bass_h / 2) + bass_offset_y,
            bass_w,
            bass_h as u32
        );

        env.canvas.copy(&textures.bass_key, None, rect_bass).unwrap();

        if env.root_key.0 != 0 {
            render_accidentals(env, textures, X_ACCI, f3_y - 18, flat);
        }
    }
}

#[cfg(not(feature = "image"))]
fn render_keys(_env: &mut Env, _textures: &Textures, _center_y: i32, _flat: bool) {
}

#[allow(dead_code)]
pub struct BufferedHead {
    x: i32, y: i32, midi_key: i32,
    color: Color
}

// Ein generischer Ringpuffer fester Größe auf dem Stack.
// T muss Copy sein, damit wir das Array einfach initialisieren können (Option::None).
pub struct StackRingBuffer<T, const N: usize> {
    buffer: [Option<T>; N],
    head: usize, // Lese-Position
    tail: usize, // Schreib-Position
    len: usize
}

impl<T, const N: usize> StackRingBuffer<T, N> {
    pub fn new() -> Self {
        const {assert!(N != 0);}
        Self {buffer: [const {None}; N], head: 0, tail: 0, len: 0}
    }

    /// Fügt ein Element hinzu.
    /// Wenn der Puffer voll ist, wird das älteste Element entfernt und zurückgegeben (Overflow).
    /// Wenn Platz ist, wird None zurückgegeben.
    pub fn push_overflow(&mut self, item: T) -> Option<T> {
        let mut overflow_item = None;

        if self.len == N {
            // Puffer voll: Wir müssen das Älteste rauswerfen (lesen)
            overflow_item = self.buffer[self.head].take();
            self.head = (self.head + 1) % N;
            self.len -= 1;
        }

        // Neues Element schreiben
        self.buffer[self.tail] = Some(item);
        self.tail = (self.tail + 1) % N;
        self.len += 1;

        overflow_item
    }

    /// Holt das nächste Element (für das Leeren am Ende)
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            return None;
        }
        let item = self.buffer[self.head].take();
        self.head = (self.head + 1) % N;
        self.len -= 1;
        item
    }
}

fn render_note(env: &mut Env, head: &BufferedHead,
  #[allow(unused_variables)]
  textures: &mut Textures
) {
    #[allow(unused_variables)]
    let accidental = determine_accidental(head.midi_key, env.root_key.0);
    #[cfg(feature = "image")] {
        let Color {r, g, b, ..} = head.color;
        if accidental != Accidental::None {
            if accidental == Accidental::Sharp {
                textures.sharp.set_color_mod(r, g, b);
                let rect_sharp = Rect::new(head.x - 16, head.y - 11,
                    Textures::SHARP_W, Textures::SHARP_H);
                env.canvas.copy(&textures.sharp, None, rect_sharp).unwrap();
            } else if accidental == Accidental::Flat {
                textures.flat.set_color_mod(r, g, b);
                let rect_flat = Rect::new(head.x - 15, head.y - 16,
                    Textures::FLAT_W, Textures::FLAT_H);
                env.canvas.copy(&textures.flat, None, rect_flat).unwrap();
            } else {
                textures.natural.set_color_mod(r, g, b);
                let rect_natural = Rect::new(head.x - 12, head.y - 11,
                    Textures::NATURAL_W, Textures::NATURAL_H);
                env.canvas.copy(&textures.natural, None, rect_natural).unwrap();
            }
        }
        textures.head.set_color_mod(r, g, b);
        let rect_head = Rect::new(head.x + 1, head.y,
            16, 15);
        env.canvas.copy(&textures.head, None, rect_head).unwrap();
    }
    #[cfg(not(feature = "image"))] {
        env.canvas.set_draw_color(head.color);
        crate::render_fill_rounded_rect(
            &mut env.canvas, head.x, head.y,
            NOTE_HEAD_WIDTH, NOTE_HEAD_HEIGHT,
            6, // Radius für Rundung
            crate::CORNER_ALL
        ).unwrap_or(());
    }
}

pub fn render_staff(env: &mut Env, view: &RenderView,
    notes: &Vec<Note>, current_time: f64, textures: &mut Textures,
    vis_offset: i32
) {
    // Hintergrund
    view.begin(&mut env.canvas, Color::RGB(255, 255, 255));

    // Blend Mode für Transparenz aktivieren (wichtig für die "seichte Spur")
    env.canvas.set_blend_mode(sdl2::render::BlendMode::Blend);

    let w = view.width();
    let h = view.height();

    let flat = is_flat_root(env.root_key.0);

    // Referenzpunkt: Mittleres C (C4, Midi 60) liegt vertikal in der Mitte des Fensters
    let center_y = h / 2;

    // Berechnung des "Steps" für C4
    let c4_step = get_staff_step(60, false);

    // -----------------------------------------------------------------
    // Playhead (Jetzt-Linie)
    // -----------------------------------------------------------------
    env.canvas.set_draw_color(PLAYHEAD_COLOR);
    env.canvas.fill_rect(Rect::new(
        PLAYHEAD_X,
        0,
        PLAYHEAD_WIDTH,
        h as u32
    )).unwrap_or(());

    // -----------------------------------------------------------------
    // Notenlinien (Staff) zeichnen
    // -----------------------------------------------------------------
    env.canvas.set_draw_color(STAFF_COLOR);

    // Wir zeichnen Linien relativ zum Center Y.
    // Eine Linie ist 1 Step hoch (bzw. 2 Steps Abstand zwischen Linien, da Linie+Zwischenraum).
    // Standard-Abstand im Notensystem ist meist 2 Steps (Linie auf E, Linie auf G -> Differenz 2).

    // Funktion zum Zeichnen einer Linie bei einem bestimmten Step
    let draw_staff_line = |canvas: &mut Canvas<Window>, step_rel_c4: i32| -> Result<(), String> {
        // Y wächst nach unten. Höherer Step = kleineres Y.
        // step * (STAFF_LINE_SPACING / 2)

        let y = center_y - (step_rel_c4 * STAFF_LINE_SPACING / 2);
        let r = Rect::new(0, y, w as u32, STAFF_LINE_THICKNESS);
        canvas.fill_rect(r)?;

        Ok(())
    };

    // Violinschlüssel (Treble): E4, G4, B4, D5, F5
    // Steps relativ zu C4 (0): E4=+2, G4=+4, B4=+6, D5=+8, F5=+10
    let treble_steps = [2, 4, 6, 8, 10];
    for s in treble_steps.iter() { draw_staff_line(&mut env.canvas, *s).unwrap_or(()); }

    // Bassschlüssel: G2, B2, D3, F3, A3
    // C4 ist Step 0. C3 ist Step -7.
    // G2 = -17 + 4 = -13 ? Nein:
    // C3 = -7. B2 = -8, A2 = -9, G2 = -10.
    // Bass Steps relativ zu C4: A3=-2, F3=-4, D3=-6, B2=-8, G2=-10
    if SHOW_BASS_STAFF {
        let bass_steps = [-2, -4, -6, -8, -10];
        for s in bass_steps.iter() { draw_staff_line(&mut env.canvas, *s).unwrap_or(()); }
    }

    // -----------------------------------------------------------------
    // Noten zeichnen (Horizontal Scrolling)
    // -----------------------------------------------------------------
    // Visible Time Range berechnen wir neu für Horizontal
    // Pixel pro Sekunde horizontal
    let visible_duration_seconds = (w as f64 - PLAYHEAD_X as f64) / PIXELS_PER_SECOND;

    // Wir schauen etwas in die Vergangenheit (links vom Playhead) und in die Zukunft (rechts)
    let past_time_limit = PLAYHEAD_X as f64 / PIXELS_PER_SECOND;

    for n in notes {
        // Optimierung: Nur Noten zeichnen, die im Fenster sichtbar sind
        // Ende der Note muss > (current_time - past) sein
        // Start der Note muss < (current_time + future) sein
        if n.start_time > current_time + visible_duration_seconds + 2.0 { break; } // +2.0 Puffer
        if n.start_time + n.duration < current_time - past_time_limit - 1.0 { continue; }

        // X-Position berechnen
        // x = PLAYHEAD + (start - now) * speed
        let x_start = PLAYHEAD_X as f64 + (n.start_time - current_time) * PIXELS_PER_SECOND;
        let note_width_px = n.duration * PIXELS_PER_SECOND;

        let display_key = n.midi_key + vis_offset;

        // Y-Position berechnen (Staff Mapping)
        let step = get_staff_step(display_key, flat);
        let rel_step = step - c4_step;
        let y_pos = center_y - (rel_step * STAFF_LINE_SPACING / 2);

        // Farbe bestimmen
        let mut color = if env.black_notes {
            Color {r: 0, g: 0, b: 0, a: 0}
        } else {
            n.color
        };

        // Wenn Note gerade aktiv ist (unter dem Playhead), leicht aufhellen
        let is_active = x_start <= PLAYHEAD_X as f64 && (x_start + note_width_px) >= PLAYHEAD_X as f64;
        if is_active {
            let color_shift = if env.black_notes {120} else {50};
            color.r = color.r.saturating_add(color_shift);
            color.g = color.g.saturating_add(color_shift);
            color.b = color.b.saturating_add(color_shift);
        }

        // A) Die Spur (Trail) - Länge der Note
        let trail_rect = Rect::new(
            x_start as i32 + 3,
            y_pos - (NOTE_HEAD_HEIGHT / 4), // Spur ist etwas dünner als der Kopf
            (note_width_px as u32).saturating_sub(3),
            (NOTE_HEAD_HEIGHT / 2) as u32
        );

        env.canvas.set_draw_color(Color::RGBA(color.r, color.g, color.b, NOTE_TRAIL_ALPHA));
        env.canvas.fill_rect(trail_rect).unwrap_or(());

        // B) Der Notenkopf (Am Anfang der Note, rechtsbündig zur Spur sozusagen,
        // da die Musik nach links fließt, ist der Anfang der Note links)
        // Wir zeichnen den Kopf bei x_start.

        // Notenkopf als abgerundetes Rechteck (sieht fast wie Ellipse aus bei passenden Maßen)
        // Zentrieren um (x_start, y_pos)
        // Da Koordinaten Top-Left sind:
        let head_x = x_start as i32; // - (NOTE_HEAD_WIDTH / 2); // Optional: zentriert auf Zeit
        let head_y = y_pos - (NOTE_HEAD_HEIGHT / 2);

        // -------------------------------------------------------------
        // Hilfslinien
        // -------------------------------------------------------------

        // 1. Berechnung sicherstellen (falls noch nicht geschehen):
        let abs_step = get_staff_step(display_key, flat);
        let rel_step = abs_step - c4_step;

        // DEBUGGING (Einkommentieren bei Bedarf):
        // if n.start_time > current_time && n.start_time < current_time + 0.1 {
        //    println!("Note: {}, Abs: {}, Rel: {}", display_key, abs_step, rel_step);
        // }

        let mut ledger_start = 0;
        let mut ledger_end = 0;
        let mut draw_ledgers = false;

        // Wichtig: Wir vergleichen rel_step (z.B. 0) statt abs_step (z.B. 28)
        if rel_step > 10 {
            // FALL 1: Note über dem Violinschlüssel (oberhalb F5 / Step 10)
            ledger_start = 12;
            ledger_end = rel_step;
            draw_ledgers = true;
        } else if rel_step < 2 {
            // FALL 2: Note unter der untersten Linie des Violinschlüssels (E4 / Step 2)

            if !SHOW_BASS_STAFF {
                // Wenn Bass deaktiviert ist: Leiter hoch bis zum Violinschlüssel (Step 0)
                // Wir zeichnen von der Note hoch bis zur 0 (Mittel-C Linie)
                ledger_start = rel_step;
                ledger_end = 0;
                draw_ledgers = true;
            } else {
                // Wenn Bass-System aktiv ist:
                // Bass liegt zwischen -10 und -2.

                if rel_step > -2 {
                    // "Niemandsland" zwischen Bass (-2) und Treble (2): Steps -1, 0, 1
                    // Mittel-C ist Step 0. Wir zeichnen nur die Linie auf der 0.
                    if rel_step == 0 {
                        ledger_start = 0;
                        ledger_end = 0;
                        draw_ledgers = true;
                    }
                } else if rel_step < -10 {
                    // Note unter dem Bass-Schlüssel (unter G2 / Step -10)
                    ledger_start = rel_step;
                    ledger_end = -12;
                    draw_ledgers = true;
                }
            }
        }

        if draw_ledgers {
            env.canvas.set_draw_color(STAFF_COLOR);
            // Iteriere durch den Bereich.
            for s in ledger_start..=ledger_end {
                // Zeichne nur auf geraden Steps (Linien)
                if s % 2 == 0 {
                    let ly = center_y - (s * STAFF_LINE_SPACING / 2);

                    // Zentriert um den Notenkopf
                    let lx = head_x + (NOTE_HEAD_WIDTH / 2) as i32 - (LEDGER_LINE_WIDTH / 2) as i32;

                    env.canvas.fill_rect(Rect::new(
                        lx,
                        ly,
                        LEDGER_LINE_WIDTH,
                        STAFF_LINE_THICKNESS
                    )).unwrap_or(());
                }
            }
        }

        // Note zeichnen ein wenig verzögern, damit sie nicht
        // von den Hilfslinien der nächsten Noten überdeckt wird
        let new_head = BufferedHead {
            x: head_x, y: head_y, midi_key: display_key,
            color: Color::RGBA(color.r, color.g, color.b, 255),
        };
        if let Some(old_head) = env.ring_buffer.push_overflow(new_head) {
            render_note(env, &old_head, textures);
        }
    }

    while let Some(head) = env.ring_buffer.pop() {
        render_note(env, &head, textures);
    }

    render_keys(env, textures, center_y, flat);
}
