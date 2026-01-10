#!/usr/bin/env python3
# ======================================================================
# Enharmonically accurate transposer
# Version 2026-01-10
#
# A musically aware transposer that calculates intervals correctly
# (steps + semitones) instead of just shifting MIDI pitch values.
# Handles enharmonics correctly (e.g., distinguishing F from E#).
# ======================================================================

import re
import tkinter as tk
from tkinter import ttk, messagebox

# ======================================================================
# CONFIGURATION
# ======================================================================
UI_LANG = "de"
UI_FONT_FAMILY = "DejaVu Sans Mono"
UI_FONT_SIZE = 11
UI_CODE_FONT_SIZE = 12
UI_PADDING = 10
UI_WINDOW_WIDTH = 1100
UI_WINDOW_HEIGHT = 850

# Musikalische Konstanten
# Stammtöne: C, D, E, F, G, A, H(B)
# Semitone Indices: 0, 2, 4, 5, 7, 9, 11
NATURAL_SEMITONES = [0, 2, 4, 5, 7, 9, 11]

# Insert your exotic intervals here, if needed
# (Display Name, Steps, Semitones)
INTERVALS = [
    ("Reine Prime / Unison", 0, 0),
    ("Kleine Sekunde (m2)", 1, 1),
    ("Große Sekunde (M2)", 1, 2),
    ("Übermäßige Sekunde (A2)", 1, 3),
    ("Kleine Terz (m3)", 2, 3),
    ("Große Terz (M3)", 2, 4),
    ("Reine Quarte (P4)", 3, 5),
    ("Übermäßige Quarte / Tritonus (A4)", 3, 6),
    ("Verminderte Quinte (d5)", 4, 6),
    ("Reine Quinte (P5)", 4, 7),
    ("Kleine Sexte (m6)", 5, 8),
    ("Große Sexte (M6)", 5, 9),
    ("Kleine Septime (m7)", 6, 10),
    ("Große Septime (M7)", 6, 11),
    ("Reine Oktave (P8)", 7, 12)
]

UI_TEXTS = {
    "en": {
        "title": "Enharmonically accurate transposer",
        "config_header": " Configuration ",
        "in_lang": "Input Syntax:",
        "out_lang": "Output Syntax:",
        "trans_header": " Transposition Interval ",
        "direction": "Direction:",
        "dir_up": "Up (+)",
        "dir_down": "Down (−)",
        "input_label": "Input (LilyPond Code):",
        "output_label": "Result:",
        "btn_run": "Transpose",
        "lang_en": "English (bes, b)",
        "lang_de": "German (b, h)",
        "lang_nl": "Nederlands (bes, b)",
        "ctx_cut": "Cut",
        "ctx_copy": "Copy",
        "ctx_paste": "Paste",
        "ctx_select_all": "Select All",
        "err_title": "Error",
        "err_msg": "An error occurred during processing:"
    },
    "de": {
        "title": "Enharmonisch akkurater Transposer",
        "config_header": " Konfiguration ",
        "in_lang": "Eingabe-Sprache:",
        "out_lang": "Ausgabe-Sprache:",
        "trans_header": " Transpositions-Intervall ",
        "direction": "Richtung:",
        "dir_up": "Aufwärts (+)",
        "dir_down": "Abwärts (−)",
        "input_label": "Eingabe (LilyPond-Code):",
        "output_label": "Ergebnis:",
        "btn_run": "Transponieren",
        "lang_en": "Englisch (bes, b)",
        "lang_de": "Deutsch (b, h)",
        "lang_nl": "Niederländisch",
        "ctx_cut": "Ausschneiden",
        "ctx_copy": "Kopieren",
        "ctx_paste": "Einfügen",
        "ctx_select_all": "Alles auswählen",
        "err_title": "Fehler",
        "err_msg": "Ein Fehler ist aufgetreten:"
    }
}

# ======================================================================
# CORE LOGIC
# ======================================================================

class Note:
    """Represents a musical note logically."""
    def __init__(self, base_index, accidental, octave):
        self.base_index = base_index # 0=C, 1=D, ... 6=B/H
        self.accidental = accidental # -2, -1, 0, 1, 2
        self.octave = octave         # 0 = c (small), 1 = c', -1 = C, etc.

class DiatonicTransposer:
    def __init__(self, input_lang="en", output_lang="en"):
        self.input_lang = input_lang
        self.output_lang = output_lang
        
        # 1. Build parsing dictionaries (String -> (Base, Accidental))
        self.note_map = self._build_note_map(input_lang)
        
        # 2. Build formatting dictionaries ((Base, Accidental) -> String)
        self.reverse_map = self._build_reverse_map(output_lang)

        # 3. Regex: Structure-aware.
        # Captures Comments, Commands, Strings to ignore them.
        # "Potential Note": Starts with a-h, followed by letters, then octave marks.
        # We validate if it's ACTUALLY a note by checking self.note_map later.
        self.pattern = re.compile(
            r"(?P<comment>%.*)|"
            r"(?P<command>\\[a-zA-Z]+)|"
            r"(?P<string>\"[^\"]*\")|"
            r"(?P<token>\b[a-h][a-z]*(?:[']+|[,]+)?(?![a-z]))" 
        )

    def _build_note_map(self, lang):
        """Generates a dictionary of allowed note names for input."""
        mapping = {}
        
        # Base definitions: (BaseIndex, NaturalName)
        # 0=c, 1=d, 2=e, 3=f, 4=g, 5=a, 6=b/h
        bases = {
            0: 'c', 1: 'd', 2: 'e', 3: 'f', 4: 'g', 5: 'a', 6: 'b'
        }
        
        # Standard Suffixes
        suffixes = {
            '': 0, 'is': 1, 'isis': 2,
            'es': -1, 'eses': -2
        }

        # --- GENERATE STANDARD COMBINATIONS ---
        for idx, char in bases.items():
            # In German, base 6 is 'h', in English it's 'b'
            if lang == 'de' and idx == 6:
                base_char = 'h'
            else:
                base_char = char
                
            for suf, acc in suffixes.items():
                # Handle standard concatenations (e.g. cis, des)
                # English: e+es = ees, a+es = aes
                # German: e+es = es, a+es = as (handled via override below usually, 
                # but let's generate standard first)
                name = base_char + suf
                mapping[name] = (idx, acc)

        # --- APPLY EXCEPTIONS / OVERRIDES ---
        
        if lang == 'en':
            # English quirks if any. LilyPond "english" uses ees, aes.
            # Some users write 'es' or 'as' shorthand, but strictly it is 'ees'.
            # We add standard variations just in case.
            pass

        elif lang == 'de':
            # 1. The "B" special case (Bb)
            mapping['b'] = (6, -1)
            
            # 2. Vowel contractions (es, as) instead of ees, aes
            # Delete wrong generated ones first if necessary, or just overwrite
            # E (2)
            mapping['es'] = (2, -1)      # replaces ees (if it existed) or adds es
            mapping['eses'] = (2, -2)    # replaces eeses
            
            # A (5)
            mapping['as'] = (5, -1)
            mapping['ases'] = (5, -2)    # THIS fixes the ases bug!
            
            # Remove "ees", "aes" if they were generated by the loop above?
            # The loop used 'e'+'es' -> 'ees'. So yes, let's clean up strict German.
            bad_keys = ['ees', 'eeses', 'aes', 'aeses', 'hes', 'heses']
            for k in bad_keys:
                if k in mapping: del mapping[k]
            
            # Add strict German H-flat logic
            # H (6) + es -> Heses is technically correct for Bbb, but 'b' is Bb.
            # 'heses' is usually Bbb.
            mapping['heses'] = (6, -2)
            # 'his' is B-sharp. 'hisis' B-double-sharp. Already generated by loop.

        return mapping

    def _build_reverse_map(self, lang):
        """
        Builds a lookup for formatting: (BaseIndex, Accidental) -> String
        Used for Output.
        """
        rev_map = {}
        # We can reuse the logic of build_note_map but inverted.
        # However, we must ensure 1:1 mapping for canonical output.
        
        # Priority logic: 
        # In German, (6, -1) MUST be "b", not "hes".
        # In German, (2, -1) MUST be "es", not "ees".
        
        # Let's define canonical names explicitly.
        bases = [0, 1, 2, 3, 4, 5, 6]
        
        for idx in bases:
            for acc in range(-2, 3): # -2 to +2
                name = ""
                # default calc
                std_chars = ['c', 'd', 'e', 'f', 'g', 'a', 'b']
                base_char = std_chars[idx]
                
                if lang == 'en':
                    # English is regular-ish
                    suffix = ""
                    if acc == 0: suffix = ""
                    elif acc == 1: suffix = "is"
                    elif acc == 2: suffix = "isis"
                    elif acc == -1: suffix = "es" # standard lilypond english is 'es' suffix, but...
                    elif acc == -2: suffix = "eses"
                    
                    # Fix vowels for standard english notation (ees, aes)
                    if base_char == 'e' and acc < 0:
                         name = 'e' + suffix # ees
                    elif base_char == 'a' and acc < 0:
                         name = 'a' + suffix # aes
                    else:
                        name = base_char + suffix

                elif lang == 'de':
                    # German Logic
                    if idx == 6: # H / B
                        if acc == 0: name = "h"
                        elif acc == 1: name = "his"
                        elif acc == 2: name = "hisis"
                        elif acc == -1: name = "b"     # Exception
                        elif acc == -2: name = "heses" # Exception (or beses? heses is standard)
                    
                    elif idx == 2: # E
                        if acc == -1: name = "es"
                        elif acc == -2: name = "eses"
                        else: name = "e" + ("is"*acc) if acc>0 else "e" # logic handled below
                    
                    elif idx == 5: # A
                        if acc == -1: name = "as"
                        elif acc == -2: name = "ases"
                        else: name = "a" + ("is"*acc) if acc>0 else "a"
                    
                    else: # c, d, f, g
                        name = base_char
                        if acc > 0: name += "is" * acc
                        elif acc < 0: name += "es" * abs(acc)

                    # Fallback for E/A positives
                    if name == "":
                        base_c = "h" if (idx==6) else std_chars[idx]
                        if acc > 0: name = base_c + "is" * acc
                        elif acc == 0: name = base_c

                rev_map[(idx, acc)] = name
        
        return rev_map

    def transpose_text(self, text, interval_steps, interval_semitones):
        
        def replace_func(m):
            # If it matched a comment, command, or string, return as is
            if m.group("comment") or m.group("command") or m.group("string"):
                return m.group(0)
            
            # Potential token found
            token = m.group("token")
            
            # Split into Name and Octave
            # Use regex to split strictly at the boundary of letters and ' or ,
            # Token regex was: \b[a-h][a-z]*(?:[']+|[,]+)?
            matcher = re.match(r"([a-zA-Z]+)([' ,]*)", token)
            if not matcher: return token # Should match due to group regex
            
            name_part, oct_part = matcher.groups()
            
            # --- VALIDATION STEP ---
            # Check if the name part is actually a valid note in the input language
            if name_part not in self.note_map:
                # Example: "cs" or "cresc" (if regex allowed it) or "f" (forte dynamic? handled as note usually)
                # If "f" is in map (it is), it gets transposed. 
                # If "cs" is input, it is NOT in map -> returned untransposed.
                return token 
            
            # Parse
            base_idx, accidental = self.note_map[name_part]
            
            curr_octave = 0
            curr_octave += oct_part.count("'")
            curr_octave -= oct_part.count(",")
            
            # --- TRANSPOSITION CALCULATION (Same as before) ---
            old_base_idx = base_idx
            new_base_idx = (old_base_idx + interval_steps) % 7
            
            oct_shift = (old_base_idx + interval_steps) // 7
            new_octave = curr_octave + oct_shift
            
            old_natural_pitch = NATURAL_SEMITONES[old_base_idx]
            new_natural_pitch = NATURAL_SEMITONES[new_base_idx]
            
            old_abs = old_natural_pitch + accidental
            target_abs = old_abs + interval_semitones
            
            semitone_oct_correction = oct_shift * 12 
            new_accidental = target_abs - (new_natural_pitch + semitone_oct_correction)
            
            # --- FORMATTING ---
            # Lookup name from reverse map
            key = (new_base_idx, new_accidental)
            
            # Fallback if accidental is crazy high/low (outside -2..2)
            # The reverse map currently only builds -2..+2. 
            # If logic produces +3, we need a generic fallback or expand the map.
            if key in self.reverse_map:
                new_name = self.reverse_map[key]
            else:
                # Generic fallback constructor for weird intervals
                std_chars = ['c', 'd', 'e', 'f', 'g', 'a', 'b']
                base_c = std_chars[new_base_idx]
                if self.output_lang == 'de' and new_base_idx == 6: base_c = 'h' # simplified
                
                suff = ""
                acc = new_accidental
                while acc > 0: suff += "is"; acc -= 1
                while acc < 0: suff += "es"; acc += 1
                new_name = base_c + suff
            
            new_oct_str = ""
            if new_octave > 0: new_oct_str = "'" * new_octave
            elif new_octave < 0: new_oct_str = "," * abs(new_octave)
            
            return new_name + new_oct_str

        return self.pattern.sub(replace_func, text)

# ======================================================================
# GUI
# ======================================================================

class TransposerGUI:
    def __init__(self, root):
        self.texts = UI_TEXTS[UI_LANG]
        self.root = root
        self.root.title(self.texts["title"])
        self.root.geometry(f"{UI_WINDOW_WIDTH}x{UI_WINDOW_HEIGHT}")
        self.root.option_add("*TCombobox*Listbox.font", (UI_FONT_FAMILY, UI_FONT_SIZE))
        
        self.setup_styles()
        self.create_widgets()

    def setup_styles(self):
        style = ttk.Style()
        style.configure(".", font=(UI_FONT_FAMILY, UI_FONT_SIZE))
        style.configure("TLabelframe.Label", font=(UI_FONT_FAMILY, UI_FONT_SIZE, "bold"))
        style.configure("Action.TButton", font=(UI_FONT_FAMILY, UI_FONT_SIZE, "bold"), foreground="#000")
        
        # Grid weights
        self.root.columnconfigure(0, weight=1)
        self.root.rowconfigure(0, weight=1)

    def create_widgets(self):
        main_frame = ttk.Frame(self.root, padding=UI_PADDING)
        main_frame.grid(row=0, column=0, sticky="NSEW")
        main_frame.columnconfigure(0, weight=1) 
        
        # --- 1. CONFIGURATION ---
        config_frame = ttk.LabelFrame(main_frame, text=self.texts["config_header"], padding=UI_PADDING)
        config_frame.grid(row=0, column=0, sticky="EW", pady=(0, UI_PADDING))
        
        # Language Options
        lang_opts = [self.texts["lang_en"], self.texts["lang_de"]]
        
        ttk.Label(config_frame, text=self.texts["in_lang"]).pack(side="left", padx=5)
        self.cb_in_lang = ttk.Combobox(config_frame, values=lang_opts, state="readonly", width=20,
          font=(UI_FONT_FAMILY, UI_FONT_SIZE))
        self.cb_in_lang.set(lang_opts[0]) # Default English
        self.cb_in_lang.pack(side="left", padx=5)
        
        ttk.Label(config_frame, text=" " * 5).pack(side="left") # Spacer
        
        ttk.Label(config_frame, text=self.texts["out_lang"]).pack(side="left", padx=5)
        self.cb_out_lang = ttk.Combobox(config_frame, values=lang_opts, state="readonly", width=20,
          font=(UI_FONT_FAMILY, UI_FONT_SIZE))
        self.cb_out_lang.set(lang_opts[0]) # Default English
        self.cb_out_lang.pack(side="left", padx=5)
        
        # --- 2. TRANSPOSITION CONTROL ---
        trans_frame = ttk.LabelFrame(main_frame, text=self.texts["trans_header"], padding=UI_PADDING)
        trans_frame.grid(row=1, column=0, sticky="EW", pady=(0, UI_PADDING))
        
        # Direction
        ttk.Label(trans_frame, text=self.texts["direction"]).pack(side="left", padx=5)
        self.cb_direction = ttk.Combobox(trans_frame, values=[self.texts["dir_up"], self.texts["dir_down"]], 
                                         state="readonly", width=15, font=(UI_FONT_FAMILY, UI_FONT_SIZE))
        self.cb_direction.current(0)
        self.cb_direction.pack(side="left", padx=5)
        
        # Interval
        interval_names = [x[0] for x in INTERVALS]
        self.cb_interval = ttk.Combobox(trans_frame, values=interval_names, state="readonly", width=35,
          font=(UI_FONT_FAMILY, UI_FONT_SIZE))
        self.cb_interval.current(2) # Default Major 2nd
        self.cb_interval.pack(side="left", padx=10)
        
        # --- 3. TEXT AREAS ---
        text_frame = ttk.Frame(main_frame)
        text_frame.grid(row=2, column=0, sticky="NSEW")
        main_frame.rowconfigure(2, weight=1)
        text_frame.columnconfigure(0, weight=1)
        text_frame.rowconfigure(1, weight=1) # Input
        text_frame.rowconfigure(4, weight=1) # Output
        
        # Input
        ttk.Label(text_frame, text=self.texts["input_label"]).grid(row=0, column=0, sticky="W")
        self.txt_in = tk.Text(text_frame, font=(UI_FONT_FAMILY, UI_CODE_FONT_SIZE), height=10, undo=True)
        self.txt_in.grid(row=1, column=0, sticky="NSEW", pady=(5, 10))
        self.add_context_menu(self.txt_in)
        
        # Action Button
        self.btn_run = ttk.Button(text_frame, text=self.texts["btn_run"], command=self.process, style="Action.TButton")
        self.btn_run.grid(row=2, column=0, sticky="EW", pady=5)
        
        # Output
        ttk.Label(text_frame, text=self.texts["output_label"]).grid(row=3, column=0, sticky="W")
        self.txt_out = tk.Text(text_frame, font=(UI_FONT_FAMILY, UI_CODE_FONT_SIZE), height=10, bg="#f0f0f0")
        self.txt_out.grid(row=4, column=0, sticky="NSEW", pady=(5, 0))
        self.add_context_menu(self.txt_out)

    def add_context_menu(self, widget):
        menu = tk.Menu(widget, tearoff=0, font=(UI_FONT_FAMILY, UI_FONT_SIZE))
        menu.add_command(label=self.texts["ctx_cut"], command=lambda: widget.event_generate("<<Cut>>"))
        menu.add_command(label=self.texts["ctx_copy"], command=lambda: widget.event_generate("<<Copy>>"))
        menu.add_command(label=self.texts["ctx_paste"], command=lambda: widget.event_generate("<<Paste>>"))
        menu.add_separator()
        menu.add_command(label=self.texts["ctx_select_all"], command=lambda: widget.tag_add("sel", "1.0", "end"))
        
        def show_menu(event):
            menu.tk_popup(event.x_root, event.y_root)
        
        widget.bind("<Button-3>", show_menu)
        widget.bind("<Button-2>", show_menu)

    def process(self):
        try:
            # 1. Gather Configuration
            in_lang_code = "de" if self.cb_in_lang.get() == self.texts["lang_de"] else "en"
            out_lang_code = "de" if self.cb_out_lang.get() == self.texts["lang_de"] else "en"
            
            # 2. Get Interval Data
            idx = self.cb_interval.current()
            if idx < 0: return
            
            _, steps, semitones = INTERVALS[idx]
            
            # 3. Apply Direction
            is_up = (self.cb_direction.get() == self.texts["dir_up"])
            if not is_up:
                steps = -steps
                semitones = -semitones
            
            # 4. Transpose
            tp = DiatonicTransposer(input_lang=in_lang_code, output_lang=out_lang_code)
            raw_text = self.txt_in.get("1.0", tk.END)
            
            result = tp.transpose_text(raw_text, steps, semitones)
            
            self.txt_out.delete("1.0", tk.END)
            self.txt_out.insert("1.0", result)
            
        except Exception as e:
            messagebox.showerror(self.texts["err_title"], f"{self.texts['err_msg']}\n{str(e)}")
            print(e) # For debug

if __name__ == "__main__":
    root = tk.Tk()
    app = TransposerGUI(root)
    root.mainloop()
