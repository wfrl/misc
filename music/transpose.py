#!/usr/bin/env python3
# ======================================================================
# Transposer tool for musical notation
# Version 2026-01-10
#
# This utility provides a graphical user interface for transposing
# musical notation written in LilyPond format. It processes raw text,
# identifying pitch names and adjusting them according to a specified
# interval or semitone offset.
# ======================================================================

import re
import tkinter as tk
from tkinter import ttk, messagebox

# ======================================================================
# CONFIGURATION
# ======================================================================
UI_LANG = "en"
UI_FONT_FAMILY = "DejaVu Sans Mono"
UI_FONT_SIZE = 12
UI_CODE_FONT_SIZE = 12
UI_PADDING = 10
UI_WINDOW_WIDTH = 1000
UI_WINDOW_HEIGHT = 800

OUTPUT_MAPPINGS = [
    ("mode_en_sharp", "c cis d dis e f fis g gis a ais b".split()),
    ("mode_en_flat",  "c des d ees e f ges g aes a bes b".split()),
    ("mode_de_sharp", "c cis d dis e f fis g gis a ais h".split()),
    ("mode_de_flat",  "c des d es e f ges g as a b h".split())
]

BASE_ALIASES = {
    "c": 0, "deses": 0, "cis": 1, "des": 1, "d": 2, "cisis": 2,
    "eeses": 2, "eses": 2, "dis": 3, "es": 3, "ees": 3, "feses": 3,
    "e": 4, "fes": 4, "disis": 4, "f": 5, "eis": 5, "geses": 5,
    "fis": 6, "ges": 6, "aeses": 7, "ases": 7, "asas": 7, "g": 7,
    "fisis": 7, "gis": 8, "as": 8, "aes": 8, "a": 9, "gisis": 9,
    "ais": 10, "ceses": 10, "ces": 11, "aisis": 11
}

# c cs d ds e f fs g gs a as b
# c df d ef e f gf g af a bf b

# do dos re res mi fa fas sol sols la las si
# do reb re mib mi fa solb sol lab la sib si

# Internationalisation of the user interface. Add your native language
# here to provide the software for your people.
UI_TEXTS = {
    "en": {
        "title": "Transposer",
        "config_header": " Configuration ",
        "in_mode_label": "Input Mode:",
        "out_mode_label": "Output Mode:",
        "trans_header": " Transposition ",
        "semitones": "Semitones:",
        "interval_or": "OR Interval:",
        "input_label": "Input (LilyPond Code):",
        "output_label": "Result:",
        "btn_run": "Transpose",
        "lang_en": "English",
        "lang_de": "German",
        "err_title_input": "Input Error",
        "err_msg_input": "Please enter a valid number for semitones or correct note names.",
        "err_title_gen": "Error",
        "err_msg_gen": "An unexpected error occurred:",
        "ctx_cut": "Cut",
        "ctx_copy": "Copy",
        "ctx_paste": "Paste",
        "ctx_select_all": "Select All",
        "mode_en_sharp": "English (Sharp)",
        "mode_en_flat":  "English (Flat)",
        "mode_de_sharp": "German (Sharp)",
        "mode_de_flat":  "German (Flat)"
    },
    "de": {
        "title": "Transposer",
        "config_header": " Konfiguration ",
        "in_mode_label": "Eingabe-Form:",
        "out_mode_label": "Ausgabe-Form:",
        "trans_header": " Transposition ",
        "semitones": "Halbtöne:",
        "interval_or": "ODER Intervall:",
        "input_label": "Eingabe (LilyPond-Code):",
        "output_label": "Ergebnis:",
        "btn_run": "Transponieren",
        "lang_en": "Englisch",
        "lang_de": "Deutsch",
        "err_title_input": "Eingabefehler",
        "err_msg_input": "Bitte eine gültige Zahl für Halbtöne oder korrekte Notennamen eingeben.",
        "err_title_gen": "Fehler",
        "err_msg_gen": "Ein unerwarteter Fehler ist aufgetreten:",
        "ctx_cut": "Ausschneiden",
        "ctx_copy": "Kopieren",
        "ctx_paste": "Einfügen",
        "ctx_select_all": "Alles auswählen",
        "mode_en_sharp": "Englisch (Kreuz)",
        "mode_en_flat":  "Englisch (Be)",
        "mode_de_sharp": "Deutsch (Kreuz)",
        "mode_de_flat":  "Deutsch (Be)"
    }
}
# ======================================================================

class Transposer:
    def __init__(self, input_mode="en", target_mapping=None):
        self.input_aliases = BASE_ALIASES.copy()
        if input_mode == "de":
            self.input_aliases["heses"] = 9
            self.input_aliases["b"] = 10
            self.input_aliases["h"] = 11
            self.input_aliases["his"] = 0
            self.input_aliases["hisis"] = 1
        else:
            self.input_aliases["beses"] = 9
            self.input_aliases["bes"] = 10
            self.input_aliases["b"] = 11
            self.input_aliases["bis"] = 0
            self.input_aliases["bisis"] = 1

        self.target = (target_mapping or
            ["c", "cis", "d", "dis", "e", "f", "fis", "g", "gis", "a", "ais", "b"])
        all_known = sorted(self.input_aliases.keys(), key=len, reverse=True)
        self.pattern = re.compile(
            r"(?P<comment>%.*)|(?P<note>(?<!\\)\b(" + "|".join(all_known) + r")([',]*))")

    def _get_semitones(self, pitch_str):
        m = re.match(r"([a-z]+)([',]*)", pitch_str)
        if not m: return 0
        name, octs = m.groups()
        val = self.input_aliases.get(name, 0)
        val += octs.count("'") * 12
        val -= octs.count(",") * 12
        return val

    def _val_to_pitch(self, total_val):
        name = self.target[total_val % 12]
        oct_off = total_val // 12
        return name + ("'" * oct_off if oct_off > 0 else "," * abs(oct_off))

    def transpose(self, text, delta):
        return self.pattern.sub(lambda m: m.group("comment") if m.group("comment") else 
            self._val_to_pitch(self._get_semitones(m.group("note")) + delta), text)

class TransposerGUI:
    def __init__(self, root):
        self.texts = UI_TEXTS[UI_LANG]
        self.root = root
        self.root.title(self.texts["title"])
        self.root.geometry(f"{UI_WINDOW_WIDTH}x{UI_WINDOW_HEIGHT}")

        # Font for the drop-down lists (list box part of the combo box)
        self.root.option_add("*TCombobox*Listbox.font", (UI_FONT_FAMILY, UI_FONT_SIZE))

        self.setup_styles()

        # Preparing the mapping lookup
        self.display_to_mapping = {}
        self.output_options = []
        for abstract_key, mapping_list in OUTPUT_MAPPINGS:
            display_name = self.texts.get(abstract_key, abstract_key)
            self.output_options.append(display_name)
            self.display_to_mapping[display_name] = mapping_list

        # Main container
        main_frame = ttk.Frame(root, padding=UI_PADDING)
        main_frame.grid(row=0, column=0, sticky="NSEW")
        root.columnconfigure(0, weight=1)
        root.rowconfigure(0, weight=1)

        # 1. Configuration
        config_frame = ttk.LabelFrame(main_frame, text=self.texts["config_header"],
            padding=UI_PADDING)
        config_frame.grid(row=0, column=0, sticky="EW", pady=(0, UI_PADDING))
        main_frame.columnconfigure(0, weight=1)

        self.in_mode = self.add_combo(config_frame, self.texts["in_mode_label"], 
            [self.texts["lang_en"], self.texts["lang_de"]], 0, 0)
        self.in_mode.set(self.texts["lang_en"])

        self.out_mode = self.add_combo(config_frame, self.texts["out_mode_label"], 
            self.output_options, 0, 2)
        self.out_mode.set(self.output_options[0])

        # 2. Transposition
        trans_frame = ttk.LabelFrame(main_frame, text=self.texts["trans_header"],
            padding=UI_PADDING)
        trans_frame.grid(row=1, column=0, sticky="EW", pady=(0, UI_PADDING))

        ttk.Label(trans_frame, text=self.texts["semitones"]).grid(row=0, column=0, padx=5)
        self.semitones = ttk.Entry(trans_frame, width=5, font=(UI_FONT_FAMILY, UI_FONT_SIZE))
        self.semitones.insert(0, "2")
        self.semitones.grid(row=0, column=1, padx=10)

        ttk.Label(trans_frame, text=self.texts["interval_or"]).grid(row=0, column=2, padx=5)
        self.inter_start = ttk.Entry(trans_frame, width=5, font=(UI_FONT_FAMILY, UI_FONT_SIZE))
        self.inter_start.grid(row=0, column=3)
        ttk.Label(trans_frame, text=" → ").grid(row=0, column=4)
        self.inter_end = ttk.Entry(trans_frame, width=5, font=(UI_FONT_FAMILY, UI_FONT_SIZE))
        self.inter_end.grid(row=0, column=5)

        # 3. Text areas
        text_container = ttk.Frame(main_frame)
        text_container.grid(row=2, column=0, sticky="NSEW")
        main_frame.rowconfigure(2, weight=1) # Allows the container to grow
        text_container.columnconfigure(0, weight=1)

        # Line weights used in the text container
        text_container.rowconfigure(1, weight=1) # Input field (txt_in)
        text_container.rowconfigure(4, weight=1) # Output field (txt_out)

        ttk.Label(text_container, text=self.texts["input_label"]).grid(
            row=0, column=0, sticky="W")
        self.txt_in = tk.Text(text_container,
            font=(UI_FONT_FAMILY, UI_CODE_FONT_SIZE), undo=True, height=8)
        self.txt_in.grid(row=1, column=0, sticky="NSEW", pady=(5, UI_PADDING))
        self.add_context_menu(self.txt_in)

        self.btn_run = ttk.Button(text_container, text=self.texts["btn_run"],
            command=self.process, style="Action.TButton")
        self.btn_run.grid(row=2, column=0, pady=5, sticky="EW")

        ttk.Label(text_container, text=self.texts["output_label"]).grid(
            row=3, column=0, sticky="W", pady=(UI_PADDING, 0))
        self.txt_out = tk.Text(text_container,
            font=(UI_FONT_FAMILY, UI_CODE_FONT_SIZE), bg="#f8f9fa", height=8)
        self.txt_out.grid(row=4, column=0, sticky="NSEW", pady=(5, 0))
        self.add_context_menu(self.txt_out)

    def add_context_menu(self, widget):
        menu = tk.Menu(widget, tearoff=0, font=(UI_FONT_FAMILY, UI_FONT_SIZE))
        menu.add_command(label=self.texts["ctx_cut"],
            command=lambda: widget.event_generate("<<Cut>>"))
        menu.add_command(label=self.texts["ctx_copy"],
            command=lambda: widget.event_generate("<<Copy>>"))
        menu.add_command(label=self.texts["ctx_paste"],
            command=lambda: widget.event_generate("<<Paste>>"))
        menu.add_separator()
        menu.add_command(label=self.texts["ctx_select_all"],
            command=lambda: widget.tag_add("sel", "1.0", "end"))

        def show_menu(event):
            menu.tk_popup(event.x_root, event.y_root)

        widget.bind("<Button-3>", show_menu) 
        widget.bind("<Button-2>", show_menu) 

    def setup_styles(self):
        style = ttk.Style()
        style.configure(".", font=(UI_FONT_FAMILY, UI_FONT_SIZE))
        style.configure("TLabelframe.Label",
            font=(UI_FONT_FAMILY, UI_FONT_SIZE, "bold"))
        style.configure("Action.TButton",
            font=(UI_FONT_FAMILY, UI_FONT_SIZE, "bold"), foreground="#000")
        style.map("Action.TButton", foreground=[('active', '#0056b3')])

    def add_combo(self, parent, label, values, row, col):
        ttk.Label(parent, text=label).grid(row=row, column=col, padx=5, sticky="E")
        cb = ttk.Combobox(parent, values=values, state="readonly", width=22, 
                          font=(UI_FONT_FAMILY, UI_FONT_SIZE)) 
        cb.grid(row=row, column=col+1, padx=10, pady=5, sticky="W")
        return cb

    def process(self):
        try:
            mode_internal = "de" if self.in_mode.get() == self.texts["lang_de"] else "en"
            target_map = self.display_to_mapping.get(self.out_mode.get())

            tp = Transposer(input_mode=mode_internal, target_mapping=target_map)

            if self.inter_start.get().strip() and self.inter_end.get().strip():
                b = tp._get_semitones(self.inter_end.get().strip())
                a = tp._get_semitones(self.inter_start.get().strip())
                delta = b - a
            else:
                delta = int(self.semitones.get())

            raw_text = self.txt_in.get("1.0", tk.END)
            result = tp.transpose(raw_text, delta)
            self.txt_out.delete("1.0", tk.END)
            self.txt_out.insert("1.0", result)
        except ValueError:
            messagebox.showerror(self.texts["err_title_input"],
                self.texts["err_msg_input"])
        except Exception as e:
            messagebox.showerror(self.texts["err_title_gen"],
                f"{self.texts['err_msg_gen']}\n{e}")

if __name__ == "__main__":
    root = tk.Tk()
    app = TransposerGUI(root)
    root.mainloop()

