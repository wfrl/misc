//
// DOCUMENTATION GENERATOR
//

// TODO: User interface currently only in english. Needs
// internationalisation.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt;
use std::fs;
use std::io;
use std::path::Path;

const DEFAULT_DIR_NAME: &str = "proofs-doc";
const DEFAULT_TOC_NAME: &str = "proofs-toc";
const ALL_ITEMS_NAME: &str = "all-items";
const NON_LINK: [&str; 5] = ["axiom", "rule", "def", "decl", "calc"];

// Safety: DOC_MARKER *must* be collision free.
const DOC_MARKER: &str = ".nd_proof_checker_doc";
const TOC_MARKER: &str = "<!-- nd-proof-checker-toc -->";


// == Public API ==

#[derive(Debug)]
pub enum DocError {
    Syntax {file: String, line: usize, msg: String},
    Io {path: String, source: io::Error},
    Safety(String)
}

impl fmt::Display for DocError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DocError::Syntax {file, line, msg} => write!(f, "{}:{}: {}", file, line, msg),
            DocError::Io {path, source} => write!(f, "{}: {}", path, source),
            DocError::Safety(msg) => write!(f, "Safety error: {}", msg)
        }
    }
}

impl std::error::Error for DocError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            DocError::Io {source, ..} => Some(source),
            DocError::Syntax {..} => None,
            DocError::Safety {..} => None
        }
    }
}

// A non-fatal problem found while reading the sources.
#[derive(Debug, Clone)]
pub struct Warning {
    pub file: String,
    pub line: usize,
    pub msg: String
}

impl fmt::Display for Warning {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}: warning: {}", self.file, self.line, self.msg)
    }
}

// One input file (the name is only used in messages).
pub struct Source {
    pub name: String,
    pub text: String
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OutFileKind {
    DocAsset, // Located in marked subfolder (e.g., CSS, chapters, search)
    RootToc   // Located in the root folder (requires TOC_MARKER)
}

// One generated output file; the path is relative to the target directory.
pub struct OutFile {
    pub path: String,
    pub content: String,
    pub kind: OutFileKind
}

pub struct Site {
    pub dir_name: String,
    pub files: Vec<OutFile>,
    pub warnings: Vec<Warning>
}

impl Site {
    // Writes all files below `base`. Like the original, only one directory
    // level is created; an already existing directory is fine.
    pub fn write_to(&self, base: &Path) -> Result<(), DocError> {
        let dir = base.join(&self.dir_name);
        let marker = dir.join(DOC_MARKER);

        if !dir.exists() {
            fs::create_dir_all(&dir)
                .map_err(|e| DocError::Io {path: dir.display().to_string(), source: e})?;
            fs::write(&marker, b"nd documentation directory\n")
                .map_err(|e| DocError::Io {path: marker.display().to_string(), source: e})?;
        } else if !marker.exists() {
            return Err(DocError::Safety(format!(
                "Directory '{}' exists but safety marker '{}' is missing.\n\
                 Aborting to protect non-documentation files.",
                dir.display(), DOC_MARKER)));
        }

        for f in &self.files {
            let p = base.join(&f.path);

            if f.kind == OutFileKind::RootToc && p.exists() {
                let existing = fs::read_to_string(&p).unwrap_or_default();
                if !existing.contains(TOC_MARKER) {
                    return Err(DocError::Safety(format!(
                        "File '{}' already exists but is missing safety marker '{}'.\n\
                         Aborting to prevent overwriting non-documentation files.",
                        p.display(), TOC_MARKER)));
                }
            }

            fs::write(&p, &f.content)
                .map_err(|e| DocError::Io { path: p.display().to_string(), source: e })?;
        }
        Ok(())
    }
}

pub fn generate(sources: &[Source]) -> Result<Site, DocError> {
    let mut env = Env::new();
    let mut acc: Vec<String> = Vec::new();
    header(&mut acc, None, "All items");
    let navi_pos = acc.len();
    acc.push(String::new());
    acc.push(" | <a href='search.htm'>Search</a></div>\n".to_string());
    let title_pos = acc.len();
    acc.push(String::new());
    let toc_pos = acc.len();
    acc.push(String::new());

    for src in sources {
        let text = normalize_newlines(&src.text);
        let chars: Vec<char> = text.chars().collect();
        extract(&src.name, &chars, &mut acc, &mut env)?;
    }

    acc[navi_pos] = format!("<div class='navi'><a href='../{}.htm'>Up</a>", env.toc_name);
    let total = env.def_count + env.decl_count + env.macro_count + env.axiom_count + env.rule_count + env.thm_count;
    acc.push("<p><b>Statistics</b>\n<pre>\n".to_string());
    acc.push(format!("{:4} definitions\n", env.def_count));
    acc.push(format!("{:4} declarations\n", env.decl_count));
    acc.push(format!("{:4} macros\n", env.macro_count));
    acc.push(format!("{:4} axioms\n", env.axiom_count));
    acc.push(format!("{:4} rules\n", env.rule_count));
    acc.push(format!("{:4} theorems\n", env.thm_count));
    acc.push(format!("{}\n", "─".repeat(16)));
    acc.push(format!("{:4} items total\n</pre>\n", total));
    footer(&mut acc);
    if !env.toc.is_empty() {
        acc[toc_pos] = table_of_contents(&env.toc);
    }
    if let Some(t) = &env.title {
        acc[title_pos] = format!("<h1>{}</h1>\n", t);
    }

    let dir = env.dir_name.clone();
    let mut files: Vec<OutFile> = Vec::new();
    files.push(OutFile {
        path: format!("{}/{}.htm", dir, ALL_ITEMS_NAME),
        content: acc.concat(),
        kind: OutFileKind::DocAsset
    });
    for p in &env.proofs {
        files.push(OutFile {
            path: format!("{}/{}", dir, page_name(&p.ident)),
            content: proof_file(&env, p),
            kind: OutFileKind::DocAsset
        });
    }
    files.push(OutFile {
        path: format!("{}/main.css", dir),
        content: main_css(),
        kind: OutFileKind::DocAsset
    });
    files.push(OutFile {
        path: format!("{}/list.css", dir),
        content: list_css(),
        kind: OutFileKind::DocAsset
    });
    files.push(toc_file(&env));
    for i in 0..env.chapters.len() {
        files.push(chapter_toc_file(&env, i));
    }
    files.push(search_page(&env));

    Ok(Site {dir_name: dir, files, warnings: env.warnings})
}


// == State ==

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {Definition, Declaration, Macro, Axiom, Rule, Theorem}

impl Kind {
    fn label(self) -> &'static str {
        match self {
            Kind::Definition => "Definition",
            Kind::Declaration => "Declaration",
            Kind::Macro => "Macro",
            Kind::Axiom => "Axiom",
            Kind::Rule => "Rule",
            Kind::Theorem => "Theorem"
        }
    }
    fn css_class(self) -> &'static str {
        match self {
            Kind::Definition => "def",
            Kind::Declaration => "decl",
            Kind::Macro => "macro",
            Kind::Axiom => "ax",
            Kind::Rule => "rule",
            Kind::Theorem => "thm"
        }
    }
}

struct TocEntry {
    title: String,
    id: String,
    children: Vec<TocEntry>,
}

struct Proof {
    ident: String,
    kind: Kind,
    item: String,
    proof: String,
    chapter: usize,
}

struct Env {
    toc: Vec<TocEntry>,
    chapter_count: usize,
    section_count: usize,
    subsection_count: usize,
    def_count: usize,
    decl_count: usize,
    macro_count: usize,
    axiom_count: usize,
    rule_count: usize,
    thm_count: usize,
    buf: Vec<String>,
    proofs: Vec<Proof>,
    dependencies: HashSet<String>,
    dep_db: HashMap<String, (Kind, HashSet<String>)>,
    // Where a name was defined (file, line); used to warn about duplicates.
    defined_at: HashMap<String, (String, usize)>,
    propose_clear: bool,
    title: Option<String>,
    notes: HashMap<String, String>,
    chapters: Vec<Vec<String>>,
    dir_name: String,
    toc_name: String,
    warnings: Vec<Warning>,
}

impl Env {
    fn new() -> Env {
        Env {
            toc: Vec::new(),
            chapter_count: 0,
            section_count: 0,
            subsection_count: 0,
            def_count: 0,
            decl_count: 0,
            macro_count: 0,
            axiom_count: 0,
            rule_count: 0,
            thm_count: 0,
            buf: Vec::new(),
            proofs: Vec::new(),
            dependencies: HashSet::new(),
            dep_db: HashMap::new(),
            defined_at: HashMap::new(),
            propose_clear: false,
            title: None,
            notes: HashMap::new(),
            chapters: Vec::new(),
            dir_name: DEFAULT_DIR_NAME.to_string(),
            toc_name: DEFAULT_TOC_NAME.to_string(),
            warnings: Vec::new()
        }
    }

    fn warn(&mut self, file: &str, line: usize, msg: impl Into<String>) {
        self.warnings.push(Warning { file: file.to_string(), line, msg: msg.into() });
    }

    // Starts a new proof: forget the steps and dependencies of the previous one.
    fn clear_proof(&mut self) {
        self.dependencies.clear();
        self.buf.clear();
        self.propose_clear = false;
    }
}


// == Character and slice helpers
// (index semantics like Python: slices are clamped) ==

fn is_space(c: char) -> bool {
    c.is_whitespace() || ('\u{1c}'..='\u{1f}').contains(&c)
}
fn is_alpha(c: char) -> bool {
    c.is_alphabetic()
}
fn is_digit(c: char) -> bool {
    c.is_numeric()
}
fn is_ident_char(c: char) -> bool {
    is_alpha(c) || is_digit(c) || c == '_' || c == '\''
}

fn slice(s: &[char], a: usize, b: usize) -> &[char] {
    let n = s.len();
    let a = a.min(n);
    let b = b.min(n);
    if a >= b {
        &s[0..0]
    } else {
        &s[a..b]
    }
}

fn slice_str(s: &[char], a: usize, b: usize) -> String {
    slice(s, a, b).iter().collect()
}

fn strip(s: &[char]) -> String {
    let mut a = 0;
    let mut b = s.len();
    while a < b && is_space(s[a]) {
        a += 1;
    }
    while b > a && is_space(s[b - 1]) {
        b -= 1;
    }
    s[a..b].iter().collect()
}

// 1-based line number of the character at `pos`.
fn line_of(s: &[char], pos: usize) -> usize {
    1 + s[..pos.min(s.len())].iter().filter(|&&c| c == '\n').count()
}

// Like Python's "universal newlines" when reading in text mode.
fn normalize_newlines(text: &str) -> String {
    text.replace("\r\n", "\n").replace('\r', "\n")
}

fn htm_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            _ => out.push(c)
        }
    }
    out
}

// Equivalent of `urllib.parse.quote(s)` (safe="/").
fn url_quote(s: &str) -> String {
    let mut out = String::new();
    for b in s.bytes() {
        if b.is_ascii_alphanumeric() || matches!(b, b'_' | b'.' | b'-' | b'~' | b'/') {
            out.push(b as char);
        } else {
            out.push_str(&format!("%{:02X}", b));
        }
    }
    out
}

// Equivalent of `json.dumps(str)` with ensure_ascii=True.
fn json_string(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{8}' => out.push_str("\\b"),
            '\u{c}' => out.push_str("\\f"),
            ' '..='~' => out.push(c),
            _ => {
                let mut buf = [0u16; 2];
                for u in c.encode_utf16(&mut buf).iter() {
                    out.push_str(&format!("\\u{:04x}", u));
                }
            }
        }
    }
    out.push('"');
    out
}


// == Scanner ==

fn consume_ident(s: &[char], mut i: usize) -> (usize, String) {
    let j = i;
    while i < s.len() && is_ident_char(s[i]) {
        i += 1;
    }
    (i, slice_str(s, j, i))
}

fn consume_space(s: &[char], mut i: usize) -> usize {
    while i < s.len() && is_space(s[i]) {
        i += 1;
    }
    i
}

fn is_open_bracket(c: char) -> bool {
    matches!(c, '(' | '{' | '[')
}
fn is_close_bracket(c: char) -> bool {
    matches!(c, ')' | '}' | ']')
}

// Index of the first `c` at bracket level 0 (`(`/`{`/`[` open,
// `)`/`}`/`]` close).
fn consume_until(c: char, s: &[char], mut i: usize) -> usize {
    let mut level: i64 = 0;
    while i < s.len() {
        let ch = s[i];
        if ch == c && level == 0 {
            break;
        } else if is_open_bracket(ch) {
            level += 1;
        } else if is_close_bracket(ch) {
            level -= 1;
        }
        i += 1;
    }
    i
}

// Binders: after one of them the notation is "charged", and the next `.` or
// `:` on the same bracket level separates the bound variable from the body
// (`forall x. P x`, `forall x: P x`). Only the discharging separator is
// affected; a `.` that ends a term is never one of them.
const BINDER_WORDS: [&str; 3] = ["forall", "exists", "fn"];
const BINDER_SYMBOLS: [char; 2] = ['∀', '∃'];

// Index of the dot that ends a term (a statement): the first `.` at bracket
// level 0 that is not the separator of a binder. Purely lexical, no parsing.
fn consume_term_end(s: &[char], mut i: usize) -> usize {
    let mut level: i64 = 0;
    // For each open bracket level (the first entry is level 0): the number of
    // binders whose separator has not been seen yet.
    let mut charged: Vec<usize> = vec![0];
    while i < s.len() {
        let ch = s[i];
        if is_ident_char(ch) {
            // Read whole words, so that `x_forall` or `fn2` are no binders.
            let (ni, word) = consume_ident(s, i);
            if BINDER_WORDS.contains(&word.as_str()) {
                if let Some(top) = charged.last_mut() {
                    *top += 1;
                }
            }
            i = ni;
            continue;
        }
        if BINDER_SYMBOLS.contains(&ch) {
            if let Some(top) = charged.last_mut() {
                *top += 1;
            }
        } else if is_open_bracket(ch) {
            level += 1;
            charged.push(0);
        } else if is_close_bracket(ch) {
            level -= 1;
            // A binder left open inside the brackets is dropped with them.
            if charged.len() > 1 {
                charged.pop();
            }
        } else if ch == '.' || ch == ':' {
            match charged.last_mut() {
                Some(top) if *top > 0 => *top -= 1,
                _ => {
                    if ch == '.' && level == 0 {
                        break;
                    }
                }
            }
        }
        i += 1;
    }
    i
}

// Reads identifiers separated by whitespace up to `.` or `,`.
// `Err(pos)`: position of a character that is no identifier character
// (the original loops forever there).
fn consume_ident_list(s: &[char], mut i: usize) -> Result<(usize, Vec<String>), usize> {
    let mut idents = Vec::new();
    while i < s.len() {
        if s[i] == '.' || s[i] == ',' {
            break;
        }
        let (ni, ident) = consume_ident(s, i);
        if ni == i {
            return Err(i);
        }
        idents.push(ident);
        i = consume_space(s, ni);
    }
    Ok((i, idents))
}

// True for labels like "2" or "10": a proof step after the first one.
fn is_number_above_one(ident: &str) -> bool {
    if ident.is_empty() || !ident.chars().all(|c| c.is_ascii_digit()) {
        return false;
    }
    let t = ident.trim_start_matches('0');
    !t.is_empty() && t != "1"
}

// The file name (without extension) of the page of an item. Capital letters
// are written as `~` and the small letter: `Union_eq` becomes `~union_eq`,
// `LEM` becomes `~l~e~m`. Names that differ only in case thus get different
// files, even on case-insensitive file systems. `~` is no identifier
// character, so different names never end up with the same file name.
// (The search page does the same in JS_CODE.)
fn file_stem(ident: &str) -> String {
    let mut out = String::with_capacity(ident.len());
    for c in ident.chars() {
        if c.is_uppercase() {
            out.push('~');
            out.extend(c.to_lowercase());
        } else {
            out.push(c);
        }
    }
    out
}

// File name of the page of an item.
fn page_name(ident: &str) -> String {
    format!("{}.htm", file_stem(ident))
}

// Link target to the page of an item.
fn page_url(ident: &str) -> String {
    url_quote(&page_name(ident))
}

fn link_ident(ident: &str) -> String {
    let starts_alpha = ident.chars().next().map_or(false, is_alpha);
    if starts_alpha && !NON_LINK.contains(&ident) {
        format!("<a href='{}'>{}</a>", page_url(ident), ident)
    } else {
        ident.to_string()
    }
}

fn update_dependencies(env: &mut Env, idents: &[String]) {
    for ident in idents {
        if ident.chars().next().map_or(false, is_alpha) {
            env.dependencies.insert(ident.clone());
        }
    }
}

fn add_to_chapter(env: &mut Env, text: String) {
    if env.chapter_count != 0 {
        let idx = env.chapter_count - 1;
        if let Some(ch) = env.chapters.get_mut(idx) {
            ch.push(text);
        }
    }
}


// == Commands: (*/cmd ... *) ==

// A directory name must be a plain name, not a path: letters, digits, `_`,
// `-` and `.`, and it must not start with a dot (so no `.` or `..`).
fn is_plain_dir_name(name: &str) -> bool {
    !name.is_empty()
        && !name.starts_with('.')
        && name.chars().all(|c| c.is_alphanumeric() || matches!(c, '_' | '-' | '.'))
}

// TODO: Titles, headings and notes may contain raw HTML on purpose. It is
// passed through unvalidated. Add validation (e.g. an allow-list of tags and
// attributes) before sources that are not fully trusted are processed.
fn process_command(s: &[char], acc: &mut Vec<String>, env: &mut Env) -> Result<(), String> {
    let mut i = 0;
    while i < s.len() && !is_space(s[i]) {
        i += 1;
    }
    let cmd: String = s[..i].iter().collect::<String>().to_lowercase();
    let content = strip(slice(s, i + 1, s.len()));
    match cmd.as_str() {
        "chapter" => {
            env.chapter_count += 1;
            env.section_count = 0;
            let id = env.chapter_count.to_string();
            acc.push(format!("<h2 id='{}'>{}</h2>\n", id, content));
            env.toc.push(TocEntry {title: content, id, children: Vec::new()});
            env.chapters.push(Vec::new());
        }
        "section" => {
            env.subsection_count = 0;
            env.section_count += 1;
            let id = format!("{}.{}", env.chapter_count, env.section_count);
            acc.push(format!("<h3 id='{}'>{}</h3>\n", id, content));
            add_to_chapter(env, format!("<h2 id='{}'>{}</h2>\n", id, content));
            match env.toc.last_mut() {
                None => return Err(format!("Section '{}' without chapter", content)),
                Some(ch) => ch.children.push(TocEntry {title: content, id, children: Vec::new()}),
            }
        }
        "subsection" => {
            env.subsection_count += 1;
            let id = format!("{}.{}.{}", env.chapter_count, env.section_count, env.subsection_count);
            acc.push(format!("<h4 id='{}'>{}</h4>\n", id, content));
            add_to_chapter(env, format!("<h3 id='{}'>{}</h3>\n", id, content));
            let chapter = match env.toc.last_mut() {
                Some(c) => c,
                None => return Err(format!("Subsection '{}' without chapter", content)),
            };
            let sec = match chapter.children.last_mut() {
                Some(x) => x,
                None => return Err(format!("Subsection '{}' without section", content)),
            };
            sec.children.push(TocEntry {title: content, id, children: Vec::new()});
        }
        "title" => {
            env.title = Some(content);
        }
        "note" => {
            let c: Vec<char> = content.chars().collect();
            let mut k = 0;
            while k < c.len() && !is_space(c[k]) {
                k += 1;
            }
            let label: String = c[..k].iter().collect();
            let text = strip(&c[k..]);
            env.notes.insert(label, text);
        }
        "dir" => {
            if !is_plain_dir_name(&content) {
                return Err(format!(
                    "dir: '{}' is not a plain directory name \
                    (allowed: letters, digits, '_', '-', '.'; \
                    must not start with '.')", content));
            }
            env.toc_name = format!("{}-toc", content);
            env.dir_name = content;
        }
        _ => {}
    }
    Ok(())
}


// == Main parser ==
//
// Besides comments and commands the sources consist of these statements:
//
//   decl NAME: TYPE.             declaration (always documented)
//   let NAME ARGS <-> TERM.      macro; documented if it is global, i.e. not
//   let NAME ARGS = TERM.        inside a `begin` ... `end` block (blocks may
//                                be nested). Inside a block it is local and
//                                only shown as a part of the proofs.
//   begin / end                  delimit a block
//   LABEL. ASSUMPTIONS ⊢ FORMULA, JUSTIFICATION.
//                                proof step, theorem, axiom, rule, definition
//
// For `decl` and `let` everything from the name up to the terminating dot is
// taken over as it is. A dot inside brackets does not end the statement, and
// neither does the dot (or colon) behind a binder (`forall`, `exists`, `fn`,
// `∀`, `∃`) that separates the bound variable from the body; see
// `consume_term_end`.

fn extract(name: &str, s: &[char], acc: &mut Vec<String>, env: &mut Env)
-> Result<(), DocError> {
    let n = s.len();
    let mut i = 0usize;
    // Line numbers of the `begin`s that are not yet closed.
    let mut blocks: Vec<usize> = Vec::new();
    while i < n {
        if is_space(s[i]) {
            if s[i] == '\n' && i + 1 < n && s[i + 1] == '\n' {
                if !env.buf.is_empty() && !env.propose_clear {
                    env.buf.push(String::new());
                }
            }
            i += 1;
        } else if s[i] == '#' {
            i += 1;
            while i < n && s[i] != '\n' {
                i += 1;
            }
            i += 1;
        } else if s[i] == '(' && i + 1 < n && s[i + 1] == '*' {
            let comment_start = i;
            i += 2;
            let j = i;
            let cmd = i < n && s[i] == '/';
            let mut terminated = false;
            while i < n {
                if s[i] == '*' && i + 1 < n && s[i + 1] == ')' {
                    if cmd {
                        process_command(slice(s, j + 1, i), acc, env).map_err(|msg|
                            DocError::Syntax {
                                file: name.to_string(),
                                line: line_of(s, comment_start),
                                msg
                            })?;
                    }
                    i += 2;
                    terminated = true;
                    break;
                }
                i += 1;
            }
            if !terminated {
                env.warnings.push(Warning {
                    file: name.to_string(),
                    line: line_of(s, comment_start),
                    msg: "unterminated comment, the rest of the file is ignored".to_string(),
                });
            }
        } else {
            i = statement(name, s, i, &mut blocks, acc, env)?;
        }
    }
    for line in blocks {
        env.warn(name, line, "'begin' without matching 'end'");
    }
    Ok(())
}

// One statement that is neither a comment nor a command, starting at `start`:
// a keyword (`decl`, `let`, `begin`, `end`) or a proof line. Returns the
// position behind the statement.
fn statement(name: &str, s: &[char], start: usize,
    blocks: &mut Vec<usize>, acc: &mut Vec<String>, env: &mut Env
) -> Result<usize, DocError> {
    let (i, ident) = consume_ident(s, start);
    match ident.as_str() {
        "decl" => Ok(plain_item(name, s, start, i, Kind::Declaration, acc, env)),
        "let" if blocks.is_empty() => Ok(plain_item(name, s, start, i, Kind::Macro, acc, env)),
        "let" => Ok(local_macro(s, i, env)),
        "begin" => {
            if env.propose_clear {
                env.clear_proof();
            }
            blocks.push(line_of(s, start));
            Ok(i)
        }
        "end" => {
            if blocks.pop().is_none() {
                env.warn(name, line_of(s, start), "'end' without matching 'begin'");
            }
            Ok(i)
        }
        _ => sequent(name, s, start, &ident, i, acc, env)
    }
}

fn is_name_start(c: char) -> bool {
    is_alpha(c) || c == '_'
}

// `decl NAME: TYPE.` and a global `let NAME ARGS <-> TERM.`: neither has a
// justification nor a proof, and neither touches the proof being collected.
// The name is the first word after the keyword; the text shown is everything
// from the name up to the terminating dot (outside of brackets).
// `after_kw` is the position behind the keyword.
fn plain_item(file: &str, s: &[char], start: usize, after_kw: usize,
    kind: Kind, acc: &mut Vec<String>, env: &mut Env
) -> usize {
    let n = s.len();
    let kw = if kind == Kind::Macro {"let"} else {"decl"};
    let line = line_of(s, start);
    let from = consume_space(s, after_kw);
    let end = consume_term_end(s, from);
    if end >= n {
        env.warn(file, line, format!(
            "'{}' without terminating '.' (unbalanced brackets?), the rest of the file is ignored", kw));
        return n;
    }
    let (_, ident) = consume_ident(s, from);
    if !ident.chars().next().map_or(false, is_name_start) {
        env.warn(file, line, format!("'{}' without a name, ignored", kw));
        return end + 1;
    }
    let ident = match kind {
        Kind::Macro => format!("{}_macro", ident),
        _ => format!("{}_decl", ident)
    };
    register_item(env, acc, NewItem {
        file, line, kind, ident,
        text: htm_escape(&strip(slice(s, from, end))),
        proof: String::new(),
        deps: HashSet::new()
    });
    end + 1
}

// A macro inside a `begin` ... `end` block is local: it is not documented on
// its own, but shown as a part of the proof.
fn local_macro(s: &[char], after_kw: usize, env: &mut Env) -> usize {
    let j = consume_term_end(s, after_kw);
    env.buf.push(format!("let{}.", htm_escape(&slice_str(s, after_kw, j))));
    j + 1
}

// The position where the formula of a proof line starts. An optional
// assumption list ("1, 4") that is directly followed by a turnstile is
// skipped. Otherwise the formula starts right at `i`.
fn formula_start(s: &[char], i: usize) -> usize {
    let n = s.len();
    let mut k = i;
    loop {
        let (k2, _) = consume_ident(s, k);
        if k2 == k {
            break;
        }
        k = consume_space(s, k2);
        if k < n && s[k] == ',' {
            k = consume_space(s, k + 1);
        } else {
            break;
        }
    }
    let mut i0 = if k < n && s[k] == '⊢' {
        k + 1
    } else if k + 1 < n && s[k] == '|' && s[k + 1] == '-' {
        k + 2
    } else {
        i
    };
    if i0 < n && s[i0] == ' ' {
        i0 += 1;
    }
    i0
}

// A proof line `LABEL. ASSUMPTIONS ⊢ FORMULA, JUSTIFICATION.` that starts at
// `start`; `ident` is the label, `after_label` the position behind it. Lines
// with a name (not a number) are theorems, axioms, rules or definitions and
// are registered as items. Returns the position behind the line.
fn sequent(name: &str, s: &[char], start: usize, ident: &str,
    after_label: usize, acc: &mut Vec<String>, env: &mut Env
) -> Result<usize, DocError> {
    let n = s.len();
    let named = s.get(start).map_or(false, |&c| is_name_start(c));
    if is_number_above_one(ident) {
        env.propose_clear = false;
    }

    // Skip the optional dot after the label.
    let mut i = consume_space(s, after_label);
    if i < n && s[i] == '.' {
        i += 1;
    }
    i = consume_space(s, i);
    let i0 = formula_start(s, i);
    // The formula ends at the first comma on bracket level 0.
    let j = consume_until(',', s, i0);
    i = consume_space(s, j + 1);
    // The kind is given by the first word of the justification.
    let (_, word) = consume_ident(s, i);
    let kind = match word.as_str() {
        "def" => Kind::Definition,
        "axiom" => Kind::Axiom,
        "rule" => Kind::Rule,
        _ => Kind::Theorem
    };
    let idents_from = i;
    let (ni, idents) = match consume_ident_list(s, i) {
        Ok(v) => v,
        Err(pos) => {
            return Err(DocError::Syntax {
                file: name.to_string(),
                line: line_of(s, pos),
                msg: format!("unexpected character '{}' in justification list", s[pos]),
            });
        }
    };
    i = ni;
    let idents_to = i;
    i = consume_term_end(s, i) + 1;
    if env.propose_clear {
        env.clear_proof();
    }
    update_dependencies(env, &idents);
    let linked = idents.iter().map(|x| link_ident(x)).collect::<Vec<_>>().join(" ");
    env.buf.push(format!("{}{}{}",
        htm_escape(&slice_str(s, start, idents_from)),
        linked,
        htm_escape(&slice_str(s, idents_to, i))));
    if named {
        let proof = env.buf.join("\n").trim().to_string();
        let deps = env.dependencies.clone();
        register_item(env, acc, NewItem {
            file: name,
            line: line_of(s, start),
            kind,
            ident: ident.to_string(),
            text: htm_escape(&slice_str(s, i0, j)),
            proof,
            deps
        });
        env.propose_clear = true;
    }
    Ok(i)
}

// An item to be documented. `text` is HTML (already escaped) and is shown
// below the heading.
struct NewItem<'a> {
    file: &'a str,
    line: usize,
    kind: Kind,
    ident: String,
    text: String,
    proof: String,
    deps: HashSet<String>
}

// Registers an item: warns about names that are used twice, adds the box to
// the overview and to the chapter, and creates the item's own page.
fn register_item(env: &mut Env, acc: &mut Vec<String>, it: NewItem) {
    let previous = env.defined_at.get(&it.ident).cloned();
    if let Some((pfile, pline)) = previous {
        env.warn(it.file, it.line, format!(
            "duplicate name '{}' (first defined at {}:{}), the later one wins",
            it.ident, pfile, pline));
    }
    env.defined_at.insert(it.ident.to_string(), (it.file.to_string(), it.line));

    let cl = it.kind.css_class();
    let kl = it.kind.label();
    let qitem = format!(
        "<div class='box'><div class='{cl}'><b class='{cl}'>{kl}.</b> <a href='{q}'>{id}</a><br>\n{t}</div></div>\n",
        cl = cl, kl = kl, q = page_url(&it.ident), id = it.ident, t = it.text);
    let item = format!(
        "<div class='box'><div class='{cl}'><b class='{cl}'>{kl}.</b> {id}<br>\n{t}</div></div>\n",
        cl = cl, kl = kl, id = it.ident, t = it.text);
    acc.push(qitem.clone());
    env.proofs.push(Proof {
        ident: it.ident.to_string(),
        kind: it.kind,
        item,
        proof: it.proof,
        chapter: env.chapter_count
    });
    add_to_chapter(env, qitem);
    env.dep_db.insert(it.ident.to_string(), (it.kind, it.deps));
    match it.kind {
        Kind::Definition => env.def_count += 1,
        Kind::Declaration => env.decl_count += 1,
        Kind::Macro => env.macro_count += 1,
        Kind::Axiom => env.axiom_count += 1,
        Kind::Rule => env.rule_count += 1,
        Kind::Theorem => env.thm_count += 1
    }
}


// == HTML generation ==

const CSS_FONTS: &str = "\"DejaVu Sans Mono\", \"Menlo\", \"Consolas\", monospace";

const CSS_COMMON: &str = r#"pre{font-size: 12pt;}
a{color: #00304a; text-decoration: none;}
a:hover{color: #d00090; text-decoration: underline;}
p a{text-decoration: underline;}
div.box{
  border-top: 2px solid #cacac2;
  border-bottom: 2px solid #cacac2;
  margin-top: 0.5em;
  margin-bottom: 0.5em;
}
div.navi{
  border: 2px solid #cacac2;
  padding-left: 12px;
  padding-right: 12px;
  margin-bottom: 2em;
  background-color: #fafaf0;
  color: #505050;
}
div.def, div.decl, div.macro, div.thm, div.ax, div.rule{
  padding-left: 12px;
  padding-right: 12px;
  padding-top: 4px;
  padding-bottom: 4px;
  background-color: #fafaf0;
}
code{
  font: inherit;
  background-color: #e6e6e0;
  border-radius: 4px;
  padding: 0 4px;
  -webkit-box-decoration-break: clone;
  box-decoration-break: clone;
}
sub, sup{line-height: 0;}
div.def {border-left: 6px solid #006000;}
div.decl{border-left: 6px solid #006000;}
div.macro{border-left: 6px solid #006000;}
div.thm {border-left: 6px solid #000080;}
div.ax  {border-left: 6px solid #d0a000;}
div.rule{border-left: 6px solid #900060;}
b.def {color: #006000;}
b.decl{color: #006000;}
b.macro{color: #006000;}
b.thm {color: #000080;}
b.ax  {color: #d0a000;}
b.rule{color: #900060;}"#;

fn main_css() -> String {
    let mut acc = String::from("\nbody{\n  font-family: ");
    acc.push_str(CSS_FONTS);
    acc.push_str(
";
  font-size: 12pt;
  margin-left: 10%;
  margin-right: 10%;
  line-height: 1.5;
  margin-top: 2em;
  margin-bottom: 6em;
}
@media(max-width: 62em){
  body{margin-left: 6%; margin-right: 6%;}
}
@media(max-width: 52em){
  body{margin-left: 3%; margin-right: 3%;}
}\n");
    acc.push_str(CSS_COMMON);
    acc.push('\n');
    acc
}

fn list_css() -> String {
    let mut acc = String::from("\nbody{\n  font-family: ");
    acc.push_str(CSS_FONTS);
    acc.push_str(
";
  font-size: 12pt;
  margin-left: 6%;
  margin-right: 6%;
  line-height: 1.5;
  margin-top: 2em;
  margin-bottom: 6em;
}
@media(max-width: 56em){
  body{margin-left: 3%; margin-right: 3%;}
}\n");
    acc.push_str(CSS_COMMON);
    acc.push('\n');
    acc
}

const JS_CODE: &str = r#"
const input = document.getElementById('input');
const results = document.getElementById('results');

// The same escaping as for the file names: a capital letter becomes ~ and
// the small letter.
function page_name(entry) {
    return entry.replace(/\p{Uppercase}/gu, c => '~' + c.toLowerCase()) + '.htm';
}

function show_entrys(entrys) {
    results.innerHTML = '';
    if (entrys.length === 0) {
        results.innerHTML = '<div>No results</div>';
        return;
    }
    const list = document.createElement('div');
    var first = true;
    entrys.forEach(entry => {
        if (first) {first = false;}
        else {list.appendChild(document.createElement('br'));}
        const link = document.createElement('a');
        link.textContent = entry;
        link.href = encodeURIComponent(page_name(entry));
        list.appendChild(link);
    });
    results.appendChild(list);
}

function search() {
    const search_term = input.value.trim();
    if (search_term.length === 0) {
        results.innerHTML = '';
        return;
    }
    const filtered = data.filter(
        entry => entry.includes(search_term));
    show_entrys(filtered);
}

input.addEventListener('keyup', function(event) {
    if (event.key === 'Enter') {search();}
});
"#;

fn header(acc: &mut Vec<String>, path: Option<&str>, title: &str) {
    let css_file = match path {
        Some(p) => format!("{}/list.css", p),
        None => "list.css".to_string(),
    };
    acc.push(format!(
"<!DOCTYPE html>
<html>
<head>
  <meta charset=\"UTF-8\">
  <title>{}</title>
  <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">
  <link href=\"{}\" rel=\"stylesheet\">
</head>
<body>\n",
        title, css_file));
}

fn footer(acc: &mut Vec<String>) {
    acc.push("</body>\n</html>".to_string());
}

fn sublist(a: &[TocEntry]) -> String {
    if a.is_empty() {
        return String::new();
    }
    let mut acc = String::from("<ol>\n");
    for x in a {
        acc.push_str(&format!("<li><a href='#{}'>{}</a>{}\n", x.id, x.title, sublist(&x.children)));
    }
    acc.push_str("</ol>");
    acc
}

fn table_of_contents(toc: &[TocEntry]) -> String {
    if toc.is_empty() {
        String::new()
    } else {
        format!("<h2>Table of contents</h2>\n{}\n", sublist(toc))
    }
}

// Axioms a theorem depends on (transitively through theorems).
fn depends_on_axioms<'a>(
    ident: &'a str,
    dep_db: &'a HashMap<String, (Kind, HashSet<String>)>,
) -> BTreeSet<&'a str> {
    let mut axioms: BTreeSet<&str> = BTreeSet::new();
    let mut visited: HashSet<&str> = HashSet::new();
    let mut stack: Vec<&str> = vec![ident];
    visited.insert(ident);
    while let Some(cur) = stack.pop() {
        let (kind, deps) = match dep_db.get(cur) {
            Some(e) => (e.0, &e.1),
            None => continue,
        };
        if kind != Kind::Theorem {
            continue;
        }
        for x in deps {
            if let Some(entry) = dep_db.get(x.as_str()) {
                if entry.0 == Kind::Axiom {
                    axioms.insert(x.as_str());
                }
                if visited.insert(x.as_str()) {
                    stack.push(x.as_str());
                }
            }
        }
    }
    axioms
}

fn number_as_word(n: usize) -> String {
    match n {
        1 => "one".to_string(),
        2 => "two".to_string(),
        3 => "three".to_string(),
        4 => "four".to_string(),
        5 => "five".to_string(),
        6 => "six".to_string(),
        7 => "seven".to_string(),
        8 => "eight".to_string(),
        9 => "nine".to_string(),
        _ => n.to_string(),
    }
}

// Formats a note (documentation comment) as a paragraph.
fn format_text(text: &str) -> String {
    let s: Vec<char> = text.chars().collect();
    format!("<p>{}</p>\n", format_inline(&s))
}

// Markup of notes:
//  * `[[name]]`, `[[name|text]]`  link to an item
//  * `\_`                         non-breaking space
//  * `` `text` ``                 `<code>` (formulas); the content is formatted
//                                 recursively, so `<sub>` and links work in it
//  * `` \` ``                     a literal backtick; an unmatched backtick
//                                 is also kept as text
//  * `<tag ...>`, `</tag>`        raw HTML (see the TODO at `process_command`)
//  * `<`, `>`, `&`                escaped, unless they start a tag or an entity
fn format_inline(s: &[char]) -> String {
    let n = s.len();
    let mut acc = String::new();
    let mut i = 0;
    while i < n {
        if s[i] == '`' {
            // Find the closing backtick, skipping escaped ones.
            let mut j = i + 1;
            while j < n && s[j] != '`' {
                j += if s[j] == '\\' && j + 1 < n && s[j + 1] == '`' { 2 } else { 1 };
            }
            if j < n {
                acc.push_str("<code>");
                acc.push_str(&format_inline(slice(s, i + 1, j)));
                acc.push_str("</code>");
                i = j + 1;
            } else {
                acc.push('`');
                i += 1;
            }
        } else if s[i] == '\\' && i + 1 < n && s[i + 1] == '`' {
            acc.push('`');
            i += 2;
        } else if s[i] == '[' && i + 1 < n && s[i + 1] == '[' {
            i += 2;
            let mut j = i;
            let mut reference: Option<String> = None;
            while i < n && s[i] != ']' {
                if s[i] == '|' {
                    reference = Some(slice_str(s, j, i));
                    j = i + 1;
                }
                i += 1;
            }
            match reference {
                None => {
                    let r = slice_str(s, j, i);
                    acc.push_str(&format!("<a href='{}'>{}</a>", page_url(&r), r));
                }
                Some(r) => {
                    let t = slice_str(s, j, i);
                    acc.push_str(&format!("<a href='{}'>{}</a>", page_url(&r), t));
                }
            }
            i += 2;
        } else if s[i] == '\\' && i + 1 < n && s[i + 1] == '_' {
            acc.push_str("&nbsp;");
            i += 2;
        } else if s[i] == '<' && i + 1 < n && (is_alpha(s[i + 1]) || s[i + 1] == '/') {
            let j = i;
            while i < n && s[i] != '>' {
                i += 1;
            }
            i += 1;
            acc.push_str(&slice_str(s, j, i));
        } else if s[i] == '<' {
            acc.push_str("&lt;");
            i += 1;
        } else if s[i] == '>' {
            acc.push_str("&gt;");
            i += 1;
        } else if s[i] == '&' && i + 1 < n && !is_alpha(s[i + 1]) {
            acc.push_str("&amp;");
            i += 1;
        } else {
            acc.push(s[i]);
            i += 1;
        }
    }
    acc
}

fn proof_file(env: &Env, p: &Proof) -> String {
    let text = if p.kind == Kind::Theorem {
        format!("<pre><b>Proof</b>\n{}\n</pre>", p.proof)
    } else {
        String::new()
    };
    let axioms = depends_on_axioms(&p.ident, &env.dep_db);
    let axiom_deps = if !axioms.is_empty() {
        let n = axioms.len();
        let links: Vec<String> = axioms
            .iter()
            .map(|x| format!("<a href='{}'>{}</a>", page_url(x), x))
            .collect();
        let links = links.join(", ");
        let axiom_count = if n == 1 { "one axiom".to_string() } else { format!("{} axioms", number_as_word(n)) };
        format!(
            "\n<p><b>Dependencies</b><br>The given proof depends on {}:<br>{}.</p>",
            axiom_count, links
        )
    } else {
        String::new()
    };
    let notes_text = match env.notes.get(&p.ident) {
        Some(t) => format_text(t),
        None => String::new(),
    };
    let navi = format!(
        "<div class='navi'><a href='chapter-{}.htm'>Up</a> | <a href='search.htm'>Search</a></div>",
        p.chapter
    );
    format!(
"<!DOCTYPE html>
<html>
<head>
  <meta charset=\"UTF-8\">
  <title>{ident}</title>
  <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">
  <link href=\"main.css\" rel=\"stylesheet\">
</head>
<body>
{navi}
<h3>{kind} {ident}</h3>
{item}{notes}{text}{deps}
</body>
</html>",
        ident = p.ident,
        navi = navi,
        kind = p.kind.label(),
        item = p.item,
        notes = notes_text,
        text = text,
        deps = axiom_deps)
}

fn toc_file(env: &Env) -> OutFile {
    let dir = env.dir_name.as_str();
    let mut acc: Vec<String> = Vec::new();
    header(&mut acc, Some(dir), "Contents");
    acc.push(format!("{}\n", TOC_MARKER));
    acc.push(format!("<div class='navi'><a href='{}/{}.htm'>All items</a>", dir, ALL_ITEMS_NAME));
    acc.push(format!(" | <a href='{}/search.htm'>Search</a></div>\n", dir));
    if let Some(t) = &env.title {
        acc.push(format!("<h1>{}</h1>\n", t));
    }
    acc.push("<h2>Table of contents</h2>\n".to_string());
    acc.push("<ol>\n".to_string());
    for x in &env.toc {
        acc.push(format!("<li><a href='{}/chapter-{}.htm'>{}</a>\n", dir, x.id, x.title));
    }
    acc.push("</ol>\n".to_string());
    footer(&mut acc);
    OutFile {
        path: format!("{}.htm", env.toc_name),
        content: acc.concat(),
        kind: OutFileKind::RootToc
    }
}

fn chapter_toc_file(env: &Env, i: usize) -> OutFile {
    let mut acc: Vec<String> = Vec::new();
    header(&mut acc, None, &format!("Chapter {}", i + 1));
    acc.push(format!(
        "<div class='navi'><a href='../{}.htm'>Up</a> | <a href='search.htm'>Search</a></div>\n",
        env.toc_name
    ));
    acc.push(format!("<h1>{}</h1>\n", env.toc[i].title));
    acc.push(table_of_contents(&env.toc[i].children));
    acc.push(env.chapters[i].concat());
    footer(&mut acc);
    OutFile {
        path: format!("{}/chapter-{}.htm", env.dir_name, i + 1),
        content: acc.concat(),
        kind: OutFileKind::DocAsset
    }
}

fn search_page(env: &Env) -> OutFile {
    let mut items: Vec<&str> = env.proofs.iter().map(|p| p.ident.as_str()).collect();
    items.sort();
    let json = format!(
        "[{}]",
        items.iter().map(|x| json_string(x)).collect::<Vec<_>>().join(", ")
    );
    let mut acc: Vec<String> = Vec::new();
    header(&mut acc, None, "Search");
    acc.push(format!("<div class='navi'><a href='{}.htm'>All items</a>", ALL_ITEMS_NAME));
    acc.push(format!(" | <a href='../{}.htm'>Table of contents</a></div>\n", env.toc_name));
    acc.push("<h2>Search</h2>\n".to_string());
    acc.push("<input type='button' value='Search' onclick='search()'>".to_string());
    acc.push("<input type='text' id='input' style='width: 20em'><br>\n<br>\n".to_string());
    acc.push("<div id='results'></div>\n".to_string());
    acc.push(format!("<script>const data = {};{}</script>", json, JS_CODE));
    footer(&mut acc);
    OutFile {
        path: format!("{}/search.htm", env.dir_name),
        content: acc.concat(),
        kind: OutFileKind::DocAsset
    }
}

pub fn doc_main(names: &[String]) -> Result<(), ()> {
    let mut sources: Vec<Source> = Vec::new();
    for name in names {
        match fs::read_to_string(&name) {
            Ok(text) => sources.push(Source {name: name.clone(), text}),
            Err(e) => {
                eprintln!("{}: {}", name, e);
                return Err(());
            }
        }
    }
    let site = match generate(&sources) {
        Ok(site) => site,
        Err(e) => {
            eprintln!("error: {}", e);
            return Err(());
        }
    };
    for w in &site.warnings {
        eprintln!("{}", w);
    }
    if let Err(e) = site.write_to(Path::new(".")) {
        eprintln!("error: {}", e);
        return Err(());
    }
    Ok(())
}
