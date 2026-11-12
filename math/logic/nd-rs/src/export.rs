
use crate::kernel::{
    is_utf8_continuation_byte, mb_is_alpha, unicode_identifier
};

// == 1. Auxiliary functions for unicode and identifiers ==

// Checks if an identifier can begin at position `i` (excludes digits).
fn can_start_ident(s: &[u8], i: usize, n: usize) -> bool {
    if i >= n {
        return false;
    }
    let b = s[i];
    if b.is_ascii_alphabetic() || b == b'_' {
        true
    } else if b > 127 {
        let mut next = i + 1;
        while next < n && is_utf8_continuation_byte(s[next]) {
            next += 1;
        }
        mb_is_alpha(&s[i..next])
    } else {
        false
    }
}

// Checks a keyword at position `pos` taking word boundaries into account.
fn is_word(s: &[u8], pos: usize, word: &[u8], n: usize) -> bool {
    let wl = word.len();
    if pos + wl <= n && &s[pos..pos + wl] == word {
        pos + wl == n || unicode_identifier(s, pos + wl, n) == pos + wl
    } else {
        false
    }
}

// == 2. Auxiliary functions for whitespaces and comments ==

// Skips a line (`# ...`) or block comment (`(* ... *)`).
fn skip_comment(s: &[u8], mut i: usize, n: usize) -> usize {
    if i + 1 < n && s[i] == b'(' && s[i + 1] == b'*' {
        i += 2;
        while i < n {
            if i + 1 < n && s[i] == b'*' && s[i + 1] == b')' {
                return i + 2;
            }
            i += 1;
        }
        return n;
    }
    if i < n && s[i] == b'#' {
        while i < n && s[i] != b'\n' {
            i += 1;
        }
        return i;
    }
    i
}

// Skips whitespaces and comments up to the next token.
fn skip_ws_and_comments(s: &[u8], mut i: usize, n: usize) -> usize {
    while i < n {
        if matches!(s[i], b' ' | b'\t' | b'\r' | b'\n') {
            i += 1;
            continue;
        }
        let after_c = skip_comment(s, i, n);
        if after_c != i {
            i = after_c;
            continue;
        }
        break;
    }
    i
}

// == 3. Statement parsers (macros, proof steps, theorems) ==

// Checks whether a binder symbol, a binder keyword,
// or any other identifier begins at position `pos`.
// Returns `Some((is_binder, next_pos))`.
fn check_binder_or_ident(s: &[u8], pos: usize, n: usize) -> Option<(bool, usize)> {
    // Unicode symbols (∀ = \u{2200}, ∃ = \u{2203}, 3 UTF-8 bytes each)
    if pos + 3 <= n {
        let sym = &s[pos..pos + 3];
        if sym == "∀".as_bytes() || sym == "∃".as_bytes() {
            return Some((true, pos + 3));
        }
    }

    // Textual identifiers / keywords
    if can_start_ident(s, pos, n) {
        let end = unicode_identifier(s, pos, n);
        let word = &s[pos..end];
        let is_binder = matches!(word, b"forall" | b"exists" | b"fn");
        return Some((is_binder, end));
    }

    None
}

// Tries to parse a `let` macro. Returns the end index (after '.') on success.
// Tries to parse a `let` macro or `decl`. Returns the end index (after '.') on success.
fn try_parse_extra(s: &[u8], i: usize, n: usize, keyword: &[u8]) -> Option<usize> {
    if !is_word(s, i, keyword, n) {
        return None;
    }
    let l = keyword.len();
    if i + l >= n || !matches!(s[i + l], b' ' | b'\t' | b'\r' | b'\n') {
        return None;
    }

    let mut c = i + l;
    let mut bracket_level: usize = 0;
    let mut binder_active = false;

    while c < n {
        let next_c = skip_comment(s, c, n);
        if next_c != c {
            c = next_c;
            continue;
        }

        // Detect and skip binders and identifiers
        if let Some((is_binder, next_pos)) = check_binder_or_ident(s, c, n) {
            if is_binder && bracket_level == 0 {
                binder_active = true;
            }
            c = next_pos;
            continue;
        }

        let cb = s[c];
        if matches!(cb, b'{' | b'(' | b'[') {
            bracket_level += 1;
        } else if matches!(cb, b'}' | b')' | b']') {
            bracket_level = bracket_level.saturating_sub(1);
        } else if cb == b':' && bracket_level == 0 && binder_active {
            binder_active = false;
        } else if cb == b'.' && bracket_level == 0 {
            if binder_active {
                binder_active = false;
            } else {
                return Some(c + 1);
            }
        }
        c += 1;
    }

    None
}

// Skips a proof step (`<Digits>. ... ⊢/|- ... , ... .`).
fn try_skip_proof_step(s: &[u8], i: usize, n: usize) -> Option<usize> {
    if !s[i].is_ascii_digit() {
        return None;
    }
    let mut curr = i;
    while curr < n && s[curr].is_ascii_digit() {
        curr += 1;
    }
    while curr < n && matches!(s[curr], b' ' | b'\t') {
        curr += 1;
    }
    if curr >= n || s[curr] != b'.' {
        return None;
    }

    let mut c = curr + 1;

    // 1. Find turnstile: |- or ⊢
    let mut found_turnstile = false;
    while c < n {
        let next_c = skip_comment(s, c, n);
        if next_c != c {
            c = next_c;
            continue;
        }
        if c + 2 <= n && &s[c..c + 2] == b"|-" {
            c += 2;
            found_turnstile = true;
            break;
        } else if c + 3 <= n && &s[c..c + 3] == "⊢".as_bytes() {
            c += 3;
            found_turnstile = true;
            break;
        }
        c += 1;
    }
    if !found_turnstile {
        return None;
    }

    // 2. Find comma before the justification (at bracket depth 0)
    let mut bracket_level: usize = 0;
    let mut found_comma = false;
    while c < n {
        let next_c = skip_comment(s, c, n);
        if next_c != c {
            c = next_c;
            continue;
        }
        let cb = s[c];
        if matches!(cb, b'{' | b'(' | b'[') {
            bracket_level += 1;
        } else if matches!(cb, b'}' | b')' | b']') {
            bracket_level = bracket_level.saturating_sub(1);
        } else if cb == b',' && bracket_level == 0 {
            found_comma = true;
            c += 1;
            break;
        }
        c += 1;
    }
    if !found_comma {
        return None;
    }

    // 3. Find concluding period of the justification (at bracket depth 0)
    let mut bracket_just: usize = 0;
    while c < n {
        let next_c = skip_comment(s, c, n);
        if next_c != c {
            c = next_c;
            continue;
        }
        let eb = s[c];
        if matches!(eb, b'{' | b'(' | b'[') {
            bracket_just += 1;
        } else if matches!(eb, b'}' | b')' | b']') {
            bracket_just = bracket_just.saturating_sub(1);
        } else if eb == b'.' && bracket_just == 0 {
            return Some(c + 1);
        }
        c += 1;
    }

    None
}

// Tries to parse a theorem / axiom / definition.
// Returns `(comma_idx, tail, end_pos)` on success.
fn try_parse_theorem(s: &[u8], i: usize, n: usize) -> Option<(usize, &'static [u8], usize)> {
    if !can_start_ident(s, i, n) {
        return None;
    }
    let mut curr = unicode_identifier(s, i, n);
    while curr < n && matches!(s[curr], b' ' | b'\t') {
        curr += 1;
    }
    if curr >= n || s[curr] != b'.' {
        return None;
    }

    let mut c = curr + 1;
    let mut bracket_level: usize = 0;
    let mut comma_idx = None;

    while c < n {
        let next_c = skip_comment(s, c, n);
        if next_c != c {
            c = next_c;
            continue;
        }
        let cb = s[c];
        if cb == b',' && bracket_level == 0 {
            comma_idx = Some(c);
            break;
        } else if matches!(cb, b'{' | b'(' | b'[') {
            bracket_level += 1;
        } else if matches!(cb, b'}' | b')' | b']') {
            bracket_level = bracket_level.saturating_sub(1);
        }
        c += 1;
    }

    let comma_pos = comma_idx?;

    // Evaluate justification (def / axiom)
    let mut k = comma_pos + 1;
    while k < n && matches!(s[k], b' ' | b'\t' | b'\r' | b'\n') {
        k += 1;
    }

    let tail: &'static [u8] = if is_word(s, k, b"def", n) {
        b"def"
    } else {
        b"axiom"
    };

    // Find concluding period of the justification
    let mut end_pos = comma_pos + 1;
    let mut bracket_just: usize = 0;
    while end_pos < n {
        let next_e = skip_comment(s, end_pos, n);
        if next_e != end_pos {
            end_pos = next_e;
            continue;
        }
        let eb = s[end_pos];
        if matches!(eb, b'{' | b'(' | b'[') {
            bracket_just += 1;
        } else if matches!(eb, b'}' | b')' | b']') {
            bracket_just = bracket_just.saturating_sub(1);
        } else if eb == b'.' && bracket_just == 0 {
            return Some((comma_pos, tail, end_pos + 1));
        }
        end_pos += 1;
    }

    None
}

// == 4. Main export function ==

pub fn export_named(s: &[u8]) -> Vec<u8> {
    let n = s.len();
    let mut acc = Vec::new();
    let mut i = 0;
    let mut scope_depth: usize = 0;

    while i < n {
        i = skip_ws_and_comments(s, i, n);
        if i >= n {
            break;
        }

        // 1. Local scopes: "begin" / "end"
        if is_word(s, i, b"begin", n) && (i + 5 == n || s[i + 5] != b'.') {
            scope_depth += 1;
            i += 5;
            continue;
        }
        if is_word(s, i, b"end", n) && (i + 3 == n || s[i + 3] != b'.') {
            scope_depth = scope_depth.saturating_sub(1);
            i += 3;
            continue;
        }

        // 2. Macros: "let ..." (export globally only)
        if let Some(end_pos) = try_parse_extra(s, i, n, b"let") {
            if scope_depth == 0 {
                if !acc.is_empty() {
                    acc.push(b'\n');
                }
                acc.extend_from_slice(&s[i..end_pos]);
            }
            i = end_pos;
            continue;
        }
        
        // 3. Declarations: "decl name: Type."
        if let Some(end_pos) = try_parse_extra(s, i, n, b"decl") {
            if !acc.is_empty() {
                acc.push(b'\n');
            }
            acc.extend_from_slice(&s[i..end_pos]);
            i = end_pos;
            continue;
        }

        // 4. Proof steps (strip)
        if let Some(next_i) = try_skip_proof_step(s, i, n) {
            i = next_i;
            continue;
        }

        // 5. Theorems / axioms / definitions (export)
        if let Some((comma_idx, tail, end_pos)) = try_parse_theorem(s, i, n) {
            if !acc.is_empty() {
                acc.push(b'\n');
            }
            acc.extend_from_slice(&s[i..comma_idx]);
            acc.extend_from_slice(b", ");
            acc.extend_from_slice(tail);
            acc.push(b'.');

            i = end_pos;
            continue;
        }

        // If no pattern matches, move forward character by character.
        // Might alternatively throw an error.
        i += 1;
    }

    acc
}
