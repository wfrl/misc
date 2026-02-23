// =====================================================================
// FORMAT UND DEFINITIONEN
// =====================================================================

#let debug = true
#let debug-fg = purple
#let debug-bg = if debug {rgb(250,180,250)} else {none}

#let fonts = (
  l: (10pt, "Lato"),
  c: (11pt, "Carlito"),
  s: (11pt, "Source Sans 3"),
  d: ( 9pt, "DejaVu Sans"),
  m: ( 9pt, "DejaVu Sans Mono"),
  b: (11pt, "Linux Biolinum O"),
  a: (10pt, "Andika"),
  h: (10pt, "FreeSans"),
  u: (10pt, "Unifont")
)
#let main-font = fonts.at("l")
#let tech-font = (9pt, "DejaVu Sans Mono")
#let mono-font = (9pt, "DejaVu Sans Mono")

#let leading = 0.75em
#set par(leading: leading)
#set par(justify: true)
// #set par(first-line-indent: 1em)
// #set par(spacing: 0.65em)
#set par(spacing: 1.4em)

#set text(lang: "de")
#set text(size: main-font.at(0), font: main-font.at(1))
#show raw: set text(size: mono-font.at(0), font: mono-font.at(1))
// #set text(features: ("onum",))
#set page(margin: (left: 25mm, right: 25mm, top: 25mm, bottom: 30mm))
#set page(numbering: "1 / 1")
#let fm-stroke = 0.6pt
#set page(
  background: place(left + top, dx: 5mm)[  
    // Obere Falzmarke
    #place(top, dy: 105mm, line(length: 3mm, stroke: fm-stroke))
    // Lochmarke
    #place(top, dy: 148.5mm, line(length: 5mm, stroke: fm-stroke))
    // Untere Falzmarke
    #place(top, dy: 210mm, line(length: 3mm, stroke: fm-stroke))
    
    #if debug {place(top + left, dx: 20mm - 5mm,  dy: 45mm,
      rect(
        width: 90mm, height: 45mm,
        stroke: 1pt + debug-fg, radius: 4mm,
        stack(
          rect(width: 100%, height: 17.7mm,
            stroke: (bottom: 1pt + debug-fg)),
          rect(width: 100%, height: 27.3mm, stroke: none))))}
    #if debug {place(top + left, dx: 20mm - 5mm, dy: 25mm, [
      #text(size: 24pt, fill: debug-fg)[*[Debug-Modus]*]\
      #text(fill: debug-fg)[Die x-Höhen:
        Main #sym.arrow abx`xba` #sym.arrow.l `Mono`\
        0123456789 abcd efgh ijkl mnop qrst uvw xyz]])}])

#let header(sender: "", sender-small: "", recipient: "",
  date: "", info: (), info-dense: false, info-small: true,
) = {
  {
    set text(size: tech-font.at(0), font: tech-font.at(1))
    set par(first-line-indent: 0em)
    v(5mm); h(1fr); box(height: 24mm, fill: debug-bg, sender)
    v(-5mm)
    box(height: 10mm, fill: debug-bg,
      text(size: 7/9*tech-font.at(0),
        underline(offset: 2pt, stroke: 0.6pt,
          sender-small)))
    v(0mm); box(height: 20mm, width: 80mm, fill: debug-bg, recipient);
    h(1fr); box(height: 20mm, fill: debug-bg,
      text(size: if info-small {8/9*tech-font.at(0)}
        else {tech-font.at(0)},
        if info-dense {
          stack(spacing: leading,
            ..info.chunks(2).map(t => t.join([~])))
        }else {
          table(columns: 2, align: (right, left),
            stroke: none, inset: 0pt, gutter: leading, ..info)
        }))
  }
  if date != "" {v(0mm); h(1fr); box(date)}
}
#let subject(x) = {v(1em); block[*#x*]}
#let closing(text, sig) = {
  v(1.2em); text; parbreak(); sig
}

// =====================================================================
// INHALT
// =====================================================================

#header(
  sender:
    [Donald Duck\
    Am Geldspeicher 1\
    12345 Entenhausen\
    Tel.: 0123 4567],
  sender-small:
    [Donald Duck, Am Geldspeicher 1, 12345 Entenhausen],
  recipient: 
    [Hase und Igel\
    Rennbahn 1\
    98765 Fabelwald],
  date: [1.~Jan.~2000],
  info: (
    [Ihr Zeichen:], [Akte-X-0000-0000],
    [Ihre Nachricht vom:], [1.~Jan.~2000],
    [Mein Zeichen:], [Akte-Y-0000-0000],
    [Meine Nachricht vom:], [1.~Jan.~2000]),
  info-dense: false, info-small: true)

#subject[Betreffzeile]

Sehr geehrte Damen und Herren,

#lorem(40)

#lorem(50)

#lorem(50)

#closing([Mit freundlichen Grüßen],
[Donald Duck, 1. Jan. 2000])

