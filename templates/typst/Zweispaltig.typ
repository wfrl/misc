
#set text(lang: "de")
#set page(margin: (inside: 25mm, outside: 15mm))
#set page(columns: 2)
#set columns(gutter: 14pt)
#set page(numbering: "1 / 1")
#set text(size: 10pt)
#set par(justify: true, first-line-indent: 1em, spacing: 0.65em)
#show math.equation: set text(font: "Libertinus Math")
#show math.equation.where(block: true): pad.with(left: 2em)
#show math.equation.where(block: true): set align(left)

#set heading(numbering: "1.1")
#show outline.entry.where(level: 1): set text(weight: "bold")

#set document(title: [Ententheorie], author: "Donald Duck")
#let date = "1. Jan. 2000"

#title()
#text(size: 12pt, {
  context document.author.join("; ")
  linebreak(); date})

#outline()

= Abschnitt
== Unterabschnitt
=== Unterunterabschnitt

#lorem(50)

$ sum_(k=1)^n k = n/2 (n+1) $

#lorem(50)

#lorem(200)

#lorem(600)

#lorem(600)
