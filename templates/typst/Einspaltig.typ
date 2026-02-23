
#set text(lang: "de")
#set page(margin: (inside: 30mm, outside: 25mm))
#set page(numbering: "1 / 1")
#set text(size: 11pt)
#set par(justify: true, first-line-indent: 1em, spacing: 0.65em)
#show math.equation: set text(font: "Libertinus Math")
#show math.equation.where(block: true): pad.with(left: 3em)
#show math.equation.where(block: true): set align(left)

#set heading(numbering: "1.1")
#show outline.entry.where(level: 1): set text(weight: "bold")

#set document(title: [Ententheorie], author: "Donald Duck")
#let date = "1. Jan. 2000"

#align(center, block[
  #title()
  #text(size: 12pt, {
    context document.author.join("; ")
    linebreak(); date
  })])

#outline()

= Abschnitt
== Unterabschnitt
=== Unterunterabschnitt

#lorem(100)

$ sum_(k=1)^n k = n/2 (n+1) $

#lorem(200)

#lorem(350)

#lorem(400)
