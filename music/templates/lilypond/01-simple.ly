\version "2.24.3"

\paper {
  top-margin = 60\mm
  left-margin = 20\mm
  right-margin = 20\mm
  bottom-margin = 20\mm
}

\header {
  title = "De Krebbel"
  composer = "Flanders, late 19th century"
  tagline = ##f
}

\markup \vspace #1

melody = \fixed c' {
  \key e\minor
  \repeat volta 2 {
    e8 g8 e8 g8 | fis8 d8 d4 | e8 g8 e8 g8 | a4 a4 |
    b8 b8 a8 a8 | g8 g8 fis8 fis8 | e8 e8 d8 d8 | e4 r4
  }\break
  \repeat volta 2 {
    e'8 e'8 b4 | e'8 e'8 b4 | g'8 g'8 fis'8 fis'8 | e'8 e'8 d'8 d'8 |
    e'8 e'8 b4 | a8 a8 b8 b8 | e4 r4
  }
}

\score {
  \new Staff {
    \numericTimeSignature
    \time 2/4
    \tempo 4 = 110
    \melody
  }
  \layout {indent = 0\mm}
  \midi {}
}

