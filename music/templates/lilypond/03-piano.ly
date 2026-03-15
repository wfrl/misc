\version "2.24.3"

\paper {
  top-margin = 60\mm
  left-margin = 20\mm
  right-margin = 20\mm
  bottom-margin = 20\mm
}

\header {
  title = "Steter Regen, fahle Lichter"
  subtitle = "in cis-Moll"
  composer = "Grauchen"
  tagline = ##f
}

\markup \vspace #1

upper = \fixed c'' {
  \clef treble
  \key cis\minor
  \numericTimeSignature
  \time 6/8
  \tempo 4 = 60
  e8 e8 e8 e8^\mp e8 e8 | dis8 (e8 fis8 gis4.) |
  <e cis'>8 (gis8 e8 fis4.) | <dis fis>8 (<dis gis>8 <dis b>8 gis4.) |
  fis8 fis8 fis8 fis8 fis8 fis8 | e4.~e4. \bar "|."
}

lower = \fixed c' {
  \clef bass
  \key cis\minor
  \time 6/8
  <a, e>4. e4. | <gis, fis>4. fis4. |
  <a, e>4. e4. | <gis, fis>16 fis16~fis4 fis4. |
  <a, e>4. e4. | <gis, fis>4.~<gis, fis>4.
}

\score {
  \new PianoStaff
  <<
    \new Staff \upper
    \new Staff \lower
  >>
  \layout {indent = 0\mm}
  \midi {}
}
