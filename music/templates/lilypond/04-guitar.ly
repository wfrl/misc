\version "2.24.3"

\paper {
  top-margin = 60\mm
  left-margin = 20\mm
  right-margin = 20\mm
  bottom-margin = 20\mm
}

\header {
  title = "Opus 1"
  composer = "wfrl"
  tagline = ##f
}

\markup \vspace #1

upper = \fixed c {
  \voiceOne
  <g d'>4 <g d'>4 e8 g8 d'4 | fis'8 g8 b8 fis'2 fis'8 |
  g'8 b8\rest g'2 g'4 | a'8 b8 a'8 b'2 b8\rest \bar "|."
}

lower = \fixed c {
  \voiceTwo
  c4 c4 s2 | d8 s8 s8 d2 d8 |
  e8 s8 e2 e4 | g8_\4 s8 s8 g2_\4 s8 \bar "|."
}

\score {
  <<
    \new Staff <<
      \clef "treble_8"
      \numericTimeSignature
      \time 4/4
      \tempo 4 = 120
      \key g\major
      \new Voice = "upper" \upper
      \new Voice = "lower" \lower
    >>
    \new TabStaff <<
      \new TabVoice = "upper" \upper
      \new TabVoice = "lower" \lower
    >>
  >>
  \layout {indent = 0\mm}
  \midi {}
}
