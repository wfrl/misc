\version "2.24.3"

\paper {
  top-margin = 40\mm
  left-margin = 20\mm
  right-margin = 20\mm
  bottom-margin = 20\mm
}

\header {
  title = "Auld Lang Syne"
  composer = \markup\right-column {
    "Music: Scotland"
    "Lyrics: Robert Burns (1788)"
  }
  tagline = ##f
}

\markup \vspace #1

melody = \fixed c' {
  \key g\major
  d4 | g4. g8 g4 b4 | a4. g8 a4 b4 | g4. g8 b4 d'4 | e'2 r4 \break
  e'4 | d'4. b8 b4 g4 | a4. g8 a4 b4 | g4. (e8) e4 (d4) | g2 r4 \break

  \sectionLabel\markup{\bold\normalsize "Refrain"}
  e'4 | d'4. (b8) b4 (g4) | a4. g8 a4 e'4 | d'4. (b8) b4 (d'4) | e'2 r4 \break
  g'4 | d'4. b8 b4 g4 | a4. g8 a4 b8. a16 | g4. (e8) e4 (d4) | g2. r4\bar "|."
}

accompaniment = {\transpose g g, {\chordmode {
  % \set chordNameLowercaseMinor = ##t
  \set noChordSymbol = ##f
  % \once \omit ChordNames.ChordName
  r4 | g2 g2/b | c'2 d'2 | g2/b g2 | c'1
     | g2/b e2:m | a2:m/c' d'2 | e2:m c'4 d'4 | g2 c'2
     | g2/b e2:m | a2:m/c' d'2 | g2/b g2:7 | c'1
     | g2/b e2:m | a2:m/c' d'2 | e2:m c'4 d'4 | g2. r4
}}}

text = \lyricmode {
  \set stanza = #"1. "
  Should auld ac -- quain -- tance be for -- got,
  and ne -- ver brought to mind?
  Should auld ac -- quain -- tance be for -- got,
  and auld __ lang __ syne?
  For auld __ lang __ syne my dear,
  for auld __ lang __ syne,
  we'll take a cup o' kind -- ness yet,
  for __ _ auld __ lang __ syne.
}

\score{
  <<
    \new ChordNames \accompaniment
    \new Staff {
      \numericTimeSignature
      \time 4/4
      \tempo 4 = 80
      \partial 4 % Length of pickup beat (Länge des Auftakts)
      \melody
    }
    \addlyrics {\text}
  >>
  \layout {indent = 0\mm}
  \midi {}
}

\markup {
  \vspace #3
  \fill-line {
    % \hspace #10.0
    \large\column {
      \line {\bold "2."\hspace #1.0
        \column {
          "And there's a hand, my trusty friend, and gie's a hand o'thine,"
          "we'll take a cup of kindness yet for the sake of auld lang syne."
        }
      }
      \vspace #1
      \line {\bold "3."\hspace #1.0
        \column {
          "And surely you'll buy your pint cup! and surely I'll buy mine!"
          "And we'll take a cup o' kindness yet, for auld lang syne."
        }
      }
      \vspace #1
      \line {\bold "4."\hspace #1.0
        \column {
          "We two have run about the hills, and picked the daisies fine;"
          "But we've wandered many a weary foot, since auld lang syne."
        }
      }
      \vspace #1
      \line {\bold "5."\hspace #1.0
        \column {
          "We two have paddled in the stream, from morning sun till dine;"
          "But seas between us broad have roared since auld lang syne."
        }
      }
      \vspace #1
      \line {\bold "6."\hspace #1.0
        \column {
          "And there's a hand my trusty friend! And give me a hand o' thine!"
          "And we'll take a right good-will draught, for auld lang syne."
        }
      }
    }
  }
}
