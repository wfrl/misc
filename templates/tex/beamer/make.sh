#!/bin/sh
export TEXINPUTS="$HOME/.local/share/tex-custom:"
name="beamer"

id=$(echo "$(pwd)/$name" | md5sum | cut -c1-8)
path="/tmp/$name-$id"

mkdir -p "$path"
pdflatex -output-directory "$path" "$name.tex"
mv "$path/$name.pdf" ./

