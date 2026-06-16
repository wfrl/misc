#!/bin/sh
#(build-all-append 2)
export TEXINPUTS="$HOME/.local/share/tex-custom:"
name="Artikel-einspaltig"

id=$(echo "$(pwd)/$name" | md5sum | cut -c1-8)
path="/tmp/$name-$id"

mkdir -p "$path"
pdflatex -output-directory "$path" "$name.tex"
# mv "$path/$name.pdf" ./
gs -sDEVICE=pdfwrite -dCompatibilityLevel=1.5 -dNOPAUSE\
    -dQUIET -dBATCH -dPrinted=false\
    -sOutputFile="$name.pdf" "$path/$name.pdf"
