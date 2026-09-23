#!/bin/sh
# Run from any working directory. Only the released manuscript files are read.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
command -v pdflatex >/dev/null 2>&1 || { echo "pdflatex is required." >&2; exit 127; }
pdflatex -interaction=nonstopmode -halt-on-error main.tex
if [ "${USE_BUNDLED_BBL:-0}" = "1" ]; then
    test -s main.bbl || { echo "The bundled main.bbl is missing." >&2; exit 1; }
elif command -v bibtex >/dev/null 2>&1; then
    bibtex main
elif command -v bibtex.original >/dev/null 2>&1; then
    bibtex.original main
else
    test -s main.bbl || { echo "BibTeX and a bundled main.bbl are both missing." >&2; exit 1; }
    echo "BibTeX unavailable; using the included main.bbl."
fi
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
if grep -E 'undefined references|undefined citations|Citation .* undefined|Reference .* undefined|multiply defined|Label.s. may have changed|Rerun to get' main.log; then
    echo "Unresolved bibliography/cross-reference diagnostics." >&2
    exit 1
fi
