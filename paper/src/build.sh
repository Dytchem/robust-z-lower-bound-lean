#!/bin/sh
# ---------------------------------------------------------------------------
# Build the manuscript.
#
#   ./build.sh            main.pdf        APS REVTeX 4.2 [preprint] manuscript
#                                         (single column, double spaced: the
#                                         format APS asks for at submission)
#                         main_arxiv.pdf  same source, single spaced
#                                         ([preprint,tightenlines]); use this
#                                         one for arXiv, which does not accept
#                                         double-spaced referee copies
#
# Requires revtex4-2 (installed under TEXMFHOME) and bibtex.
# ---------------------------------------------------------------------------
set -e
cd "$(dirname "$0")"

echo "== main.pdf (preprint, double spaced) =="
pdflatex -interaction=nonstopmode main.tex >/dev/null
bibtex main >/dev/null
pdflatex -interaction=nonstopmode main.tex >/dev/null
pdflatex -interaction=nonstopmode main.tex >/dev/null
printf '   %s pages\n' "$(pdfinfo main.pdf | awk '/^Pages/{print $2}')"

echo "== main_arxiv.pdf (preprint, single spaced) =="
tmp=$(mktemp -d)
cp main.tex verification.tex discussion.tex num_tables.tex \
   refs.bib fignum_num.pdf figphys.pdf "$tmp"/
sed 's/^  preprint,$/  preprint,\n  tightenlines,/' main.tex > "$tmp"/main.tex
( cd "$tmp" && pdflatex -interaction=nonstopmode main.tex >/dev/null \
  && bibtex main >/dev/null \
  && pdflatex -interaction=nonstopmode main.tex >/dev/null \
  && pdflatex -interaction=nonstopmode main.tex >/dev/null )
cp "$tmp"/main.pdf main_arxiv.pdf
cp "$tmp"/main.log main_arxiv.log
rm -rf "$tmp"
printf '   %s pages\n' "$(pdfinfo main_arxiv.pdf | awk '/^Pages/{print $2}')"

echo "== checks =="
for f in main main_arxiv; do
  printf '   %-11s errors=%s undefined=%s overfull=%s\n' "$f" \
    "$(grep -c '^! ' $f.log)" "$(grep -ci undefined $f.log)" "$(grep -c Overfull $f.log)"
done
