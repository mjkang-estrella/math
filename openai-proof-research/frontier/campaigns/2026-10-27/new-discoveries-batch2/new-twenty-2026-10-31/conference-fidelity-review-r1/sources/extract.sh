#!/bin/bash
set -euo pipefail
for v in 1210.5725v1 1210.5725; do
 pdftotext -layout "../../fresh-corpus-r3/sources/$v.pdf" "$v.independent.txt"
done
pdftotext -layout ../../fresh-corpus-r3/sources/web/28_Lee_Manhattan_ISIT13.pdf ISIT.independent.txt
pdftoppm -f 4 -l 4 -scale-to 1800 -png ../../fresh-corpus-r3/sources/1210.5725v1.pdf v1 >/dev/null 2>render-v1.log
pdftoppm -f 6 -l 6 -scale-to 1800 -png ../../fresh-corpus-r3/sources/1210.5725.pdf v2 >/dev/null 2>render-v2.log
pdftoppm -f 2 -l 2 -scale-to 1800 -png ../../fresh-corpus-r3/sources/web/28_Lee_Manhattan_ISIT13.pdf isit >/dev/null 2>render-isit.log
