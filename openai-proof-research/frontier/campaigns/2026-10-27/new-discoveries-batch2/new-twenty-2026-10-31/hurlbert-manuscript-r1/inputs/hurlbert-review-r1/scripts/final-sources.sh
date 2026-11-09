#!/bin/bash
set -eu
cd "$(dirname "$0")/.."
f(){ ./scripts/capped.sh python3 -I -B "$PWD/scripts/fetch.py" "$1" "$2"; }
f openalex-source-citers 'https://api.openalex.org/works?filter=cites:W4362716257&per-page=100'
f openalex-chung-correct 'https://api.openalex.org/works/https://doi.org/10.1016/0012-365X(92)90699-G'
f research-problems https://glennhurlbert.github.io/Papers/RPGCUCpub.pdf
