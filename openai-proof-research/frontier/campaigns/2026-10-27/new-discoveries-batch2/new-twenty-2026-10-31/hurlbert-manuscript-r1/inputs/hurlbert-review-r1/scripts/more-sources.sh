#!/bin/bash
set -eu
cd "$(dirname "$0")/.."
f(){ ./scripts/capped.sh python3 -I -B "$PWD/scripts/fetch.py" "$1" "$2"; }
f holroyd https://webhome.cs.uvic.ca/~ruskey/Publications/Universal/ShortPermsJournal.pdf
f slides https://webhome.cs.uvic.ca/~ruskey/Publications/Universal/UniPermAppTheory.pdf
f gabric https://skeeter.socs.uoguelph.ca/~sawada/papers/kary-successor.pdf
f fillmore https://arxiv.org/pdf/2310.13067
f openalex-source-doi 'https://api.openalex.org/works/https://doi.org/10.1016/j.aam.2023.102522'
f openalex-chung-search 'https://api.openalex.org/works?search=Universal%20cycles%20for%20combinatorial%20structures&per-page=3'
f github-two 'https://api.github.com/search/repositories?q=%22universal+cycles%22+permutations&per_page=50'
