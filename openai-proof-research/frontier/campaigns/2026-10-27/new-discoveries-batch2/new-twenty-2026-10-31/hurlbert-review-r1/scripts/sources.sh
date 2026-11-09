#!/bin/bash
set -eu
cd "$(dirname "$0")/.."
f(){ ./scripts/capped.sh python3 -I -B "$PWD/scripts/fetch.py" "$1" "$2"; }
f johnson https://arxiv.org/pdf/0710.5611
f horan https://arxiv.org/pdf/1301.1270
f ruskey https://webhome.cs.uvic.ca/~ruskey/Publications/Universal/ShortPerms.pdf
f holroyd-index https://webhome.cs.uvic.ca/~ruskey/Publications/Universal/ShortPermsJournal.html
f hurlbert-pubs https://glennhurlbert.github.io/pubs.html
f kirsch-page https://mason.gmu.edu/~rkirsch4/
f openalex-source 'https://api.openalex.org/works?search=Graph%20Universal%20Cycles%20Compression%20Connections&per-page=5'
f openalex-chung 'https://api.openalex.org/works/https://doi.org/10.1016/0012-365X(92)90670-G'
f github-one 'https://api.github.com/search/repositories?q=Hurlbert+universal+cycles&per_page=30'
f pool-projects https://raw.githubusercontent.com/Vilin97/lean-pool/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/projects.yml
f pool-tree 'https://api.github.com/repos/Vilin97/lean-pool/git/trees/01db1d7049cf9668bda1e9e106875ee1278b43e6?recursive=1'
f oeis 'https://oeis.org/search?q=permutations+universal+cycles&fmt=json'
f author-chung https://www.fanchung.org/ron-graham/papers
