#!/bin/bash
set -eu
cd "$(dirname "$0")/.."
f(){ ./scripts/capped.sh python3 -I -B "$PWD/scripts/fetch.py" "$1" "$2"; ./scripts/capped.sh pdftotext -layout "downloads/$1/body-0" "downloads/$1/text.txt"; }
f overlap-enumeration https://arxiv.org/pdf/1609.02210
f cycle-polytope https://arxiv.org/pdf/1910.02233
f gray-survey https://arxiv.org/pdf/2202.01280
f permutation-classes https://dmtcs.episciences.org/2727/pdf
f ruskey-explicit https://arxiv.org/pdf/0710.1842
