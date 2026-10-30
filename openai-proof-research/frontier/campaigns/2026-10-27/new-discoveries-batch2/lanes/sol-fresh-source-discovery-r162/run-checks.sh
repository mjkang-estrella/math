#!/bin/bash
set -eu
cd "$(dirname "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
guard=../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py
python "$guard" python checks.py checks-replay.json
python "$guard" python triangle.py
python "$guard" python controls.py
python "$guard" python -c 'from pathlib import Path; import json; p=Path("."); assert (p/"checks.json").read_bytes()==(p/"checks-replay.json").read_bytes(); a=json.loads((p/"checks.json").read_text()); assert sum(x["connected_labeled"] for x in a["small"])==771; print("PASS: exact replay and 771 small connected graphs")'
