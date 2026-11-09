#!/usr/bin/env bash
set -euo pipefail
TRACE_PACKET_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
source "$TRACE_PACKET_DIR/env.sh"
TRACE_REPLAY_DIR="$TRACE_PACKET_DIR/clean-replay"
python3 - "$TRACE_PACKET_DIR" "$TRACE_REPLAY_DIR" <<'INNER'
import sys,zipfile,pathlib
p=pathlib.Path(sys.argv[1]);out=pathlib.Path(sys.argv[2]);out.mkdir(exist_ok=True)
with zipfile.ZipFile(p/'formal-source.zip','w') as z:
 for f in sorted((p/'formal').iterdir()):
  if f.suffix in ['.lean','.toml','.json'] or f.name=='lean-toolchain':z.write(f,f.name)
with zipfile.ZipFile(p/'formal-source.zip') as z:z.extractall(out)
for f in out.glob('*.olean'):f.unlink()
INNER
export LEAN_PATH="$TRACE_REPLAY_DIR:$LEAN_PATH"
TRACE_CPUS=$(python3 -c 'import os;print(",".join(map(str,sorted(os.sched_getaffinity(0))[:2])))')
for TRACE_MODULE in TraceFormal CoordinateRelation MatrixRelation FullCE FixedList Recursion ReductionData InverseCertificates SampleEvaluations EvaluationTables InverseSound Audit; do
  echo "REBUILD $TRACE_MODULE"
  taskset -c "$TRACE_CPUS" lean -j2 -M6000 -DwarningAsError=true -o "$TRACE_REPLAY_DIR/$TRACE_MODULE.olean" "$TRACE_REPLAY_DIR/$TRACE_MODULE.lean"
done
python3 - "$TRACE_REPLAY_DIR" <<'INNER'
import pathlib,re,sys
for p in pathlib.Path(sys.argv[1]).glob('*.lean'):
 s=p.read_text()
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',s),p
print('PASS strict replay; no forbidden proof construct; axiom audits printed above')
INNER
