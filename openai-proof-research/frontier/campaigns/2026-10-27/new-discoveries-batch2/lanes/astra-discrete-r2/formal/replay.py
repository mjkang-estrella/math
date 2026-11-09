"""Replay the initial bridge with pinned Lean, without modifying shared files."""
from pathlib import Path
import os, subprocess, hashlib, json
lane=Path(__file__).resolve().parent.parent
base=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal')
lean=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
paths=[base/'.lake/build/lib/lean']+sorted((base/'.lake/packages').glob('*/.lake/build/lib/lean'))
env=dict(os.environ,LEAN_PATH=':'.join(map(str,paths)))
r=subprocess.run([str(lean),'formal/ResidueBridge.lean'],cwd=lane,env=env,text=True,capture_output=True)
(lane/'formal/check.log').write_text(r.stdout+r.stderr)
report={'exit_code':r.returncode,'lean_version':subprocess.check_output([str(lean),'--version'],text=True).strip(),'lean_binary_sha256':hashlib.sha256(lean.read_bytes()).hexdigest(),'mathlib_commit':'d13f23b723b8a846827a245b89c10fc7d3f11612','source_sha256':hashlib.sha256((lane/'formal/ResidueBridge.lean').read_bytes()).hexdigest(),'scope':'Three auxiliary real-algebra/order lemmas only; no Hoggatt endpoint.'}
(lane/'formal/replay.json').write_text(json.dumps(report,indent=2))
print(r.stdout+r.stderr);print(json.dumps(report,indent=2));raise SystemExit(r.returncode)
