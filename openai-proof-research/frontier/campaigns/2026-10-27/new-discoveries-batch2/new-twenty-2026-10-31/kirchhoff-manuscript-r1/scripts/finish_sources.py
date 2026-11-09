from pathlib import Path
import json,hashlib,shutil
D=Path(__file__).resolve().parents[1]
pin=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/lake-manifest.json')
h=json.loads((D/'input-hashes-before.json').read_text());h[str(pin)]=hashlib.sha256(pin.read_bytes()).hexdigest();(D/'input-hashes-before.json').write_text(json.dumps(h,indent=2)+'\n');shutil.copyfile(pin,D/'sources/lake-manifest.json')
p=D/'replay.py';s=p.read_text();s=s.replace("run('audit',['Audit.lean'])","run('audit',['-o','Audit.olean','Audit.lean'])\nrun('leanchecker-Audit',['--checker','Audit'])")
s=s.replace("run('semantic-controls'", "run('semantic-controls'")
# Demand exact version, never call Lean outside guard.
s=s.replace("run('version',['--version'])","run('version',['--version'])\nv=(D/'logs/version.log').read_text()\nif '4.34.1' not in v or '5045d0056413266e57c625dcd7c365b10e377c52' not in v: raise SystemExit('Wrong Lean pin: '+v)")
p.write_text(s)
