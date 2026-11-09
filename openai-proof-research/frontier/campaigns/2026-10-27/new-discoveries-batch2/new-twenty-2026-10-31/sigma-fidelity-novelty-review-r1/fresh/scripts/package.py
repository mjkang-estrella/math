#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,zipfile,shutil
r=Path(__file__).resolve().parent.parent
files=[*r.glob('Sigma/*.lean'),*r.glob('scripts/*.py')]
files += [r/f for f in ['Audit.lean','NegativeControls.lean','PrintAxioms.lean','lean-toolchain','pins.json','PROOF-MAP.md','SUMMARY.md','results.json','TASK.txt','receipts/inputs-before.json','receipts/inputs-after.json','receipts/preservation.json']]
files=sorted(files)
manifest={'algorithm':'sha256','note':'All archived files except MANIFEST.json itself. No generated oleans. Replay receipts remain external to avoid self-reference.','files':{str(p.relative_to(r)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}}
(r/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
with zipfile.ZipFile(r/'proof-packet.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in files+[r/'MANIFEST.json']:z.write(p,p.relative_to(r))
e=r/'extracted-replay'
if e.exists():shutil.rmtree(e)
e.mkdir()
with zipfile.ZipFile(r/'proof-packet.zip') as z:z.extractall(e)
print('Packaged and freshly extracted',len(files)+1,'files.')
