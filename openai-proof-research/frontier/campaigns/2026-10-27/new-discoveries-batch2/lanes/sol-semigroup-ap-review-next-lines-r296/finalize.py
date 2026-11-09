from pathlib import Path
import hashlib,json
L=Path(__file__).resolve().parent
provenance=dict(science='101 flat preinspection original/copy bindings in bindings.json',history='Top-level SCOUTING only, frozen before alias checks; dedup-bindings.json',sources='access.json: live arXiv PDF hashes and derived text hashes before inspection',restrictions='No children/Lean/manuscript/shared/git/public/browser/MathDB edits; fixed guard caps; root alone accepts',counts=dict(additional=9,total=39,next=40),novelty='No current public registry clearance and no novelty claim',proof='AP independently reviewed; new support A/B ordinary candidates pending independent review')
(L/'provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
rows=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in {'manifest.json','verification-receipt.json'}:
  rows.append(dict(path=str(p.relative_to(L)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
(L/'manifest.json').write_text(json.dumps(rows,indent=2)+'\n')
print('Manifest entries',len(rows))
