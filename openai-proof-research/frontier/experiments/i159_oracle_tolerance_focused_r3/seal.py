"""Canonical inventory, prevalidation, then a single exclusive-create seal."""
from pathlib import Path
import json,hashlib
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i159_oracle_tolerance_focused_r3'
E=ROOT/'frontier/experiments/i159_oracle_tolerance_focused_r3'
REPORT=ROOT/'frontier/reviews/i159-oracle-tolerance-focused-r3.md'
assert not (S/'seal.json').exists(),'No resealing'
def sha(b):return hashlib.sha256(b).hexdigest()
# Prevalidate all direct immutable bytes and read passages before inventory/seal.
for r in json.loads((S/'immutable.json').read_text()):assert sha((ROOT/r['path']).read_bytes())==r['sha256'],r['path']
for r in json.loads((S/'read-log.json').read_text()):
 b=(ROOT/r['path']).read_bytes();assert sha(b)==r['sha256'];lines=b.decode().splitlines();assert sha('\n'.join(lines[r['start']-1:r['end']]).encode())==r['passage_sha256']
files=[p for d in (S,E) for p in d.rglob('*') if p.is_file() and p not in (S/'inventory.json',S/'seal.json')]+[REPORT]
assert not any(p.is_symlink() for p in files)
rows=[]
for p in sorted(files,key=lambda p:str(p.relative_to(ROOT))):
 b=p.read_bytes();rows.append({'path':str(p.relative_to(ROOT)),'sha256':sha(b),'bytes':len(b)})
assert len({r['path'] for r in rows})==len(rows)
inventory=json.dumps(rows,indent=2)+'\n';(S/'inventory.json').write_text(inventory)
for r in rows:assert sha((ROOT/r['path']).read_bytes())==r['sha256']
seal={'schema':1,'iteration':159,'scope':'Original R154 focused correctness review; I157 historical broad audit incomplete','inventory_sha256':sha(inventory.encode()),'owned_files_including_inventory_and_seal':len(rows)+2,'prevalidated':True,'seal_creations':1,'replay':'python3 -B frontier/experiments/i159_oracle_tolerance_focused_r3/verify.py','no_repair_or_reseal':True}
with (S/'seal.json').open('x') as f:f.write(json.dumps(seal,indent=2)+'\n')
print(json.dumps({'status':'SEALED ONCE','owned_files':len(rows)+2,'seal_sha256':sha((S/'seal.json').read_bytes())},indent=2))
