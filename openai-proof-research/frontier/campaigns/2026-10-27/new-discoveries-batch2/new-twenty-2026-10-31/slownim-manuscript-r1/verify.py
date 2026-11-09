import hashlib,json
from pathlib import Path
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for line in (L/'MANIFEST.sha256').read_text().splitlines():
 expected,name=line.split('  ',1);assert sha(L/name)==expected,name
for name,expected in json.loads((L/'inputs.before.json').read_text()).items():
 p=Path(name)
 if p.exists():assert sha(p)==expected,name
assert sha(L/'source.zip')=='e1f35146078b39a2ace25101b02806404f741adb7042e1376f77d7c09e359996'
print('PASS: dossier manifest, available frozen originals and exact Lean packet')
