import hashlib,json
from pathlib import Path
r=Path(__file__).resolve().parent
f=json.loads((r/'frozen-before.json').read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in f['files'].items():
 assert sha(Path(f['root'])/n)==h,n
 if n.startswith('formal/') or n in ['guard.py','helper_guard.py','replay_guard.py','pins.json']:
  assert sha(r/n)==h,n
print(json.dumps({'frozen_originals_unchanged':True,'inherited_mathematical_modules_byte_identical':True}))
