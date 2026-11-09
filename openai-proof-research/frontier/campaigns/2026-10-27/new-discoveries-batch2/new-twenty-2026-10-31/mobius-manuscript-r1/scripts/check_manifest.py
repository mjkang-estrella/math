from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parents[1]
m=json.loads((D/'manifest.json').read_text())
for name,h in m.items():
 p=Path(name);assert not p.is_absolute() and '..' not in p.parts
 assert hashlib.sha256((D/p).read_bytes()).hexdigest()==h,name
print('PASS',len(m),'manifest members')
