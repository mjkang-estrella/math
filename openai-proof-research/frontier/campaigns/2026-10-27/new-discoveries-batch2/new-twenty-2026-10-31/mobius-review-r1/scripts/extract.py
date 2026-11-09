from pathlib import Path
import zipfile,hashlib,json
D=Path(__file__).resolve().parents[1]; S=D.parent/'expanded-corpus-r246'
m=json.loads((S/'packet-manifest.json').read_text()); p=S/m['packet']
assert hashlib.sha256(p.read_bytes()).hexdigest()==m['sha256']
r=D/'replay'/'fresh';r.mkdir()
with zipfile.ZipFile(p) as z:
 assert sorted(z.namelist())==sorted(m['files'])
 for name,h in m['files'].items():
  assert '/' not in name and '\\' not in name
  b=z.read(name);assert hashlib.sha256(b).hexdigest()==h
  (r/name).write_bytes(b)
print(m)
