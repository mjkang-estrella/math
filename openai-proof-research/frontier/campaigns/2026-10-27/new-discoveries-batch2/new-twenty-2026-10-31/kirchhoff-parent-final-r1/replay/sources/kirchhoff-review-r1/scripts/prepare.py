from pathlib import Path
import hashlib,json,zipfile
D=Path(__file__).resolve().parents[1]; P=D.parent
files=[]
for x in ['kirchhoff-formal-r2/formal','kirchhoff-formal-r2/fresh-extracted/receipts']:
 files+=list((P/x).rglob('*'))
for x in ['kirchhoff-formal-r2/kirchhoff-source-only.zip','kirchhoff-formal-r2/SUMMARY.md','kirchhoff-formal-r2/statement-correspondence.md','kirchhoff-formal-r2/results.json','kirchhoff-formal-r1/PRIOR-ART.md','kirchhoff-formal-r1/PRIOR-ART.json','kirchhoff-formal-r1/outputs/exact-independent.json','kirchhoff-root-ruling-r1.json','expanded-corpus-r105/KIRCHHOFF-LEAD.md','expanded-corpus-r105/raw/349441.jsonl','expanded-corpus-r105/extracted.json']:
 files.append(P/x)
files+=list((P/'expanded-corpus-r105/sources').glob('2101.07103.*'))
h={str(f):hashlib.sha256(f.read_bytes()).hexdigest() for f in files if f.is_file()}
(D/'receipts/input-before.json').write_text(json.dumps(h,indent=2))
z=P/'kirchhoff-formal-r2/kirchhoff-source-only.zip'
assert h[str(z)]=='927d6c3cb8977308a190122f511788bd8606a7cdcbf28ccbc159852b8830ea3c'
with zipfile.ZipFile(z) as q:
 for f in q.infolist():
  p=Path(f.filename)
  assert not p.is_absolute() and '..' not in p.parts and not (f.external_attr>>16)&0o170000==0o120000
  assert p.suffix not in ['.olean','.so']
 q.extractall(D/'fresh')
print(q.namelist())
