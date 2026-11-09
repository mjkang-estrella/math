from pathlib import Path
import hashlib,json,shutil
D=Path(__file__).resolve().parents[1]; P=D.parent
files=[P/'kirchhoff-formal-r1'/s for s in ['PRIOR-ART.md','PRIOR-ART.json','outputs/exact-independent.json','GAPS.md']]
files+=list((P/'kirchhoff-formal-r1/scripts').glob('*'))
files+=[P/'kirchhoff-root-ruling-r1.json']
files+=[P/'expanded-corpus-r105'/s for s in ['KIRCHHOFF-LEAD.md','outputs/kirchhoff-certificate.json','raw/349441.jsonl']]
files+=list((P/'expanded-corpus-r105/sources').glob('2101.07103.*'))
h={str(f.relative_to(P)):hashlib.sha256(f.read_bytes()).hexdigest() for f in files if f.is_file()}
assert h['kirchhoff-formal-r1/outputs/exact-independent.json']=='fd1e3a116188ccee76410656252c678bffa3ba743edc5921e6d79aaf981d5f59'
for f in files:
 if f.is_file():
  t=D/'inputs'/f.relative_to(P);t.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,t);assert hashlib.sha256(t.read_bytes()).hexdigest()==h[str(f.relative_to(P))]
(D/'input-hashes-before.json').write_text(json.dumps(h,indent=2)+'\n')
