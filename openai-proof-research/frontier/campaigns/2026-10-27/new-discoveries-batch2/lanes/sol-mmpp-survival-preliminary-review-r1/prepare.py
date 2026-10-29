from pathlib import Path
import json,hashlib,shutil
b=Path(__file__).resolve().parent;l=b.parent; f=l/'root-mmpp-survival-review-freeze-r1/review-freeze.json';d=json.loads(f.read_text());src=Path(d['source_lane']);out={}
for n,h in d['files'].items():
 data=(src/n).read_bytes();actual=hashlib.sha256(data).hexdigest();assert actual==h,(n,actual,h)
 p=b/'copy'/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data);out[n]=actual
shutil.copyfile(f,b/'review-freeze.json');(b/'originals-before.json').write_text(json.dumps(out,indent=2))
c={}
for p in [l.parent/'ledger.json',l.parent/'prior-campaign-context.json',src/'context-read.json']:
 d=json.loads(p.read_text());c[str(p)]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'data':d}
(b/'context.json').write_text(json.dumps(c,indent=2));print('55 verified and byte-copied',len(out))
for p,z in c.items():
 d=z['data'];print(p, list(d) if isinstance(d,dict) else type(d))
 if 'accepted' in d:
  print([(x.get('number'),x.get('title')) for x in d['accepted']])
