import hashlib,json,zipfile
from pathlib import Path
r=Path(__file__).resolve().parent;s=r.parent/'sol-factorial-product-manuscript-packet-r1'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b)
 return h.hexdigest()
m=json.loads((s/'final-review-freeze-manifest.json').read_text())['files']
for n,h in m.items():assert sha(s/n)==h,n
freeze=dict(m);freeze['final-review-freeze-manifest.json']=sha(s/'final-review-freeze-manifest.json')
(r/'freeze.json').write_text(json.dumps({'root':str(s),'files':freeze},indent=2)+'\n')
dest=r/'extracted';assert not dest.exists()
with zipfile.ZipFile(s/'packet.zip') as z:
 names=z.namelist();assert len(names)==len(set(names))
 assert all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in names)
 assert not any(n.endswith(('.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig','.o','.so','.pyc')) for n in names)
 z.extractall(dest)
payload=json.loads((dest/'manifest.json').read_text())
assert {p.relative_to(dest).as_posix() for p in dest.rglob('*') if p.is_file()}==set(payload)|{'manifest.json'}
for n,h in payload.items():assert sha(dest/n)==h,n
o={'status':'ROOT_INTAKE_PASS','frozen_files':len(m),'payload_files':len(payload),'packet_sha256':sha(s/'packet.zip'),'paper_sha256':sha(s/'paper.pdf'),'pages_read':3,'credit':0,'counts':[8,38]}
(r/'INTAKE.json').write_text(json.dumps(o,indent=2)+'\n');print(json.dumps(o))
