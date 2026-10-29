import hashlib,json,zipfile
from pathlib import Path
r=Path(__file__).resolve().parent;s=r.parent/'sol-renyi-threshold-manuscript-packet-r1'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(65536):h.update(b)
 return h.hexdigest()
mf=json.loads((s/'final-review-freeze-manifest.json').read_text())['files']
for n,h in mf.items():assert sha(s/n)==h,n
freeze=dict(mf);freeze['final-review-freeze-manifest.json']=sha(s/'final-review-freeze-manifest.json')
(r/'freeze.json').write_text(json.dumps({'root':str(s),'files':freeze},indent=2)+'\n')
dest=r/'extracted-source';assert not dest.exists()
with zipfile.ZipFile(s/'packet.zip') as z:
 assert all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in z.namelist())
 assert not any(n.endswith(('.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig','.o','.so','.pyc')) for n in z.namelist())
 z.extractall(dest)
m=json.loads((dest/'manifest.json').read_text())
assert {p.relative_to(dest).as_posix() for p in dest.rglob('*') if p.is_file()}==set(m)|{'manifest.json'}
for n,h in m.items():assert sha(dest/n)==h,n
d={'status':'ROOT_INTAKE_PASS','frozen_files':len(mf),'packet_payload_files':len(m),'packet_sha256':sha(s/'packet.zip'),'paper_sha256':sha(s/'paper.pdf'),'pages_visually_read_by_root':4,'credit':0,'counts':[8,38]}
(r/'INTAKE.json').write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d))
