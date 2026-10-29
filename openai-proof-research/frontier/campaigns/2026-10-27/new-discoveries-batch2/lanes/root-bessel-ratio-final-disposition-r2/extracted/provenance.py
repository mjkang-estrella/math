import json,hashlib,tarfile,shutil
from pathlib import Path
L=Path(__file__).resolve().parent
B=L.parents[1]
files=[L.parents[5]/'AGENTS.md',B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json', B/'lanes/root-bessel-ratio-adjudication-r1/ADJUDICATION.json']
(L/'inputs').mkdir(exist_ok=True)
hashfile=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
records=[]
for p in files:
 if p.exists():
  before=hashfile(p); target=L/'inputs'/((p.parent.name+'-')+p.name); shutil.copyfile(p,target);target.chmod(0o444)
  records.append(dict(original=str(p),copy=str(target.relative_to(L)),before=before,copy_sha256=hashfile(target),after=hashfile(p)))
archive=L/'base-component.tar.gz'
assert hashfile(archive)=='41a063e4a225bbce03d31eb3a5106c02ae7dcf38082e710ec125c72f4aee2d73'
with tarfile.open(archive) as t:
 core={n:hashlib.sha256(t.extractfile(n).read()).hexdigest() for n in ['BesselRatio.lean','BesselAnalytic.lean','BesselInterfaces.lean']}
assert all(hashfile(L/n)==h for n,h in core.items())
archive.chmod(0o444)
for n in core:(L/n).chmod(0o444)
pins=json.loads((L/'pins.json').read_text())
assert hashfile(Path(pins['lean_binary']))==pins['lean_sha256']
packages={}
for n,p in pins['packages'].items():
 path=Path(p['path']);gd=path/'.git'
 if gd.is_file():gd=(path/gd.read_text().strip().split(': ',1)[1]).resolve()
 head=(gd/'HEAD').read_text().strip()
 if head.startswith('ref: '):
  ref=head[5:]; rf=gd/ref
  if rf.exists():head=rf.read_text().strip()
  else:
   matches=[s.split()[0] for s in (gd/'packed-refs').read_text().splitlines() if s.endswith(' '+ref)]; assert len(matches)==1;head=matches[0]
 assert head==p['revision'],(n,head)
 packages[n]=dict(actual=head,expected=p['revision'],path=str(path))
(L/'provenance.json').write_text(json.dumps(dict(base_sha256=hashfile(archive),core_sha256=core,inputs=records,packages=packages),indent=2)+'\n')
print('PASS archive, three unchanged modules, source copies, Lean binary and all eight package HEADs')
