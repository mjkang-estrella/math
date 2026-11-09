from pathlib import Path
import hashlib,json,tarfile,gzip,io
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
names=['Finite.lean','Cube.lean','Endpoint.lean','Audit.lean','lean_guard.py','run.sh','audit_verify.py','pins.json']
m={n:sha(L/n) for n in names}
(L/'source-manifest.json').write_text(json.dumps(m,indent=2)+'\n');names+=['source-manifest.json']
with (L/'source-only.tar.gz').open('wb') as f:
 with gzip.GzipFile(filename='',mode='wb',fileobj=f,mtime=0) as gz:
  with tarfile.open(fileobj=gz,mode='w',format=tarfile.USTAR_FORMAT) as t:
   for n in sorted(names):
    data=(L/n).read_bytes();i=tarfile.TarInfo(n);i.size=len(data);i.mode=0o644;i.uid=i.gid=i.mtime=0;i.uname=i.gname='';t.addfile(i,io.BytesIO(data))
dest=L/'fresh-replay';dest.mkdir(exist_ok=False)
with tarfile.open(L/'source-only.tar.gz') as t:t.extractall(dest,filter='data')
assert not list(dest.rglob('*.olean'))
r={'archive_sha256':sha(L/'source-only.tar.gz'),'members':names,'deterministic':'USTAR sorted paths, uid/gid/mtime=0, mode644; gzip mtime0 empty filename','initial_own_oleans':[],'archive_contains':'only source, runner, audit, pins; immutable libraries external'}
(L/'archive-receipt.json').write_text(json.dumps(r,indent=2)+'\n')
print(r)
