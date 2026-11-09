from pathlib import Path
import hashlib,json,tarfile,gzip,io
L=Path(__file__).resolve().parent
names=['Definitions.lean','Witness.lean','Audit.lean','lean_guard.py','verify_pins.py','audit_verify.py','pins.json','run.sh']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(L/'source-manifest.json').write_text(json.dumps({n:sha(L/n) for n in names},indent=2)+'\n')
with (L/'source-only.tar.gz').open('wb') as f:
 with gzip.GzipFile(filename='',mode='wb',fileobj=f,mtime=0) as z:
  with tarfile.open(fileobj=z,mode='w') as t:
   for name in sorted(names+['source-manifest.json']):
    b=(L/name).read_bytes(); info=tarfile.TarInfo(name);info.size=len(b);info.mtime=0;info.mode=0o644;info.uid=info.gid=0;info.uname=info.gname='';t.addfile(info,io.BytesIO(b))
D=L/'fresh-replay';D.mkdir()
with tarfile.open(L/'source-only.tar.gz') as t:t.extractall(D,filter='data')
print('deterministic source-only archive and fresh extraction complete')
