from pathlib import Path
import json,hashlib,tarfile,gzip,io
R=Path(__file__).resolve().parent;C=R.parent/'root-mathdb-cayley-formal-intake-r357/frozen/sol-mathdb-cayley-source-formal-r353'
s=json.loads((C/'source-manifest.json').read_text())
with tarfile.open(C/'source-only.tar.gz') as t:
 assert len(t.getnames())==len(set(t.getnames())) and set(t.getnames())==set(s)|{'source-manifest.json'}
 for m in t:
  assert m.isfile() and m.name in set(s)|{'source-manifest.json'} and m.mtime==0
  assert t.extractfile(m).read()==(C/m.name).read_bytes()
assert (C/'lean_guard.py').read_bytes()==(R.parent/'sol-das-ap-irreducible-source-formal-r1/lean_guard.py').read_bytes()
with (R/'source-only.tar.gz').open('wb') as f:
 with gzip.GzipFile(filename='',mode='wb',fileobj=f,mtime=0) as z:
  with tarfile.open(fileobj=z,mode='w') as t:
   for n in sorted(list(s)+['source-manifest.json']):
    b=(C/n).read_bytes();i=tarfile.TarInfo(n);i.size=len(b);i.mode=0o644;i.mtime=0;i.uid=i.gid=0;i.uname=i.gname='';t.addfile(i,io.BytesIO(b))
assert (R/'source-only.tar.gz').read_bytes()==(C/'source-only.tar.gz').read_bytes()
D=R/'replay';D.mkdir()
with tarfile.open(R/'source-only.tar.gz') as t:t.extractall(D,filter='data')
print('PASS rebuilt deterministic archive; exact bytes; nine source-only members; guard matches bound RUN reference')
