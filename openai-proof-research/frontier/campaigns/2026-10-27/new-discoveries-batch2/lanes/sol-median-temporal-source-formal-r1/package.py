from pathlib import Path
import json,hashlib,io,gzip,tarfile,shutil
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
names=['FiniteCore.lean','IntegerLeaf.lean','Audit.lean','lean_guard.py','audit_verify.py','run.sh','pins.json']
for p in L.glob('*.olean'):p.unlink()
assert not list(L.glob('*.olean'))
manifest={n:sha(L/n) for n in names}
(L/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
names+=['source-manifest.json']
buf=io.BytesIO()
with tarfile.open(fileobj=buf,mode='w',format=tarfile.USTAR_FORMAT) as tf:
 for n in sorted(names):
  raw=(L/n).read_bytes();t=tarfile.TarInfo(n);t.size=len(raw);t.mtime=0;t.uid=t.gid=0;t.mode=0o644
  tf.addfile(t,io.BytesIO(raw))
with (L/'source-only.tar.gz').open('wb') as out:
 with gzip.GzipFile(filename='',fileobj=out,mode='wb',mtime=0) as gz:gz.write(buf.getvalue())
fresh=L/'fresh-replay-02';assert not fresh.exists();fresh.mkdir()
with tarfile.open(L/'source-only.tar.gz','r:gz') as tf:
 for m in tf.getmembers():
  assert m.isfile() and m.name in names and Path(m.name).name==m.name
  (fresh/m.name).write_bytes(tf.extractfile(m).read())
assert not list(fresh.glob('*.olean'))
assert all(sha(fresh/n)==h for n,h in manifest.items())
(L/'archive-receipt.json').write_text(json.dumps({'sha256':sha(L/'source-only.tar.gz'),'deterministic':'USTAR sorted, uid/gid/mtime0, gzip mtime0 filename empty','local_compiled_artifacts_deleted':True,'fresh_extraction_sources_equal':True},indent=2)+'\n')
print('fresh source-only archive ready')
