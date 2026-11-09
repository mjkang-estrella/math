from pathlib import Path
import json,hashlib,tarfile,gzip,io
L=Path(__file__).resolve().parent
sha=lambda x:hashlib.sha256(x).hexdigest()
files=[p for p in L.iterdir() if p.is_file() and (p.suffix in {'.lean','.py','.md'} or p.name in {'pins.json','freeze.json','provenance.json','run.sh'})]
files+=list((L/'frozen').rglob('*'))+list((L/'administrative').rglob('*'))
files=sorted({p for p in files if p.is_file()},key=lambda p:str(p.relative_to(L)))
manifest={str(p.relative_to(L)):sha(p.read_bytes()) for p in files}
(L/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
files.append(L/'source-manifest.json');files.sort(key=lambda p:str(p.relative_to(L)))
buf=io.BytesIO()
with tarfile.open(fileobj=buf,mode='w',format=tarfile.USTAR_FORMAT) as tf:
 for p in files:
  raw=p.read_bytes();t=tarfile.TarInfo(str(p.relative_to(L)));t.size=len(raw);t.mode=0o644;t.mtime=0;t.uid=t.gid=0;t.uname=t.gname='';tf.addfile(t,io.BytesIO(raw))
raw=gzip.compress(buf.getvalue(),mtime=0)
(L/'source-only.tar.gz').write_bytes(raw)
(L/'archive-receipt.json').write_text(json.dumps({'sha256':sha(raw),'bytes':len(raw),'members':[str(p.relative_to(L)) for p in files],'compiled_artifacts':False,'deterministic':'USTAR sorted, uid/gid0, mode0644, mtime0, gzip mtime0'},indent=2)+'\n')
fresh=L/'fresh-replay';fresh.mkdir(exist_ok=False)
with tarfile.open(fileobj=io.BytesIO(raw),mode='r:gz') as tf:tf.extractall(fresh,filter='data')
print(json.dumps({'archive_sha256':sha(raw),'members':len(files),'fresh':str(fresh)}))
