from pathlib import Path
import hashlib,json,gzip,tarfile,io
L=Path(__file__).resolve().parent
names=sorted(list(json.loads((L/'source-manifest.json').read_text()))+['source-manifest.json','SUMMARY.md','CLOCK-BRIDGE.md','FAILURES.md'])
buf=io.BytesIO()
with tarfile.open(fileobj=buf,mode='w',format=tarfile.USTAR_FORMAT) as t:
 for n in names:
  b=(L/n).read_bytes(); i=tarfile.TarInfo(n);i.size=len(b);i.mode=0o644;i.mtime=0;i.uid=i.gid=0;i.uname=i.gname=''
  t.addfile(i,io.BytesIO(b))
(L/'source-only.tar.gz').write_bytes(gzip.compress(buf.getvalue(),mtime=0))
R=L/'fresh-replay'
assert not R.exists()
R.mkdir()
with tarfile.open(L/'source-only.tar.gz') as t:t.extractall(R,filter='data')
assert not list(R.rglob('*.olean')) and not list(R.rglob('*.ilean'))
(L/'archive-receipt.json').write_text(json.dumps({'sha256':hashlib.sha256((L/'source-only.tar.gz').read_bytes()).hexdigest(),'members':names,'initial_extracted_own_compiled_artifacts':[]},indent=2)+'\n')
