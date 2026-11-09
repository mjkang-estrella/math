from pathlib import Path
import resource,signal,sys,json,hashlib,zipfile
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(230)
L=Path(__file__).resolve().parent;out=Path(sys.argv[1]).resolve()
assert not out.is_relative_to(L),'ZIP output must be outside packet tree'
files=sorted(f for f in L.rglob('*') if f.is_file() and f.name!='MANIFEST.json')
for f in files:
 assert f.suffix not in ['.olean','.ilean','.o','.so','.a','.pyc','.zip'],f
 assert not {'__pycache__','.lake','dev','extracted','logs-development'}.intersection(f.relative_to(L).parts),f
mf={str(f.relative_to(L)):dict(bytes=f.stat().st_size,sha256=hashlib.sha256(f.read_bytes()).hexdigest()) for f in files}
(L/'MANIFEST.json').write_text(json.dumps(mf,indent=2,sort_keys=True)+'\n')
files=sorted(files+[L/'MANIFEST.json'])
with zipfile.ZipFile(out,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for f in files:
  zi=zipfile.ZipInfo(str(f.relative_to(L)),(2026,10,29,0,0,0));zi.compress_type=zipfile.ZIP_DEFLATED;zi.external_attr=0o644<<16
  z.writestr(zi,f.read_bytes(),compresslevel=9)
print(json.dumps(dict(entries=len(files),bytes=out.stat().st_size,sha256=hashlib.sha256(out.read_bytes()).hexdigest())))
