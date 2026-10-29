from pathlib import Path
import hashlib,json,zipfile,resource,signal
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(210,210));signal.alarm(230)
L=Path(__file__).resolve().parent
files=[]
for dirname in ['formal','inputs']:
 files.extend(p for p in (L/dirname).rglob('*') if p.is_file())
files.extend(L/f for f in ['run.py','pins.json','replay.py','package.py','modules.json','generate.py','make_empty.py','make_forced.py','benchmark.py','INTERFACE.md','SUMMARY.md','provenance.json','empty-cases.json','measurements.json','remaining-cases.json'])
files.extend(p for p in L.glob('*.log'))
files.extend(p for p in L.glob('*failed.lean.txt'))
files.append(L/'runs.jsonl')
# Preserve failed benchmark source without importing it into the audited endpoint.
fail=L/'benchmark-sources';fail.mkdir(exist_ok=True)
for p in (L/'dev').glob('Large*.lean'):(fail/p.name).write_bytes(p.read_bytes())
files.extend(fail.glob('*.lean'))
files=sorted(set(files))
manifest={str(p.relative_to(L)):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in files}
(L/'source-manifest.json').write_text(json.dumps(manifest,sort_keys=True,indent=2)+'\n')
with zipfile.ZipFile(L/'source-only-component.zip','w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for p in files+[L/'source-manifest.json']:
  i=zipfile.ZipInfo(str(p.relative_to(L)),date_time=(1980,1,1,0,0,0));i.compress_type=zipfile.ZIP_DEFLATED;i.external_attr=0o100644<<16
  z.writestr(i,p.read_bytes())
print(hashlib.sha256((L/'source-only-component.zip').read_bytes()).hexdigest())
