import os,resource,signal,json,hashlib,zipfile,re
from pathlib import Path
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(20,25));signal.alarm(30)
L=Path(__file__).resolve().parent;A=L/'addon';h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files=list(json.loads((A/'source-manifest.json').read_text()))+['source-manifest.json']
zp=L/'source-only-sorted-addon.zip'
with zipfile.ZipFile(zp,'w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for f in files:
  info=zipfile.ZipInfo(f,(2026,10,29,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED;z.writestr(info,(A/f).read_bytes())
x=L/'addon-extracted';x.mkdir()
with zipfile.ZipFile(zp) as z:z.extractall(x)
(L/'addon-archive-receipt.json').write_text(json.dumps({'sha256':h(zp),'bytes':zp.stat().st_size,'source_only':True},indent=2))
# The smoke test only confirms independent placement shards can be imported together.
s=(L/'formal/OriginAudit.lean').read_text();a=s[s.index('import Lean'):];st=a.index('let mods := #[');en=a.index(']',st)
a=a[:st]+'let mods := #[`ShardImportSmoke]'+a[en+1:]
(L/'formal/SmokeAudit.lean').write_text('import ShardImportSmoke\n'+a)
