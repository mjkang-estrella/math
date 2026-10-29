import os,resource,signal,json,hashlib,shutil
from pathlib import Path
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(15,20));signal.alarm(25)
L=Path(__file__).resolve().parent;A=L/'addon';A.mkdir(exist_ok=True);(A/'formal').mkdir(exist_ok=True)
mods=['Grid','Growth','Normalization','Bounds','Witness','Efficient','Coverage','Existence','ListCertificate','Assembly','SmallClosure','SortedCertificate','FastSmallClosure']
for m in mods:shutil.copy2(L/'formal'/(m+'.lean'),A/'formal'/(m+'.lean'))
for p in ['pins.json','run.py']:shutil.copy2(L/p,A/p)
s=(L/'formal/OriginAudit.lean').read_text();a=s[s.index('import Lean'):];start=a.index('let mods := #[');end=a.index(']',start)
a=a[:start]+'let mods := #[`SortedCertificate, `FastSmallClosure]'+a[end+1:]
(A/'formal/AddonAudit.lean').write_text('import FastSmallClosure\n'+a)
(A/'modules.json').write_text(json.dumps(mods))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest={'formal/'+p.name:sha(p) for p in (A/'formal').glob('*.lean')};manifest.update({p:sha(A/p) for p in ['pins.json','run.py','modules.json']})
(A/'source-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
