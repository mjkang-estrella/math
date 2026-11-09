import resource,os
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(35,35))
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
from pathlib import Path
import re,hashlib,json
p=Path(__file__).resolve().parent
packages=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
lean=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux')
roots=[(q,q/'.lake/build/lib/lean') for q in packages.iterdir() if q.is_dir()]+[(lean/'src/lean',lean/'lib/lean')]
seen=set();manifest={};missing=[]
def imports(text):
 out=[];i=0;depth=0
 while i<len(text):
  if text.startswith('/-',i):depth+=1;i+=2
  elif depth and text.startswith('-/',i):depth-=1;i+=2
  elif depth:i+=1
  elif text.startswith('--',i):
   j=text.find('\n',i);i=len(text) if j<0 else j
  else:out.append(text[i]);i+=1
 clean=''.join(out)
 return re.findall(r'^(?:(?:public|private|meta) )*import\s+(?:all\s+)?([A-Za-z][A-Za-z0-9_.]*)',clean,re.M)

def sha(f):
 h=hashlib.sha256()
 with f.open('rb') as s:
  for b in iter(lambda:s.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def visit(n):
 if n in seen:return
 seen.add(n)
 rel=Path(*n.split('.'))
 for src,lib in roots:
  f=src/rel.with_suffix('.lean');o=lib/rel.with_suffix('.olean')
  if o.is_file():
   manifest[str(o)]=sha(o)
   if f.is_file():
    manifest[str(f)]=sha(f)
    for m in imports(f.read_text()):visit(m)
   return
 missing.append(n)
for f in (p/'formal').glob('*.lean'):
 if f.name=='Probe.lean':continue
 for n in re.findall(r'^import\s+(\S+)',f.read_text(),re.M):
  if not (p/'formal'/f'{n}.lean').exists():visit(n)
result={'root_dependencies':sorted(seen),'hashes':manifest,'missing':missing,'scope':'Recursive source import closure, resolved compiled oleans plus available source bytes; compiler binary separately pinned. Imports parsed from one-import-per-line syntax.'}
(p/'dependency-hashes.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'modules':len(seen),'files':len(manifest),'missing':missing}))
