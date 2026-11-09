from pathlib import Path
import re,json,hashlib
w=Path(__file__).resolve().parent;pk=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages');tc=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux')
roots=[(p,p/'.lake/build/lib/lean') for p in pk.iterdir() if p.is_dir()]+[(tc/'src/lean',tc/'lib/lean')]
def strip_comments(s):
 out=[];i=0;depth=0
 while i<len(s):
  if s[i:i+2]=='/-':depth+=1;i+=2
  elif depth and s[i:i+2]=='-/':depth-=1;i+=2
  elif depth:
   if s[i]=='\n':out.append('\n')
   i+=1
  elif s[i:i+2]=='--':
   j=s.find('\n',i);i=len(s) if j<0 else j
  else:out.append(s[i]);i+=1
 return ''.join(out)
r={};missing=[];todo=re.findall(r'^(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([\w.]+)',strip_comments((w/'PartialEndpoint.lean').read_text()),re.M)
while todo:
 n=todo.pop()
 if n in r:continue
 rel=Path(*n.split('.'));hit=None
 for a,b in roots:
  f=(a/rel).with_suffix('.lean')
  if f.exists():hit=(f,(b/rel).with_suffix('.olean'));break
 if hit is None:missing.append(n);continue
 f,o=hit;data=f.read_bytes();r[n]={'source':str(f),'source_sha256':hashlib.sha256(data).hexdigest(),'olean':str(o),'olean_sha256':hashlib.sha256(o.read_bytes()).hexdigest() if o.exists() else None};todo+=re.findall(r'^(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([\w.]+)',strip_comments(data.decode()),re.M)
(w/'dependency-hashes.json').write_text(json.dumps({'scope':'Transitive source-import closure using anchored import parser; implicit Init runtime covered by pinned toolchain, not a claim of external kernel replay','modules':r,'unresolved':sorted(set(missing))},indent=2));print(len(r),'modules; unresolved',sorted(set(missing)))
