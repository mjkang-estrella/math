from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parent; L=D.parent
refs=json.loads((D/'flat-bindings.json').read_text())
for lane,names in [('sol-mathdb-primary-qualified-breadth-r406',['primary/abert.pdf','primary/abert.txt','primary/abert.meta.json']),('sol-mathdb-primary-qualified-breadth-r404',['evidence/bestvina.pdf','evidence/bestvina.txt']),('sol-mathdb-primary-qualified-breadth-r576',['1503.05295.html','1503.05295.txt','source-provenance.json'])]:
 p=L/lane; m=json.loads((p/'manifest.json').read_text())
 for name in ['manifest.json']+names:
  f=p/name
  if not f.exists():continue
  b=f.read_bytes(); h=hashlib.sha256(b).hexdigest()
  if name!='manifest.json':
   x=next(x for x in m['files'] if x['path']==name); assert h==x['sha256'] and len(b)==x.get('size',x.get('bytes'))
  refs.append({'path':str(f),'sha256':h,'size':len(b)})
(D/'flat-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
print('source binding PASS',len(refs))
