from pathlib import Path
import os,re,json,hashlib,datetime
L=Path(__file__).parent;R=L.parents[5]
pat=re.compile(rb'(?<![A-Za-z0-9])10\.2478/ausm-2020-0020(?![A-Za-z0-9])|nil.?clean|nilpotents.{0,50}differences',re.I)
n=hits=errors=0
with (L/'supplement-content.jsonl').open('x') as co,(L/'supplement-hashes.jsonl').open('x') as ha,(L/'supplement-hits.jsonl').open('x') as ho:
 for base,dirs,files in os.walk(R):
  dirs[:]=sorted(d for d in dirs if d not in ['.git','node_modules','.lake','__pycache__'] and Path(base,d)!=L)
  for name in sorted(files):
   p=Path(base,name);rel=str(p.relative_to(R));low=rel.lower()
   # Independently revisit all authored semantic notes and all script languages.
   if p.suffix.lower() not in ['.md','.py','.sh','.js','.ts','.mjs','.cjs','.toml','.ipynb','.rst'] and not any(t in low for t in ['openproblem','screened-out','agents.']):continue
   h=hashlib.sha256();size=0;prev=b''
   try:
    with p.open('rb') as f:
     while b:=f.read(65536):
      h.update(b);co.write(json.dumps({'path':rel,'offset':size,'text':b.decode('utf8','replace')})+'\n')
      for m in pat.finditer(prev+b):ho.write(json.dumps({'path':rel,'offset':size-len(prev)+m.start(),'context':(prev+b)[max(0,m.start()-160):m.end()+300].decode('utf8','replace')})+'\n');hits+=1
      prev=b[-256:];size+=len(b)
    ha.write(json.dumps({'path':rel,'bytes':size,'sha256':h.hexdigest()})+'\n');n+=1
   except OSError as e:ha.write(json.dumps({'path':rel,'error':str(e)})+'\n');errors+=1
print(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':n,'hits':hits,'errors':errors,'scope':'all-date semantic documentation and script supplement; includes zero-character nilclean spelling'}))
