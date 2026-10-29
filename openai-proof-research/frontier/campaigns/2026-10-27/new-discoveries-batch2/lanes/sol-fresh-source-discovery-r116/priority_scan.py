import os,re,json,hashlib,time
from pathlib import Path
L=Path(__file__).resolve().parent;R=L.parents[5]
pat=re.compile(rb'Matkowski|paranorm|Mulholland|converse.{0,25}Minkowski|jca2591|2507[.]01353|Radon.partition',re.I)
n=hits=0
with (L/'priority-hits.jsonl').open('w') as out,(L/'priority-manifest.jsonl').open('w') as mf:
 for base,dirs,files in os.walk(R):
  dirs[:]=[d for d in dirs if d not in {'.git','.lake','node_modules','__pycache__'} and Path(base,d)!=L]
  for name in files:
   p=Path(base,name)
   if p.suffix not in {'.md','.py','.sh'}:continue
   if any(x in name.lower() for x in ('inventory-content','required-content','semantic-hit','screen-hit','duplicate-corpus','audit-')):continue
   if p.stat().st_size>2000000:continue
   h=hashlib.sha256();nh=0
   with p.open('rb') as f:
    tail=b'';off=0
    while True:
     b=f.read(65536)
     if not b:break
     h.update(b);s=tail+b
     if nh<4:
      for m in pat.finditer(s):
       out.write(json.dumps({'path':str(p.relative_to(R)),'offset':off-len(tail)+m.start(),'excerpt':s[max(0,m.start()-180):m.end()+400].decode('utf8','replace')})+'\n');nh+=1
       if nh>=4:break
     tail=b[-256:];off+=len(b)
   mf.write(json.dumps({'path':str(p.relative_to(R)),'sha256':h.hexdigest(),'bytes':off,'hits':nh})+'\n');n+=1;hits+=bool(nh)
print(json.dumps({'files':n,'hit_files':hits}))
