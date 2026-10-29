import os,re,json,hashlib,time
from pathlib import Path
L=Path(__file__).resolve().parent;R=L.parents[5]
pat=re.compile(r'2606[.]13162|Permanental.Inequalities.and.Unit|Pan.{0,20}Skandera',re.I)
out=(L/'priority-originals.jsonl').open('w');n=0;shown=0
for base,dirs,files in os.walk(R):
 dirs[:]=[d for d in dirs if d not in {'.git','.lake','node_modules','__pycache__'} and Path(base,d)!=L]
 for name in files:
  if not (re.search(r'^(SUMMARY|PROOF|discovery|review|NEXT|SCREENED-OUT|novelty-rejections)',name,re.I) and name.endswith(('.md','.txt'))):continue
  p=Path(base,name);h=hashlib.sha256();tail='';hits=[]
  with p.open(errors='replace') as f:
   for s in f:
    h.update(s.encode())
    if pat.search(s):hits.append(s[:650])
  n+=1
  if hits:
   d={'path':str(p.relative_to(R)),'sha256_text':h.hexdigest(),'hits':hits[:8]};out.write(json.dumps(d)+'\n')
   if shown<35:print(json.dumps(d));shown+=1
out.close();print('original source/history files inspected',n)
for name in ('omega','openai'):
 p=L/'sources'/(name+'-head.json')
 d=json.loads(p.read_text());print('HEAD',name,d['sha'],d['commit']['committer']['date'])
