import json,gzip,re,hashlib
from pathlib import Path
L=Path(__file__).resolve().parent;B=L.parent
pat=re.compile(r'Matkowski|paranorm|Mulholland|Minkowski|QuasiArithmetic|quasi.arithmetic|GeneratorConvex|ConvexGenerator',re.I)
with (L/'registry-path-selection-corrected.jsonl').open('w') as out:
 for name in ('omega','openai'):
  p=B/'root-edge-irregulator-final-freeze-r1'/(name+'-tree.txt.gz');n=hits=0;h=hashlib.sha256()
  with gzip.open(p,'rb') as f:
   for line in f:
    h.update(line);n+=1;s=line.decode().strip()
    if pat.search(s):out.write(json.dumps({'registry':name,'path_record':s})+'\n');hits+=1
  print(name,n,hits,h.hexdigest())
 for p in [B/'sol-supertoken-preliminary-review-r1/omega-new-delta.json',L/'sources/omega-delta.json']:
  if not p.exists(): print('missing',str(p));continue
  d=json.loads(p.read_text());print('delta',p.name,d.get('total_commits'),len(d.get('files',[])))
  for x in d.get('files',[]):
   if pat.search(x['filename']) or pat.search(x.get('patch','')):
    out.write(json.dumps({'comparison':str(p),'path':x['filename'],'patch':x.get('patch','')[:7000]})+'\n')
for name in ('exactcoverage.json','intervals.json','net-changed-paths.json','baseline.json','http.jsonl'):
 p=B/'sol-renyi-registry-gap-closure-r3'/name
 h=hashlib.sha256()
 with p.open('rb') as f:
  for chunk in iter(lambda:f.read(131072),b''):h.update(chunk)
 print('reused-structural',name,p.stat().st_size,h.hexdigest())
