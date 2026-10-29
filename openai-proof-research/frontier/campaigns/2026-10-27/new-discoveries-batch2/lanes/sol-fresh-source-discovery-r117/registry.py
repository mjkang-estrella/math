import json,gzip,hashlib,re,urllib.request,time
from pathlib import Path
L=Path(__file__).resolve().parent;B=L.parent
pat=re.compile(r'Inverse.?Z|Matroid.*(?:LogConc|Unimod)|PanSkanderaWang|psw.bruhat|Permanental|Grothendieck.*(?:Class|Moduli)|Mbar|Aluffi',re.I)
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(65536),b''):h.update(b)
 return h.hexdigest()
paths=[];frozen=json.loads((L/'frozen-before.json').read_text())
with (L/'registry-target-paths.jsonl').open('w') as out:
 for name in ('omega','openai'):
  p=B/'root-edge-irregulator-final-freeze-r1'/(name+'-tree.txt.gz')
  with gzip.open(p,'rt') as f:
   for s in f:
    if pat.search(s):out.write(json.dumps({'registry':name,'pathrecord':s.strip()})+'\n')
 intervals=json.loads((B/'sol-renyi-registry-gap-closure-r3/intervals.json').read_text())
 for interval in intervals:
  candidates=[]
  def walk(d):
   if isinstance(d,dict):
    for k,v in d.items():
     if isinstance(v,str) and v.endswith('.json'):candidates.append(v)
     else:walk(v)
   elif isinstance(d,list):
    for x in d:walk(x)
  walk(interval)
  for name in candidates:
   p=Path(name)
   if not p.is_absolute():p=B/'sol-renyi-registry-gap-closure-r3'/p
   if p.exists():paths.append(p)
 for p in [B/'sol-supertoken-preliminary-review-r1/omega-new-delta.json',B/'sol-factorial-product-prior-clearance-r2/fresh-delta.json']+paths:
  frozen.append({'path':str(p),'sha256':sha(p)})
  d=json.loads(p.read_text())
  for x in d.get('files',[]):
   if pat.search(x.get('filename','')+' '+x.get('patch','')):
    out.write(json.dumps({'response':str(p),'filename':x['filename'],'patch':x.get('patch','')[:10000]})+'\n')
 print('actual referenced comparison paths',len(set(paths)))
with (L/'frozen-before.json').open('w') as f:json.dump(frozen,f,indent=2)
head=json.loads((L/'sources/omega-head.json').read_text())['sha']
url='https://api.github.com/repos/the-omega-institute/trureturing/compare/0d4df45e499f5e2d97471c506c555c18fd44920c...'+head
r={'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'url':url,'path':'sources/fresh-delta.json'}
try:
 with urllib.request.urlopen(url,timeout=25) as f:
  b=f.read(8000001)
  if len(b)>8000000:raise ValueError('cap 8MB')
  (L/'sources/fresh-delta.json').write_bytes(b);d=json.loads(b);r.update(status=f.status,sha256=hashlib.sha256(b).hexdigest(),commits=d.get('total_commits'),files=len(d.get('files',[])),complete_file_list=len(d.get('files',[]))<300)
  for x in d.get('files',[]):
   if pat.search(x['filename']+' '+x.get('patch','')):print('current matching',x['filename'])
except Exception as e:r.update(error=str(e),status=getattr(e,'code',None))
with (L/'http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
print(json.dumps(r))
