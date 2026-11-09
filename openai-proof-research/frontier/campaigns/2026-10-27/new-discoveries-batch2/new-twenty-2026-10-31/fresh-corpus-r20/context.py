import os,resource,pathlib,json,re,hashlib
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(40,40));resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
p=pathlib.Path(__file__).resolve().parent;root=p.parents[4];ids=json.loads((p/'reservation.json').read_text())['ids'];rx=re.compile(r'(?<![0-9])(?:'+ '|'.join(map(str,ids))+r')(?![0-9])');hits=[];visited=0
for f in root.rglob('*'):
 if f.is_file() and f.suffix in ['.json','.md'] and f.stat().st_size<300000 and any(x in f.name.lower() for x in ['summary','review','reject','result','context','ledger'] ) and p not in f.parents:
  visited+=1
  try:t=f.read_text()
  except:continue
  if rx.search(t):
   hits.append({'path':str(f),'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'passages':[t[max(0,m.start()-250):m.end()+700] for m in rx.finditer(t)]})
(p/'prior-notes.json').write_text(json.dumps({'visited':visited,'limit':'named md/json files under campaign tree <=300kB; does not clear title-only/global notes','hits':hits},indent=2)+'\n');print('visited',visited,'hits',len(hits));print(json.dumps(hits,indent=2)[:26000])
