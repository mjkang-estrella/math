from pathlib import Path
import json,hashlib,sys,urllib.request,datetime,subprocess
b=Path(__file__).resolve().parent;l=b.parent
def digest(x):return hashlib.sha256(x).hexdigest()
if sys.argv[1]=='prepare':
 f=l/'root-mmpp-survival-review-freeze-r1/review-freeze.json';d=json.loads(f.read_text());out={}
 for n,h in d['files'].items():
  x=(Path(d['source_lane'])/n).read_bytes();assert digest(x)==h,n
  p=b/'copy'/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(x);out[n]=h
 (b/'review-freeze.json').write_bytes(f.read_bytes());(b/'before.json').write_text(json.dumps(out,indent=2))
 context={}
 for p in [l.parent/'AGENTS.md',l.parent/'NEXT.md',l.parent/'ledger.json',l.parent/'prior-campaign-context.json',l/'sol-mmpp-survival-preliminary-review-r1/review.md',l/'sol-mmpp-survival-preliminary-review-r1/provenance.json',l/'root-edge-irregulator-final-freeze-r1/CURRENT-REGISTRIES.json']:
  x=p.read_bytes();context[str(p)]={'sha256':digest(x),'bytes':len(x)}
  q=b/'context'/p.parent.name/p.name;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(x)
  if p.suffix=='.json':
   z=json.loads(x)
   if p.name=='ledger.json':print('ledger',json.dumps({k:v for k,v in z.items() if k not in ['accepted','excluded']},indent=2)[:12000]);print('accepted',[(v.get('number'),v.get('title')) for v in z.get('accepted',[])])
 (b/'context-read.json').write_text(json.dumps(context,indent=2));print('verified copied',len(out))
elif sys.argv[1]=='fetch':
 logs=json.loads((b/'http.json').read_text()) if (b/'http.json').exists() else []
 for n,url in json.loads(sys.argv[2]):
  z={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'name':n}
  try:
   with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'mathematical-historical-review/1.0'}),timeout=30) as r:x=r.read(24000000);z.update(status=r.status,final_url=r.url,sha256=digest(x),bytes=len(x))
   p=b/'sources'/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(x)
   if x.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
  except Exception as e:z['error']=str(e)
  logs.append(z);print(z)
 (b/'http.json').write_text(json.dumps(logs,indent=2))
elif sys.argv[1]=='finish':
 d=json.loads((b/'review-freeze.json').read_text());out={}
 for n,h in d['files'].items():
  assert digest((Path(d['source_lane'])/n).read_bytes())==h,n
  assert digest((b/'copy'/n).read_bytes())==h,n
  out[n]=h
 (b/'after.json').write_text(json.dumps(out,indent=2));print('originals and copies verified',len(out))
 hashes={str(p.relative_to(b)):digest(p.read_bytes()) for p in sorted(b.rglob('*')) if p.is_file() and p.name!='evidence-hashes.json'}
 (b/'evidence-hashes.json').write_text(json.dumps(hashes,indent=2)+'\n')
