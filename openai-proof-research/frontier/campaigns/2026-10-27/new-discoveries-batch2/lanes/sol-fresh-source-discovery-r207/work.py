from pathlib import Path
import json, hashlib, datetime, urllib.request, urllib.error, sys, re, subprocess
L=Path(__file__).resolve().parent; B=L.parents[1]
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(b): return hashlib.sha256(b).hexdigest()
def save(n,x): (L/n).write_text(json.dumps(x,indent=2)+'\n')
def bind(p,n):
 b=p.read_bytes(); c=L/n;c.parent.mkdir(parents=True,exist_ok=True);c.write_bytes(b)
 assert sha(p.read_bytes())==sha(c.read_bytes())==sha(b)
 return dict(original=str(p.resolve()),copy=n,sha256=sha(b))
if sys.argv[1]=='init':
 base=L.parent/'sol-fresh-source-discovery-r204'; rows=json.loads((base/'history-receipt.json').read_text())['records']; known={x['original']:x for x in rows}
 for d in L.parent.iterdir():
  if d.is_dir() and d!=L:
   for p in d.iterdir():
    if p.is_file() and p.name.lower() in {'summary.md','discovery.md','proof.md','review.md','decision.md'}:known.setdefault(str(p.resolve()),{'original':str(p.resolve()),'sha256':None})
 refreshed=[];changed=[]
 for i,(p,x) in enumerate(sorted(known.items())):
  f=Path(p)
  if not f.exists():refreshed.append(dict(original=p,missing=True));continue
  h=sha(f.read_bytes());rec=dict(original=p,sha256=h,previous=x.get('sha256'))
  if h!=x.get('sha256'):
   rec.update(bind(f,f'changed/{i}.md'));changed.append(rec)
  else:rec['snapshot_reference']=str(base/x['copy'])
  refreshed.append(rec)
 save('qualified-original-index.json',dict(utc=now(),base_index=str(base/'history-receipt.json'),records=refreshed))
 save('changed-records.json',changed)
 indexes=[]
 for p in (base/'indexes').iterdir():indexes.append(bind(p,'indexes/'+p.name))
 indexes.append(bind(base/'history-receipt.json','indexes/r204.json'))
 if (base/'alias-refresh.json').exists():indexes.append(bind(base/'alias-refresh.json','indexes/inherited-aliases.json'))
 save('index-bindings.json',indexes)
 for n in ['ledger.json','NEXT.md','prior-campaign-context.json','AGENTS.md']:bind(B/n,'administrative/'+n)
 print('qualified',len(refreshed),'changed',len(changed));print('\n'.join(x['original'] for x in changed))
elif sys.argv[1]=='fetch':
 (L/'sources').mkdir(exist_ok=True)
 for a in sys.argv[2:]:
  n,u=a.split('=',1);rec=dict(utc=now(),url=u,file=n)
  try:
   assert not any(s in u.lower() for s in ['github','codeload','sciencedirect','google.','export.arxiv'])
   assert not (L/'http.jsonl').exists() or u not in (L/'http.jsonl').read_text(),'no retries'
   with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Mathematical research'}),timeout=25) as f:
    b=f.read(14000001);assert len(b)<=14000000;rec.update(status=f.status,final_url=f.url)
   (L/'sources'/n).write_bytes(b);rec.update(sha256=sha(b),bytes=len(b))
   rec['binding']=bind(L/'sources'/n,'frozen/'+n)
  except Exception as e:
   rec['error']=repr(e)
   if isinstance(e,urllib.error.HTTPError):
    b=e.read(100000);(L/'sources'/(n+'.error')).write_bytes(b);rec['error_sha256']=sha(b)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
  print(json.dumps(rec))
elif sys.argv[1]=='screen':
 pat=re.compile(sys.argv[2],re.I);hits=[]
 for x in json.loads((L/'qualified-original-index.json').read_text())['records']:
  if x.get('missing'):continue
  p=L/x['copy'] if 'copy' in x else Path(x['snapshot_reference']);b=p.read_bytes();assert sha(b)==x['sha256']
  s=b.decode(errors='replace');ms=list(pat.finditer(s))
  if ms:hits.append(dict(original=x['original'],sha256=x['sha256'],excerpts=[s[max(0,m.start()-100):m.end()+220] for m in ms[:5]]))
 save(sys.argv[3],dict(utc=now(),pattern=pat.pattern,hits=hits));print(json.dumps(hits)[:24000])
