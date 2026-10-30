from pathlib import Path
import json, hashlib, datetime, urllib.request, urllib.error, sys, re
L=Path(__file__).resolve().parent
B=L.parent.parent
R=B.parents[3]
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(b): return hashlib.sha256(b).hexdigest()
def put(p,b):
 p=L/p;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b if isinstance(b,bytes) else b.encode())
def js(p,x): put(p,json.dumps(x,indent=2)+'\n')
def fetch(name,url):
 t=now();rec={'utc':t,'url':url}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source verification (bounded public academic retrieval)'}),timeout=35) as q:
   data=q.read(16000000);rec.update(status=q.status,final_url=q.url,headers=dict(q.headers))
  put('primary/original/'+name,data);put('primary/copy/'+name,data)
  rec.update(sha256=sha(data),bytes=len(data),frozen_before_read=True)
 except Exception as e:
  rec['failure']=repr(e)
  if isinstance(e,urllib.error.HTTPError):
   data=e.read();put('failures/'+name,data);rec['body_sha256']=sha(data)
 js('retrieval/'+name+'.json',rec);print(json.dumps(rec));return rec
def setup():
 js('administrative/snapshot.json',{'utc':now(),'note':'Mutable administrative snapshot only, not scientific input','counts':[9,39,40]})
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
  if (B/n).exists():put('administrative/'+n,(B/n).read_bytes())
 inputs=[R/'AGENTS.md',B/'AGENTS.md']
 inputs += [B/f'lanes/root-r{r}-handback/DECISION.md' for r in [193,194,197,199,201,202,203,204]]
 inputs += [B/f'lanes/sol-fresh-source-discovery-r{r}/SUMMARY.md' for r in [202,203,204]]
 bindings=[]
 for i,p in enumerate(inputs):
  if p.exists():
   d=p.read_bytes();c=f'assigned/{i}-{p.name}';put(c,d);bindings.append({'original':str(p),'copy':c,'sha256':sha(d),'kind':'historical snapshot'})
 js('assigned-bindings.json',bindings)
 idx=B/'lanes/sol-fresh-source-discovery-r205/indexes'
 print('indexes',[(p.name,p.stat().st_size) for p in idx.iterdir()])
 for n in ['index-bindings.json','legacy-alias-refresh.json']:
  x=json.loads((idx.parent/n).read_text());print(n, str(x)[:1800])
 print('repo root',R)
def refresh():
 idx=B/'lanes/sol-fresh-source-discovery-r205/indexes';paths={};indexbindings=[]
 for p in [idx.parent/'history-receipt.json']:
  data=p.read_bytes();x=json.loads(data);indexbindings.append({'path':str(p),'sha256':sha(data)})
  for r in x.get('records',[]):
   if isinstance(r,dict):o=r.get('original');h=r.get('sha256')
   else:o=r[0];h=r[1]
   if not o:continue
   q=Path(o);q=q if q.is_absolute() else R/q
   paths[str(q)]=h
 # Only direct top-level reports in actual lane directories; no recursive history promotion.
 for lane in B.joinpath('lanes').iterdir():
  if lane==L or not lane.is_dir():continue
  for n in ['SUMMARY.md','discovery.md','DECISION.md','review.md','PROOF.md']:
   p=lane/n
   if p.exists():paths.setdefault(str(p),None)
 records=[]
 for o,old in sorted(paths.items()):
  p=Path(o)
  if not p.exists():records.append({'original':o,'missing':True});continue
  d=p.read_bytes();h=sha(d);changed=h!=old
  rec={'original':o,'sha256':h,'previous':old,'changed_or_new':changed}
  previous=next((r for r in x.get('records',[]) if isinstance(r,dict) and r.get('original')==o),None)
  if not changed and previous and previous.get('copy'):
   cp=idx.parent/previous['copy']
   assert sha(cp.read_bytes())==h
   rec['reused_snapshot']=str(cp)
  if changed:
   c='history-delta/'+sha(o.encode())[:24]+'-'+p.name;put(c,d);rec['snapshot']=c
  records.append(rec)
 js('qualified-original-index.json',{'utc':now(),'upstream_indexes':indexbindings,'records':records,'qualification':'Inherited index provenance retained; path membership does not independently authenticate every inherited original. Equal bytes do not prove provenance. No recursive discovery.'})
 print('refresh',len(records),'changed/new',sum(r.get('changed_or_new',False) for r in records),'missing',sum(r.get('missing',False) for r in records))
 # Keep inherited aliases in their own provenance class, without treating them as originals.
 a=B/'lanes/sol-fresh-source-discovery-r205/legacy-alias-refresh.json';d=a.read_bytes();put('indexes/inherited-aliases.json',d)
 js('indexes/inherited-alias-binding.json',{'path':str(a),'sha256':sha(d),'qualification':'Inherited aliases only, not promoted originals'})
def screen(terms,label):
 x=json.loads((L/'qualified-original-index.json').read_text());hits={t:[] for t in terms}
 for r in x['records']:
  if r.get('missing'):continue
  p=L/r['snapshot'] if 'snapshot'in r else Path(r.get('reused_snapshot',r['original']))
  s=p.read_text(errors='replace').lower()
  for t in terms:
   if t.lower() in s:hits[t].append(r['original'])
 js(label,{'utc':now(),'terms':hits,'bounded_originals':len(x['records']),'limits':'Qualified canonical paths only; no clearance of all history or live public registries.'});print(json.dumps({t:v[:12] for t,v in hits.items()},indent=2))
if __name__=='__main__':
 if sys.argv[1]=='setup':setup()
 elif sys.argv[1]=='refresh':refresh()
 elif sys.argv[1]=='fetch':fetch(sys.argv[2],sys.argv[3])
 elif sys.argv[1]=='screen':screen(sys.argv[3:],sys.argv[2])
