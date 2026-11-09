from pathlib import Path
import json,hashlib,datetime,sys,urllib.request,urllib.error,re,subprocess
L=Path(__file__).resolve().parent; B=L.parents[1]
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,o):
 p=L/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(o,indent=2)+'\n')
def bind(p,n):
 b=p.read_bytes();q=L/n;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
 assert sha(p.read_bytes())==sha(q.read_bytes())==sha(b)
 return dict(original=str(p.resolve()),copy=n,sha256=sha(b),utc=now())
if sys.argv[1]=='init':
 known={}
 for lane,fn in [('sol-fresh-source-discovery-r209','qualified-original-index.json'),('sol-fresh-source-discovery-r210','history.json'),('sol-fresh-source-discovery-r211','qualified-original-index.json')]:
  p=L.parent/lane/fn
  bind(p,'indexes/'+lane+'.json')
  for r in json.loads(p.read_text())['records']:
   if not r.get('missing'):
    r=dict(r);r['snapshot_reference']=r.get('snapshot_reference',r.get('canonical_copy',str(p.parent/r.get('copy',''))));known[r['original']]=r
 for d in L.parent.iterdir():
  if d.is_dir() and d!=L:
   for p in d.iterdir():
    if p.is_file() and p.name.lower() in {'summary.md','discovery.md','proof.md','review.md','decision.md'}:known.setdefault(str(p.resolve()),dict(original=str(p.resolve())))
 out=[];changed=[]
 for i,(s,r) in enumerate(sorted(known.items())):
  p=Path(s)
  if not p.exists():out.append(dict(original=s,missing=True));continue
  h=sha(p.read_bytes());q=Path(r.get('snapshot_reference','/nonexistent'))
  if h!=r.get('sha256') or not q.is_file() or sha(q.read_bytes())!=h:
   z=bind(p,f'changed/{i}.md');z['snapshot_reference']=str(L/z.pop('copy'));changed.append(z)
  else:z=dict(original=s,sha256=h,snapshot_reference=str(q))
  out.append(z)
 save('qualified-original-index.json',dict(utc=now(),records=out,qualification='point-in-time historical references, not scientific premises'))
 save('changed-records.json',changed)
 a=json.loads((L.parent/'sol-fresh-source-discovery-r211/alias-refresh.json').read_text());save('inherited-aliases.json',a)
 for n in ['ledger.json','NEXT.md','prior-campaign-context.json','AGENTS.md']:bind(B/n,'administrative/'+n)
 print('originals',len(out),'changed',len(changed));print('\n'.join(x['original'] for x in changed))
elif sys.argv[1]=='fetch':
 for arg in sys.argv[2:]:
  n,u=arg.split('=',1);rec=dict(utc=now(),url=u,file='sources/'+n)
  try:
   assert not any(x in u.lower() for x in ['github','codeload','sciencedirect','google.'])
   assert not (L/'http.jsonl').exists() or u not in (L/'http.jsonl').read_text(),'no retry'
   with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Mathematical research'}),timeout=22) as f:
    b=f.read(12000001);assert len(b)<=12000000;rec.update(status=f.status,final_url=f.url)
   p=L/'sources'/n;p.parent.mkdir(exist_ok=True);p.write_bytes(b);rec.update(sha256=sha(b),bytes=len(b),binding=bind(p,'frozen/'+n))
  except Exception as e:
   rec['error']=repr(e)
   if isinstance(e,urllib.error.HTTPError):
    b=e.read(100000);p=L/'sources'/(n+'.error');p.parent.mkdir(exist_ok=True);p.write_bytes(b);rec['error_hash']=sha(b)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
  print(json.dumps(rec))
elif sys.argv[1]=='screen':
 pat=re.compile(sys.argv[2],re.I);hits=[]
 for r in json.loads((L/'qualified-original-index.json').read_text())['records']:
  if r.get('missing'):continue
  b=Path(r['snapshot_reference']).read_bytes();assert sha(b)==r['sha256'];s=b.decode(errors='replace');ms=list(pat.finditer(s))
  if ms:hits.append(dict(original=r['original'],excerpts=[s[max(0,m.start()-80):m.end()+160] for m in ms[:4]]))
 save(sys.argv[3],dict(utc=now(),pattern=pat.pattern,hits=hits));print(json.dumps(hits)[:21000])
