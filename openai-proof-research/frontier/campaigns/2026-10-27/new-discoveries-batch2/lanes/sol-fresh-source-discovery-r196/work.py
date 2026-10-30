from pathlib import Path
import json,hashlib,datetime,sys,os,re,urllib.request,subprocess
L=Path(__file__).resolve().parent; B=L.parents[1]; R=L.parents[5]
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,x):(L/n).write_text(json.dumps(x,indent=2)+'\n')
mode=sys.argv[1]
if mode=='setup':
 for n in ['NEXT.md','ledger.json','prior-campaign-context.json']:(L/('snapshot-'+n)).write_bytes((B/n).read_bytes())
 pairs=[]
 def bind(p,q):
  b=p.read_bytes();h=sha(b);q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
  assert sha(p.read_bytes())==h==sha(q.read_bytes());pairs.append(dict(original=str(p.resolve()),copy=str(q.relative_to(L)),sha256=h))
 old=B/'lanes/sol-fresh-source-discovery-r193'; base=json.loads((old/'history-receipt.json').read_text()); records={r[0]:r for r in base['records']}
 # Preserve every inherited actual path, including provenance aliases; never promote generated inventories.
 names={'SUMMARY.md','discovery.md','PROOF.md','review.md','DECISION.md'}
 prune={'originals','frozen','inputs','context','packet','private','history','copies','source','sources','verification','extracted','node_modules','.git','assigned-inputs'}
 for root,ds,fs in os.walk(R/'frontier/campaigns'):
  ds[:]=[d for d in ds if d not in prune and not d.startswith(('verification','freeze','frozen','extracted'))]
  if Path(root)==L:ds[:]=[];continue
  for n in fs:
   if n in names:
    p=Path(root)/n;rel=str(p.relative_to(R));records.setdefault(rel,[rel,'',0])
 changed=[];missing=[];out=[]
 for rel,prev,z in sorted(records.values()):
  p=R/rel
  if not p.is_file():missing.append(rel);continue
  b=p.read_bytes();h=sha(b)
  if h!=prev:changed.append(rel)
  bind(p,L/'originals'/rel);out.append([rel,h,len(b)])
 for p in [R/'AGENTS.md',B/'AGENTS.md',old/'history-receipt.json',old/'inherited-access.json',R.parent/'sources/upstream.json',R/'sources/upstream.json',R/'sources/CONTENTS.md']:
  if p.is_file():bind(p,L/'context'/p.name)
 for r in [191,192,193]:
  d=B/'lanes'/f'sol-fresh-source-discovery-r{r}'
  for n in ['SUMMARY.md','discovery.md','FAILURES.md','http.jsonl','provenance.json']:
   if (d/n).is_file():bind(d/n,L/'context'/f'r{r}-{n}')
 groups={}
 for p,h,z in out:groups.setdefault(h,[]).append(p)
 save('history-receipt.json',dict(utc=now(),base_records=len(base['records']),records=out,aliases=groups,changed=changed,missing=missing,distinct_bodies=len(groups),limit='bounded direct-original refresh; inherited aliases retained; not all-history clearance'))
 save('scientific-input-freeze.json',pairs)
 print(dict(records=len(out),distinct=len(groups),changed=changed,missing=missing))
elif mode=='fetch':
 (L/'sources').mkdir(exist_ok=True)
 denied=(L/'context/inherited-access.json').read_text();existing=(L/'http.jsonl').read_text() if (L/'http.jsonl').exists() else ''
 for a in sys.argv[2:]:
  n,u=a.split('=',1);r=dict(utc=now(),name=n,url=u)
  try:
   assert not any(s in u.lower() for s in ['github','codeload','sciencedirect','google.','arxiv.org/search','export.arxiv','api.crossref'])
   assert u not in denied and u not in existing,'inherited/already attempted URL; no retry'
   with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Mathematical-source-research/1.0'}),timeout=25) as f:
    b=f.read(10000001);assert len(b)<=10000000;(L/'sources'/n).write_bytes(b);r.update(status=f.status,final_url=f.url,sha256=sha(b),bytes=len(b))
  except Exception as e:r['error']=repr(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
  print(r)
elif mode=='extract':
 for p in (L/'sources').glob('*.pdf'):
  if p.read_bytes().startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
elif mode=='audit':
 pat=re.compile(sys.argv[2],re.I);hits=[]
 for p,h,z in json.loads((L/'history-receipt.json').read_text())['records']:
  s=(L/'originals'/p).read_text(errors='replace');ms=list(pat.finditer(s))
  if ms:hits.append(dict(path=p,sha256=h,excerpts=[s[max(0,m.start()-120):m.end()+180] for m in ms[:3]]))
 save(sys.argv[3],dict(utc=now(),pattern=pat.pattern,hits=hits));print(json.dumps(hits)[:18000])
