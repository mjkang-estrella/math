from pathlib import Path
import sys,json,hashlib,datetime,urllib.request,urllib.error,re,os,subprocess
L=Path(__file__).resolve().parent;B=L.parents[1];R=B.parents[3]
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,x):(L/n).write_text(json.dumps(x,indent=2)+"\n")
def bind(p,n):
 b=p.read_bytes();c=L/n;c.parent.mkdir(parents=True,exist_ok=True);c.write_bytes(b);assert sha(p.read_bytes())==sha(c.read_bytes())==sha(b)
 return dict(original=str(p),copy=n,sha256=sha(b))
if sys.argv[1]=='init':
 refs=[];known={}
 for r in [193,194,197,199,203]:
  p=L.parent/f'sol-fresh-source-discovery-r{r}'/'history-receipt.json';refs.append(bind(p,f'indexes/r{r}.json'))
 # Qualified canonical provenance comes from r195 and r198; legacy aliases retained above, never promoted.
 p=L.parent/'sol-fresh-source-discovery-r203/history-receipt.json';refs.append(bind(p,'indexes/r195-qualified.json'))
 for x in json.loads(p.read_text())['records']:known[x['original']]=x['sha256']
 p=L.parent/'sol-fresh-source-discovery-r198/scientific-freeze.json';refs.append(bind(p,'indexes/r198-freeze.json'))
 for x in json.loads(p.read_text()):
  if '/originals/' not in x['original'] and Path(x['original']).name.lower() in {'summary.md','discovery.md','proof.md','review.md','decision.md'}:known[x['original']]=x['sha256']
 # New direct lane records only, no recursion into copied histories.
 for d in (B/'lanes').iterdir():
  if not d.is_dir() or d==L:continue
  for f in d.iterdir():
   if f.is_file() and f.name.lower() in {'summary.md','discovery.md','proof.md','review.md','decision.md'}:known.setdefault(str(f),None)
 rows=[];changed=[]
 for p,h in sorted(known.items()):
  f=Path(p)
  if not f.exists():continue
  rec=bind(f,'originals/'+str(f.relative_to(R)));rec['previous']=h;rows.append(rec)
  if rec['sha256']!=h:changed.append(dict(**rec,body=f.read_text()))
 save('history-receipt.json',dict(utc=now(),records=rows,qualification='r195 qualified plus r198 original bindings and direct lane reports. Legacy r193/r194/r197 provenance aliases preserved in indexes; no equal-byte provenance inference.'))
 save('changed-records.json',changed);save('index-bindings.json',refs)
 # Active research records snapshots are mutable, excluded from settled scientific binding.
 active=[x for x in rows if any('/sol-fresh-source-discovery-r'+str(r)+'/' in x['original'] for r in range(195,206))]
 save('active-snapshots.json',active);save('scientific-freeze.json',[x for x in rows if x not in active]+refs)
 for n in ['NEXT.md','ledger.json','prior-campaign-context.json','AGENTS.md']:(L/('snapshot-'+n)).write_bytes((B/n).read_bytes())
 save('instruction-bindings.json',[bind(R/'AGENTS.md','context/ancestor-AGENTS.md')])
 print('qualified',len(rows),'changed',len(changed),'active',len(active));print('\n'.join(x['original'] for x in changed))
elif sys.argv[1]=='fetch':
 (L/'sources').mkdir(exist_ok=True)
 for a in sys.argv[2:]:
  n,u=a.split('=',1);rec=dict(utc=now(),url=u,file=n)
  try:
   assert not any(s in u.lower() for s in ['github','codeload','sciencedirect','google.','export.arxiv'])
   prior=(L/'http.jsonl').read_text() if (L/'http.jsonl').exists() else '';assert u not in prior,'no retries'
   with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Mathematical primary source research'}),timeout=25) as f:
    b=f.read(12000001);assert len(b)<=12000000;rec.update(status=f.status,final_url=f.url)
   (L/'sources'/n).write_bytes(b);rec.update(sha256=sha(b),bytes=len(b))
  except Exception as e:
   rec['error']=repr(e)
   if isinstance(e,urllib.error.HTTPError):
    b=e.read(100000);(L/'sources'/(n+'.error')).write_bytes(b);rec['error_sha256']=sha(b)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
  print(rec)
elif sys.argv[1]=='screen':
 pat=re.compile(sys.argv[2],re.I);hits=[]
 for x in json.loads((L/'history-receipt.json').read_text())['records']:
  s=(L/x['copy']).read_text();ms=list(pat.finditer(s))
  if ms:hits.append(dict(original=x['original'],sha256=x['sha256'],excerpts=[s[max(0,m.start()-100):m.end()+180] for m in ms[:5]]))
 save(sys.argv[3],dict(utc=now(),pattern=pat.pattern,hits=hits));print(json.dumps(hits)[:22000])
