import pathlib,hashlib,json,sys,urllib.request,datetime,subprocess
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,x):
 p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2)+'\n')
def freeze(paths):
 out=[]
 for p in paths:
  p=pathlib.Path(p).resolve(); h=sha(p); q=L/'frozen'/p.name
  if q.exists() and sha(q)!=h: q=L/'frozen'/(h[:12]+'-'+p.name)
  q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes())
  assert sha(p)==sha(q)==h
  out.append(dict(original=str(p),copy=str(q),sha256=h))
 return out
if sys.argv[1]=='init':
 for name in ['ledger.json','prior-campaign-context.json','AGENTS.md']:
  p=B/name; q=L/'administrative'/name;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes())
 paths=[L.parent/x/'SCOUTING.md' for x in ['sol-wide-discrete-mechanism-r226','sol-wide-new-analysis-r227','sol-seidel-switching-breadth-depth-r228']]
 save(L/'frozenbindings.json',freeze(paths))
 print('history frozen',len(paths))
elif sys.argv[1]=='freeze':
 old=json.loads((L/'frozenbindings.json').read_text());old+=freeze(sys.argv[2:]);save(L/'frozenbindings.json',old)
elif sys.argv[1]=='get':
 name,url=sys.argv[2:];q=L/'primary'/name;q.parent.mkdir(parents=True,exist_ok=True)
 r=dict(url=url,date=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source inspection (bounded)'}),timeout=35) as f:
   r.update(status=f.status,final_url=f.url); data=f.read(10_000_001)
  assert len(data)<=10_000_000
  q.write_bytes(data);r.update(sha256=sha(q),bytes=len(data))
  # Freeze before content extraction/read.
  old=json.loads((L/'frozenbindings.json').read_text());old+=freeze([q]);save(L/'frozenbindings.json',old)
  if name.endswith('.pdf'):
   subprocess.run(['pdftotext','-layout',str(q),str(q.with_suffix('.txt'))],check=True,timeout=30)
 except Exception as e:r['failure']=repr(e)
 with (L/'primaryreceipts.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(json.dumps(r))
elif sys.argv[1]=='history':
 terms=sys.argv[2:];out=[]
 for p in B.joinpath('lanes').glob('*/SCOUTING.md'):
  if p.parent==L:continue
  # Bind originals before any semantic read, retaining compact references only.
  h=sha(p);s=p.read_text(errors='replace');assert sha(p)==h
  hits=[t for t in terms if t.lower() in s.lower()]
  if hits:out.append(dict(path=str(p),sha256=h,terms=hits,lines=[x[:900] for x in s.splitlines() if any(t.lower() in x.lower() for t in hits)][:8]))
 save(L/'history-screen.json',out); print(json.dumps(out)[:22000])
elif sys.argv[1]=='admin':
 for n in ['ledger.json','prior-campaign-context.json']:
  d=json.loads((L/'administrative'/n).read_text())
  print(n, list(d))
  for k,v in d.items():
   if isinstance(v,list):
    for x in v:
     if isinstance(x,dict): print(k,json.dumps({a:b for a,b in x.items() if a in ['title','scope','source_target','reason','status','note']}))
elif sys.argv[1]=='oldaliases':
 root=B.parent.parent/'2026-10-26'/'new-discoveries'
 terms=sys.argv[2:];out=[];bindings=[]
 for sub in ['lanes','candidates']:
  for p in root.joinpath(sub).glob('*/SUMMARY.md'):
   h=sha(p);bindings.append(dict(original=str(p),sha256=h));s=p.read_text(errors='replace');assert sha(p)==h
   hits=[t for t in terms if t.lower() in s.lower()]
   if hits:out.append(dict(path=str(p),sha256=h,terms=hits))
 save(L/'old-history-bindings.json',bindings);save(L/'old-alias-screen.json',out);print(json.dumps({'files':len(bindings),'hits':out}))
