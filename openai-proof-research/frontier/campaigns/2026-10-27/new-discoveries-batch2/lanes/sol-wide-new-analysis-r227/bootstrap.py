import pathlib,hashlib,json,shutil,datetime
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
(L/'administrative').mkdir(exist_ok=True)
for n in ['AGENTS.md','ledger.json','prior-campaign-context.json']:
 shutil.copyfile(B/n,L/'administrative'/n)
refs=[]
for name in ['sol-stable-persistence-breadth-depth-r225','sol-multiplier-breadth-depth-r224','sol-wide-discrete-mechanism-r226']:
 for n in ['SUMMARY.md','SCOUTING.md','discovery.md']:
  p=L.parent/name/n
  if p.exists():
   h=sha(p); q=L/'frozen'/name/n;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
   assert sha(p)==sha(q)==h
   refs.append({'original':str(p),'copy':str(q),'sha256':h})
(L/'freeze.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'refs':refs},indent=2))
for r in refs:
 print('\nREFERENCE',r['copy']);print(pathlib.Path(r['copy']).read_text()[:16000])
for n in ['ledger.json','prior-campaign-context.json']:
 d=json.loads((L/'administrative'/n).read_text());print(n,'keys',list(d))
 print(json.dumps({k:v for k,v in d.items() if k in ['accepted_count','total_accepted_count','next_global_outcome_number','accepted','published_papers']})[:14000])
