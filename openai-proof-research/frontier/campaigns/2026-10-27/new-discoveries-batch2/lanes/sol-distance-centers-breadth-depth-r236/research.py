import pathlib,hashlib,json,shutil,os,urllib.request,datetime,subprocess
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
def sha(p): return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def save(n,v): (L/n).write_text(json.dumps(v,indent=2,ensure_ascii=False))
def freeze(p):
 p=pathlib.Path(p); h=sha(p); q=L/'frozen'/h/p.name; q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists(): shutil.copyfile(p,q)
 assert sha(p)==sha(q)==h
 with (L/'bindings.jsonl').open('a') as f:f.write(json.dumps({'original':str(p),'copy':str(q),'sha256':h})+'\n')
 return q
def fetch(url,name):
 record={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'mathematical-research/1.0'}),timeout=25) as r:
   data=r.read(12000000);record.update(status=r.status,final_url=r.url)
  p=L/'primary'/name;p.parent.mkdir(exist_ok=True);p.write_bytes(data);record['sha256']=sha(p);record['path']=str(p);freeze(p)
 except Exception as e: record['failure']=str(e)
 with (L/'retrieval.jsonl').open('a') as f:f.write(json.dumps(record)+'\n')
 return record
if __name__=='__main__':
 (L/'administrative').mkdir(exist_ok=True)
 for n in ['AGENTS.md','ledger.json','prior-campaign-context.json']: shutil.copyfile(B/n,L/'administrative'/n)
 for lane in ['sol-riesz-positive-persistence-r233','sol-wavelet-annulus-breadth-depth-r230']:
  for n in ['SCOUTING.md','ATTACK.md']:
   p=L.parent/lane/n
   if p.exists(): freeze(p)
 for p in (L.parent/'sol-riesz-positive-persistence-r233'/'primary').iterdir():
  if p.is_file(): freeze(p)
 print((L/'bindings.jsonl').read_text())
