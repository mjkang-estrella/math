import pathlib,hashlib,json,urllib.request,datetime,sys
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
R=B.parents[3]
def sha(p): return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def save(p,x): pathlib.Path(p).write_text(json.dumps(x,indent=2))
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def freeze(p,admin=False):
 p=pathlib.Path(p).resolve();d=L/('admin' if admin else 'science');d.mkdir(exist_ok=True)
 q=d/(p.parent.name+'--'+p.name);h=sha(p);q.write_bytes(p.read_bytes());assert sha(p)==sha(q)==h
 with (L/'bindings.jsonl').open('a') as f:f.write(json.dumps(dict(original=str(p),copy=str(q),sha256=h,administrative=admin,utc=now()))+'\n')
 return q
def fetch(url,name):
 p=L/'primary'/name;p.parent.mkdir(exist_ok=True)
 rec=dict(url=url,utc=now(),name=name)
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research-source-verification/1.0'}),timeout=35) as r:
   b=r.read(12000001);assert len(b)<=12000000
   p.write_bytes(b);rec.update(status=r.status,bytes=len(b),sha256=sha(p),content_type=r.headers.get('Content-Type'))
 except Exception as e:
  rec['error']=str(e)
  if p.exists() and p.stat().st_size==0:p.unlink()
 with (L/'access.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(json.dumps(rec))
 return p
if __name__=='__main__':
 c=sys.argv[1]
 if c=='init':
  for p in [B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',R/'AGENTS.md',L.parent/'root-scout-r268-disposition/STATUS.md']:
   freeze(p,True)
  r=L.parent/'sol-wide-analytic-probabilistic-scout-r268'
  for n in ['SCOUTING.md','discovery.md','SUMMARY.md','FAILURES.md','primary/1801.07238v1.pdf','science/1801.07238v1.txt','check.py']:
   freeze(r/n)
 elif c=='fetch':
  p=fetch(sys.argv[2],sys.argv[3])
  if p.exists():freeze(p)
 elif c=='freeze':freeze(sys.argv[2])
 elif c=='list':
  import xml.etree.ElementTree as E
  A='{http://www.w3.org/2005/Atom}'
  for e in E.parse(L/'primary'/sys.argv[2]).findall(A+'entry'):
   print(e.findtext(A+'id'),'|',e.findtext(A+'published')[:10],'|',' '.join(e.findtext(A+'title').split()),'|',' '.join(e.findtext(A+'summary').split())[:int(sys.argv[3]) if len(sys.argv)>3 else 400]);print()
