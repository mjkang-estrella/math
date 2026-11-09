import pathlib,hashlib,json,urllib.request,datetime,sys,subprocess
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
R=B.parents[3]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,x): p.write_text(json.dumps(x,indent=2))
def freeze(p,admin=False):
 d=L/('admin' if admin else 'science');d.mkdir(exist_ok=True)
 q=d/(p.parent.name+'--'+p.name); h=sha(p);q.write_bytes(p.read_bytes());assert sha(p)==sha(q)==h
 with (L/'bindings.jsonl').open('a') as f:f.write(json.dumps(dict(original=str(p),copy=str(q),sha256=h,administrative=admin))+'\n')
 return q
def fetch(url,name):
 p=L/'primary'/name;p.parent.mkdir(exist_ok=True)
 rec=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research-source-verification/1.0'}),timeout=35) as r:
   b=r.read(12000001);assert len(b)<=12000000
   p.write_bytes(b);rec.update(status=r.status,bytes=len(b),sha256=sha(p))
 except Exception as e:rec['error']=str(e)
 with (L/'access.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 return p
if __name__=='__main__':
 if sys.argv[1]=='init':
  for p in [B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',R/'AGENTS.md']:
   if p.exists():freeze(p,True)
  for p in [R/'sources/upstream.json',R/'sources/CONTENTS.md',L.parent/'sol-wide-analytic-uniform-mechanisms-r264/SCOUTING.md',L.parent/'sol-wide-analytic-uniform-mechanisms-r264/science/history-index.json',L.parent/'root-taylor-domination-disposition-r2/STATUS.md']:
   if p.exists():freeze(p)
  for p in (L/'admin').glob('*'):print(p.name,p.read_text()[:1000])
  for p in (L/'science').glob('*SCOUTING*'):print(p.read_text())
 elif sys.argv[1]=='fetch':freeze(fetch(sys.argv[2],sys.argv[3]))
 elif sys.argv[1]=='list':
  import xml.etree.ElementTree as E
  for e in E.parse(L/'primary'/sys.argv[2]).findall('{http://www.w3.org/2005/Atom}entry'):
   print(e.findtext('{http://www.w3.org/2005/Atom}id'),e.findtext('{http://www.w3.org/2005/Atom}title'),e.findtext('{http://www.w3.org/2005/Atom}summary')[:650])
 elif sys.argv[1]=='freeze':freeze(pathlib.Path(sys.argv[2]))
