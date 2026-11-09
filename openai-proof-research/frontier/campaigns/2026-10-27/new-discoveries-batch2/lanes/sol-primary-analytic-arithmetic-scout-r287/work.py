from pathlib import Path
import json,hashlib,datetime,urllib.request,subprocess,sys,re
L=Path(__file__).resolve().parent; B=L.parent.parent
def h(b):return hashlib.sha256(b).hexdigest()
def log(n,r):
 with (L/n).open('a') as f:f.write(json.dumps(r)+'\n')
def freeze(p,admin=False):
 p=Path(p).resolve(); d=p.read_bytes(); digest=h(d)
 q=L/('administrative' if admin else 'frozen')/(digest[:16]+'-'+p.name);q.parent.mkdir(exist_ok=True)
 if not q.exists():q.write_bytes(d)
 assert h(q.read_bytes())==digest==h(p.read_bytes())
 log('primarybindings.jsonl',dict(original=str(p),copy=str(q),sha256=digest,administrative=admin,utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
 return q
def read(p,a=0,b=15000):
 q=freeze(p);d=q.read_bytes();print(d.decode(errors='replace')[a:b]);assert h(d)==h(q.read_bytes())==h(Path(p).read_bytes())
def fetch(name,url):
 p=L/'primary'/name;p.parent.mkdir(exist_ok=True);r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'AcademicResearch/1.0'}),timeout=22) as u:d=u.read(10000000);r.update(status=u.status,final_url=u.url)
  if any(x in d[:30000].lower() for x in [b'captcha',b'cf-chl-',b'just a moment']):raise ValueError('challenge STOP')
  p.write_bytes(d);freeze(p);r.update(sha256=h(d),bytes=len(d))
  if d.startswith(b'%PDF'):
   subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True,timeout=25);freeze(p.with_suffix('.txt'))
 except Exception as e:r['failure']=repr(e);log('failures.jsonl',r)
 log('access.jsonl',r);print(json.dumps(r))
if __name__=='__main__':
 if sys.argv[1]=='init':
  for p in [B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B.parents[2]/'AGENTS.md']:
   if p.exists():freeze(p,True)
  for n in ['ledger.json','prior-campaign-context.json']:
   j=json.loads((B/n).read_text());print(n, list(j));print(json.dumps(j)[:1500])
 elif sys.argv[1]=='fetch':fetch(*sys.argv[2:])
 elif sys.argv[1]=='read':read(sys.argv[2],*[int(x) for x in sys.argv[3:]])
 elif sys.argv[1]=='questions':
  for n in sys.argv[2:]:
   p=Path(n);q=freeze(p);s=q.read_text(errors='replace');print('\nSOURCE',p,s[:900])
   for m in list(re.finditer(r'(?:Conjecture|Question|Problem|conjecture|question)\s+\d+[.\d]*',s))[:20]:print('OFFSET',m.start(),'PAGE',s[:m.start()].count('\f')+1,s[max(0,m.start()-120):m.start()+1900])
   assert h(p.read_bytes())==h(q.read_bytes())
