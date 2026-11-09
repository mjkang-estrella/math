import pathlib,hashlib,json,sys,urllib.request,urllib.error,subprocess,time,shutil
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def log(name,x):
 with (L/name).open('a') as f:f.write(json.dumps(x)+'\n')
def freeze(p,category):
 p=pathlib.Path(p).resolve(); d=L/category/p.name; d.parent.mkdir(parents=True,exist_ok=True)
 a=sha(p);shutil.copyfile(p,d);assert a==sha(d)==sha(p)
 log('bindings.jsonl',dict(original=str(p),copy=str(d.relative_to(L)),sha256=a,category=category));return d
if sys.argv[1]=='init':
 for p in [B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',L.parents[5]/'AGENTS.md']:
  if p.exists():freeze(p,'administrative')
 for p in [B/'lanes/root-scout-r288-disposition/STATUS.md',B/'lanes/sol-csordas-forgacs-czds-preliminary-review-r1/SCOUTING.md']:
  d=freeze(p,'history');print(d.read_text())
elif sys.argv[1]=='fetch':
 name,url=sys.argv[2:4];p=L/'primary'/name;p.parent.mkdir(exist_ok=True)
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Research-source-reader/1.0'})
  with urllib.request.urlopen(req,timeout=35) as r:
   body=r.read(12*1024*1024);status=r.status; final=r.url
  p.write_bytes(body);log('access.jsonl',dict(url=url,final=final,status=status,file=str(p.relative_to(L)),sha256=sha(p),bytes=len(body),time=time.time()))
  print(name,status,len(body),sha(p))
 except Exception as e:log('access.jsonl',dict(url=url,error=str(e),time=time.time()));print('FAILED',url,str(e))
elif sys.argv[1]=='text':
 p=L/'primary'/sys.argv[2];a=sha(p);d=L/'texts'/(p.stem+'.txt');d.parent.mkdir(exist_ok=True)
 subprocess.run(['pdftotext','-layout',str(p),str(d)],check=True);assert a==sha(p)
 log('derivations.jsonl',dict(source=str(p.relative_to(L)),sha256=a,text=str(d.relative_to(L)),text_sha256=sha(d)))
elif sys.argv[1]=='dedup':
 q=sys.argv[2];r=subprocess.run(['rg','-i','-l','--glob','*.md','--glob','*.json',q,str(B/'lanes'),str(L.parents[5]/'frontier/sources')],capture_output=True,text=True)
 paths=[p for p in r.stdout.splitlines() if str(L) not in p and '/administrative/' not in p and '/frozen/' not in p and '/inputs/' not in p]
 log('alias-checks.jsonl',dict(query=q,paths=paths));print('\n'.join(paths[:35]),'TOTAL',len(paths))
elif sys.argv[1]=='html':
 from html.parser import HTMLParser
 class P(HTMLParser):
  def handle_data(self,s):
   if s.strip():print(s[:2200])
 p=L/'primary'/sys.argv[2];a=sha(p);P().feed(p.read_text());assert a==sha(p)
