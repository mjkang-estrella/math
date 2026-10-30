import pathlib,sys,json,hashlib,datetime,urllib.request,urllib.error,shutil
L=pathlib.Path(__file__).resolve().parent
B=L.parent.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(n,x): (L/n).write_text(json.dumps(x,indent=2)+'\n')
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
if sys.argv[1]=='freeze':
 rows=[]
 for name in ['sol-fresh-source-discovery-r170','sol-dsbs-negative-preliminary-review-r1','root-dsbs-preliminary-adoption-r1']:
  for p in sorted((L.parent/name).rglob('*')):
   if p.is_file():
    rel=p.relative_to(L.parent);q=L/'copies'/rel;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
    rows.append(dict(original=str(p),copy=str(q.relative_to(L)),sha256=sha(p),copy_sha256=sha(q)))
 dump('before-hashes.json',rows)
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md','AGENTS.md']:
  (L/'context').mkdir(exist_ok=True);shutil.copyfile(B/n,L/'context'/n)
 print('frozen',len(rows))
elif sys.argv[1]=='get':
 name,url=sys.argv[2:4];d=L/'retrieved';d.mkdir(exist_ok=True)
 row=dict(utc=now(),url=url,name=name)
 try:
  r=urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source comparison (public documents)'}),timeout=25)
  data=r.read(16000000);row.update(status=r.status,final_url=r.url)
 except urllib.error.HTTPError as e:data=e.read(1000000);row.update(status=e.code,error=str(e))
 except Exception as e:data=b'';row.update(error=repr(e))
 (d/name).write_bytes(data);row.update(bytes=len(data),sha256=hashlib.sha256(data).hexdigest());dump('retrieved/'+name+'.receipt.json',row);print(json.dumps(row))
elif sys.argv[1]=='extract':
 from html.parser import HTMLParser
 class Parser(HTMLParser):
  def __init__(self):super().__init__();self.text=[];self.links=[];self.skip=0
  def handle_data(self,s):
   if not self.skip:self.text.append(s)
  def handle_endtag(self,t):
   if t in ['script','style']:self.skip=max(0,self.skip-1)
  def handle_starttag(self,t,a):
   if t in ['script','style']:self.skip+=1
   if t=='a':self.links.append(dict(a))
 for name in sys.argv[2:]:
  p=L/'retrieved'/name
  s=Parser();s.feed(p.read_text(errors='replace'))
  (p.with_suffix(p.suffix+'.txt')).write_text(' '.join(s.text))
  dump('retrieved/'+name+'.links.json',s.links)
elif sys.argv[1]=='verify-inputs':
 rows=json.loads((L/'before-hashes.json').read_text());out=[]
 for r in rows:
  a=sha(pathlib.Path(r['original']));c=sha(L/r['copy']);assert a==c==r['sha256'];out.append(dict(original=r['original'],copy=r['copy'],original_sha256=a,copy_sha256=c))
 dump('after-hashes.json',out);print('verified',len(out),'originals and copies; live NEXT deliberately excluded')
