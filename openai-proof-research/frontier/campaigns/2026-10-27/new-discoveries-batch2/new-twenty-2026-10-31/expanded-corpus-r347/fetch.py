from html.parser import HTMLParser
class Parser(HTMLParser):
 def __init__(self): super().__init__(); self.out=[]; self.skip=0
 def handle_starttag(self,t,a):
  a=dict(a)
  if t in ['script','style']: self.skip+=1
  if t in ['p','div','section','h1','h2','h3','li','tr']: self.out.append('\n')
  if t in ['img','math'] and a.get('alttext',a.get('alt')): self.out.append(a.get('alttext',a.get('alt')))
 def handle_endtag(self,t):
  if t in ['script','style']: self.skip=max(0,self.skip-1)
 def handle_data(self,d):
  if not self.skip:self.out.append(d)
def fetch(job):
 name,url=job; utc=datetime.datetime.now(datetime.timezone.utc).isoformat(); rec={'name':name,'url':url,'utc':utc,'method':'GET','read_depth':'acquired only'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical source review (public GET)'}),timeout=12) as f:
   b=f.read(20*1024**2); rec.update(status=f.status,final_url=f.url,bytes=len(b),sha256=sha(b)); write('sources/'+name+'.raw',b)
  if not b.startswith(b'%PDF'):
   parser=Parser(); parser.feed(b.decode(errors='replace')); write('sources/'+name+'.txt',''.join(parser.out))
 except Exception as e: rec.update(error=str(e),status=getattr(e,'code',None))
 save('http/'+name+'.json',rec); return rec
r=json.loads(read(L/'reservation.json')); jobs=[]
for a in sorted(set(x['source_url'].split('/')[-1] for x in r['rows'])):
 jobs.extend([(a+'-abs','https://arxiv.org/abs/'+a),(a+'-html','https://arxiv.org/html/'+a)])
jobs.extend([('leanpool','https://leanpool.com/'),('formalconjectures','https://github.com/google-deepmind/formal-conjectures'),('leanpool-projects','https://raw.githubusercontent.com/leanprover-community/leanprover-community.github.io/master/projects.yml')])
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for x in ex.map(fetch,jobs): print(json.dumps(x))
