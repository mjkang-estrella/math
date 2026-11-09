import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(30,30));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,re,hashlib,time
from html.parser import HTMLParser
L=pathlib.Path(__file__).resolve().parent;t=time.monotonic()
class P(HTMLParser):
 def __init__(self):super().__init__();self.o=[];self.m=0;self.s=0
 def handle_starttag(self,t,a):
  d=dict(a)
  if t=='math':self.m+=1;self.o.append(' $'+d.get('alttext','')+'$ ')
  if t in ['script','style']:self.s+=1
  if t in ['p','div','section','h1','h2','h3','h4','li','tr']:self.o.append('\n')
 def handle_endtag(self,t):
  if t=='math':self.m-=1
  if t in ['script','style']:self.s-=1
 def handle_data(self,x):
  if not self.m and not self.s:self.o.append(x)
for n in ['tensor-companion','tensor-companion-abs','packing-companion','packing-companion-abs','365524-v1','365524-v2']:
 p=P();p.feed((L/f'sources/{n}.html').read_text());txt=re.sub(r'[ \t\r\f\v]+',' ',''.join(p.o));txt=re.sub('\n+','\n',txt);(L/f'text/{n}.txt').write_text(txt)
 if n=='tensor-companion':print(txt[1000:20000])
 if n=='packing-companion':
  for m in list(re.finditer('rigid|stress|six',txt,re.I))[:6]:print('PACK',txt[max(0,m.start()-160):m.start()+700])
for n in ['pool-main','openai-math']:
 txt=(L/f'sources/{n}.html').read_text();print('HEAD',n,re.findall(r'"currentOid":"([0-9a-f]+)"',txt)[:3]);print('LINKS',n,[x for x in re.findall(r'href="([^"]+)"',txt) if 'candidate' in x or 'projects' in x][:15])
# semantic ID matches, distinct from arbitrary hash-string hits
matches=[]
for h in json.loads((L/'history-matches.json').read_text()):
 def walk(x,path=''):
  if isinstance(x,dict):
   if str(x.get('mathdb_id',x.get('id',''))) in h['id_hits']:matches.append({'path':h['path'],'record':x})
   for k,v in x.items():
    if str(k) in h['id_hits']:matches.append({'path':h['path'],'record':v})
    elif isinstance(v,(dict,list)):walk(v,path+'/'+str(k))
  elif isinstance(x,list):
   for v in x:walk(v,path)
 walk(h['content'])
(L/'history-semantic-matches.json').write_text(json.dumps(matches,indent=2)+'\n');print('ACTUAL ID matches',len(matches))
(L/'resource-review-follow.json').write_text(json.dumps({'exit':0,'wall':time.monotonic()-t,'self':list(resource.getrusage(resource.RUSAGE_SELF))})+'\n')
