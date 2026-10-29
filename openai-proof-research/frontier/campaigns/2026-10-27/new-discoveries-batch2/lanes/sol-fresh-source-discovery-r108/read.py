from pathlib import Path
import urllib.request,json,hashlib
from html.parser import HTMLParser
L=Path(__file__).parent;records=[]
class P(HTMLParser):
 def __init__(self):super().__init__();self.a=[]
 def handle_data(self,d):self.a.append(d)
def get(n,u):
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'research-source-check'}),timeout=25) as r:b=r.read();status=r.status
  (L/'sources'/n).write_bytes(b);records.append({'name':n,'url':u,'status':status,'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b)})
  if 'arxiv.org/html/' in u:
   p=P();p.feed(b.decode());(L/'sources'/(n+'.txt')).write_text(' '.join(p.a))
  return b
 except Exception as e:records.append({'name':n,'url':u,'error':str(e)});return b''
get('sahbi.raw','https://arxiv.org/html/2610.03785')
get('sahbi-abs.raw','https://arxiv.org/abs/2610.03785')
get('covers.raw','https://arxiv.org/html/2610.29846')
get('omega-HEAD.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD')
get('openai-HEAD.json','https://api.github.com/repos/openai/math/commits/HEAD')
(L/'http.json').write_text(json.dumps(records,indent=2))
for n in ['sahbi.raw','covers.raw']:
 p=L/'sources'/(n+'.txt')
 if p.exists():
  s=p.read_text();print(n)
  import re
  for m in re.finditer(r'Conjecture|References|star-forming set',s):print(s[max(0,m.start()-250):m.start()+2200])
