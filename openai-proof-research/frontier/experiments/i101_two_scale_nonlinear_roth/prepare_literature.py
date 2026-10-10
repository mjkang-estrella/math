"""Preparation only. Not imported or run by the final verifier."""
from pathlib import Path
import urllib.request,urllib.error,json,hashlib
from html.parser import HTMLParser
S=Path('frontier/sources/i101_two_scale_nonlinear_roth/literature');S.mkdir(exist_ok=True)
class Text(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
  if t=='math':self.out.append(dict(a).get('alttext','')) ;self.skip+=1
  if t in ['p','div','section','h1','h2','h3','h4','h5','h6','li','tr']:self.out.append('\n')
 def handle_endtag(self,t):
  if t in ['script','style','math']:self.skip=max(0,self.skip-1)
  if t in ['p','div','section','h1','h2','h3','h4','h5','h6','li','tr']:self.out.append('\n')
 def handle_data(self,d):
  if not self.skip:self.out.append(d)
rows=[]
for name,url in [('pp-version','https://arxiv.org/abs/2003.04122'),('sw-version','https://arxiv.org/abs/2505.16822'),('as-version','https://arxiv.org/abs/2506.13010'),('pps-version','https://arxiv.org/abs/2407.08338'),('pps-v1','https://arxiv.org/html/2407.08338v1')]:
 p=S/(name+'.html')
 try:
  with urllib.request.urlopen(url,timeout=40) as r:b=r.read();status=r.status;final=r.url
 except urllib.error.HTTPError as e:b=e.read();status=e.code;final=e.url
 except Exception as e:rows.append({'url':url,'error':repr(e)});continue
 p.write_bytes(b);rows.append({'url':url,'final_url':final,'status':status,'path':str(p),'sha256':hashlib.sha256(b).hexdigest()})
 if name=='pps-v1' and status==200:
  parser=Text();parser.feed(b.decode());t='\n'.join(s.strip() for s in ''.join(parser.out).splitlines() if s.strip())+'\n';(S/'pps-v1.txt').write_text(t)
(S/'retrieval.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps(rows,indent=2))
