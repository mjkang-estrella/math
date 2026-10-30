from pathlib import Path
from html.parser import HTMLParser
import hashlib,json,re
L=Path(__file__).resolve().parent
class P(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.depth=0
 def handle_starttag(self,t,a):
  if t=='math':self.out.append(dict(a).get('alttext',''));self.depth+=1
  elif self.depth:self.depth+=1
  elif t in ['p','div','section','h1','h2','h3','li']:self.out.append('\n')
 def handle_endtag(self,t):
  if self.depth:self.depth-=1
 def handle_data(self,d):
  if not self.depth:self.out.append(d)
rows=json.loads((L/'primary-freeze.json').read_text())
for p in (L/'sources').glob('*.html'):
 if any(x['original']==str(p.resolve()) for x in rows):continue
 c=L/'frozen-primary'/p.name;c.write_bytes(p.read_bytes());h=hashlib.sha256(p.read_bytes()).hexdigest();assert hashlib.sha256(c.read_bytes()).hexdigest()==h;rows.append(dict(original=str(p.resolve()),copy=str(c.relative_to(L)),sha256=h))
(L/'primary-freeze.json').write_text(json.dumps(rows,indent=2))
for x in rows:
 p=L/x['copy'];a=P();a.feed(p.read_text());s=''.join(a.out);(L/'sources'/(p.stem+'.txt')).write_text(s)
 if p.stem in ['energy','schubert','bases']:
  print('SOURCE',p.stem)
  for m in re.finditer('(?i)conjecture|open problem|question|remains open',s):print(s[max(0,m.start()-180):m.end()+1800])
