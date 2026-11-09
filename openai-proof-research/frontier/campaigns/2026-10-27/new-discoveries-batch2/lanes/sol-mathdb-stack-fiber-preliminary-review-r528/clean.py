from pathlib import Path
from html.parser import HTMLParser
import hashlib,json
D=Path(__file__).resolve().parent
class H(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['math','script','style']:
   if t=='math' and not self.skip:self.out.append(dict(a).get('alttext',''))
   self.skip+=1
  if t in ['p','div','h1','h2','h3','h4','li']:self.out.append('\n')
 def handle_endtag(self,t):
  if t in ['math','script','style']:self.skip-=1
 def handle_data(self,s):
  if not self.skip:self.out.append(s)
rows=[]
for name in ['defant-zheng','yi']:
 h=H();h.feed((D/(name+'.html')).read_text());p=D/(name+'-clean.txt');p.write_text(''.join(h.out));b=p.read_bytes();rows.append(dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest()))
P=D.parent/'sol-mathdb-primary-qualified-breadth-r522'
r=json.loads((P/'records.json').read_text())
(D/'record-structure.txt').write_text(str(type(r))+'\n'+str(r)[:1000])
(D/'clean-bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
