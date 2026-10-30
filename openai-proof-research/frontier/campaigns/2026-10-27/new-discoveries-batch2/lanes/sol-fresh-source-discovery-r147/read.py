import sys,re
from pathlib import Path
from html.parser import HTMLParser
L=Path(__file__).resolve().parent
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.math=0;self.skip=0
 def handle_starttag(self,t,a):
  d=dict(a)
  if t in ('script','style'):self.skip+=1
  if t=='math':self.math+=1;self.out.append(' '+d.get('alttext','')+' ')
  if t in ('p','div','section','h1','h2','h3','h4','li','tr'):self.out.append('\n')
 def handle_endtag(self,t):
  if t in ('script','style'):self.skip-=1
  if t=='math':self.math-=1
 def handle_data(self,s):
  if not self.math and not self.skip:self.out.append(s)
for n in sys.argv[1:]:
 p=L/'sources'/n;q=Parser();q.feed(p.read_text());s=re.sub(r'\n\s*\n+','\n', ''.join(q.out));p.with_suffix('.txt').write_text(s)
 print(n,len(s))
