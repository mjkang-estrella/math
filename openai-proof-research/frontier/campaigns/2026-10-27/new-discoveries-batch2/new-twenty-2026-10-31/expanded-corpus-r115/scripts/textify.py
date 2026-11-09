from html.parser import HTMLParser
import pathlib,sys
class P(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.math=0
 def handle_starttag(self,t,a):
  if t=='math':
   self.math+=1;self.out.append(' '+dict(a).get('alttext','')+' ')
  if t in ['p','h1','h2','h3','h4','div','li']:self.out.append('\n')
 def handle_endtag(self,t):
  if t=='math':self.math-=1
 def handle_data(self,d):
  if not self.math:self.out.append(d)
D=pathlib.Path(__file__).resolve().parents[1]
for f in (D/'sources').glob('*.html'):
 p=P();p.feed(f.read_text());f.with_suffix('.txt').write_text(''.join(p.out))
