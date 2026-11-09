from html.parser import HTMLParser
import pathlib,re,json
D=pathlib.Path(__file__).resolve().parents[1]
class P(HTMLParser):
 def __init__(self):super().__init__();self.parts=[];self.math=0;self.skip=0
 def handle_starttag(self,t,a):
  a=dict(a)
  if t=='math':self.math+=1;self.parts.append(' '+a.get('alttext','')+' ')
  if not self.math and t in ('p','div','section','h1','h2','h3','h4','li','tr'):self.parts.append('\n')
 def handle_endtag(self,t):
  if t=='math':self.math-=1
 def handle_data(self,d):
  if not self.math:self.parts.append(d)
for p in (D/'sources').glob('*.html'):
 s=P();s.feed(p.read_text());t='\n'.join(re.sub(r'\s+',' ',l).strip() for l in ''.join(s.parts).splitlines());p.with_suffix('.txt').write_text(t)
 for n,l in enumerate(t.splitlines(),1):
  if any(w in l.lower() for w in ['conjecture','verified','computational','checked up','experiment']):print(p.stem,n,l[:5000])
