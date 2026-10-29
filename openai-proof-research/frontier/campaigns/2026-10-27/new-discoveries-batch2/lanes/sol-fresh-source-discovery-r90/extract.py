import pathlib,json,xml.etree.ElementTree as E
from html.parser import HTMLParser
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.math=0;self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
  if t=='math':self.out.append(dict(a).get('alttext',''));self.math+=1
  if t in ['p','section','h2','h3','h4']:self.out.append('\n')
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip-=1
  if t=='math':self.math-=1
 def handle_data(self,d):
  if not self.math and not self.skip:self.out.append(d)
b=pathlib.Path(__file__).parent
for p in (b/'sources').glob('*.html'):
 s=Parser();s.feed(p.read_text());t=''.join(s.out);p.with_suffix('.txt').write_text(t);print(p.name,t[:150])
r=E.parse(b/'sources/lyon.xml').getroot()
for e in r.findall('.//{http://www.w3.org/1998/Math/MathML}math'):
 # preserve MathML's TeX alternatives if any
 pass
out=[]
for el in r.iter():
 if el.tag in ['p','title','disp-formula']:
  out.append(' '.join(''.join(el.itertext()).split()))
(b/'sources/lyon.txt').write_text('\n'.join(out))
for n in ['omega-head.json','openai-head.json']:
 d=json.loads((b/'sources'/n).read_text());print(n,d.get('sha'),d.get('commit',{}).get('committer',{}))
