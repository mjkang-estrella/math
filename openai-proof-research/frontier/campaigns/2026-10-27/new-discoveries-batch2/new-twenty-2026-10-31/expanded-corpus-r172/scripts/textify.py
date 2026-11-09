import pathlib,html.parser
D=pathlib.Path(__file__).resolve().parents[1]
class Parser(html.parser.HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  if t=='math':self.out.append(dict(a).get('alttext',''));self.skip+=1
  if t in ('p','section','div','h1','h2','h3','li'):self.out.append('\n')
 def handle_endtag(self,t):
  if t=='math':self.skip-=1
 def handle_data(self,s):
  if not self.skip:self.out.append(s)
for p in (D/'sources').glob('arxiv*.html'):
 s=Parser();s.feed(p.read_text());p.with_suffix('.txt').write_text(''.join(s.out));print(p.name)
