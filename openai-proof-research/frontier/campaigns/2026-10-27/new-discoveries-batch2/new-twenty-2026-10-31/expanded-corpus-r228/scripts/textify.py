import pathlib,html.parser
D=pathlib.Path(__file__).resolve().parents[1]
class P(html.parser.HTMLParser):
 def __init__(self):super().__init__();self.x=[]
 def handle_data(self,d):self.x.append(d)
 def handle_endtag(self,t):
  if t in ('p','div','section','h1','h2','h3','li','figure'):self.x.append('\n')
for p in (D/'sources').glob('*.html'):
 s=P();s.feed(p.read_text());p.with_suffix('.txt').write_text(''.join(s.x))
