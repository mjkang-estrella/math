import pathlib,html.parser
D=pathlib.Path(__file__).resolve().parents[1]
class Parser(html.parser.HTMLParser):
 def __init__(self):super().__init__();self.parts=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
  if t in ['p','div','section','h1','h2','h3','h4','li']:self.parts.append('\n')
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip-=1
 def handle_data(self,s):
  if not self.skip:self.parts.append(s)
for p in (D/'sources').glob('*.html'):
 s=Parser();s.feed(p.read_text());(D/'sources'/(p.stem+'.txt')).write_text(''.join(s.parts))
