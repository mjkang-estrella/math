import pathlib,html.parser,re
class Parser(html.parser.HTMLParser):
 def __init__(self): super().__init__();self.a=[];self.skip=0
 def handle_starttag(self,t,a):
  if t=='math':
   self.a.append(' $'+dict(a).get('alttext','')+'$ ');self.skip+=1
  if t in ['p','div','section','h1','h2','h3','li']:self.a.append('\n')
 def handle_endtag(self,t):
  if t=='math':self.skip-=1
 def handle_data(self,d):
  if not self.skip:self.a.append(d)
L=pathlib.Path(__file__).resolve().parents[1]
for p in (L/'receipts').glob('*-html.body'):
 s=Parser();s.feed(p.read_text());(L/'outputs'/(p.stem+'.txt')).write_text(re.sub(r'\n\s*\n','\n',''.join(s.a)))
