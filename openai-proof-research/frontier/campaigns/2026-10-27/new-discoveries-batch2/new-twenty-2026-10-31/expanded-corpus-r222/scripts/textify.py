import pathlib,html.parser,re,json
class P(html.parser.HTMLParser):
 def __init__(self):super().__init__();self.a=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style']: self.skip+=1
 def handle_endtag(self,t):
  if t in ['script','style']: self.skip-=1
 def handle_data(self,d):
  if not self.skip:self.a.append(d)
D=pathlib.Path(__file__).resolve().parents[1]
for f in (D/'sources').glob('*.html'):
 p=P();p.feed(f.read_text());s=re.sub(r'\s+',' ',' '.join(p.a));(D/'sources'/(f.stem+'.txt')).write_text(s)
 contexts=[]
 for m in re.finditer('conjectur|Figure|verified|checked|enumerat',s,re.I): contexts.append(s[max(0,m.start()-200):m.end()+950])
 (D/'sources'/(f.stem+'.contexts.txt')).write_text('\n\n'.join(contexts))
