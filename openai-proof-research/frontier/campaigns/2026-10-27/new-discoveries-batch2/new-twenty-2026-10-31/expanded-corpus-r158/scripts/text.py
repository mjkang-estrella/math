from html.parser import HTMLParser
import pathlib,re
L=pathlib.Path(__file__).resolve().parents[1]
class P(HTMLParser):
 def __init__(self):super().__init__();self.a=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['p','div','section','h1','h2','h3','h4','li']:self.a.append('\n')
  if t in ['script','style','annotation']:self.skip+=1
 def handle_endtag(self,t):
  if t in ['script','style','annotation']:self.skip-=1
 def handle_data(self,d):
  if not self.skip:self.a.append(d)
for f in (L/'sources').glob('*.html'):
 p=P();p.feed(f.read_text());t=re.sub(r'[ \t]+',' ',''.join(p.a));t=re.sub(r'\n\s*\n','\n',t)
 f.with_suffix('.txt').write_text(t)
for f in sorted((L/'sources').glob('*.txt')):
 t=f.read_text();print('\nSOURCE',f.name)
 lines=t.splitlines()
 inds=[i for i,l in enumerate(lines) if re.search('conjectur|question|verified|computational|exhaustive',l,re.I)]
 for i in inds:
  print('\n'.join(lines[max(0,i-1):min(len(lines),i+3)])[:2200])
