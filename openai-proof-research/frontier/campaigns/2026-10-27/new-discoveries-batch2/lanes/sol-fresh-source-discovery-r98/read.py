from pathlib import Path
from html.parser import HTMLParser
P=Path(__file__).resolve().parent
class Text(HTMLParser):
 def __init__(self):super().__init__();self.a=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
  if t in ['p','div','section','h1','h2','h3','h4','h5','h6']:self.a.append('\n')
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip-=1
 def handle_data(self,d):
  if not self.skip:self.a.append(d)
for name in ['git','ikl','ikl_successor','git_abs','ikl_abs','ikl_successor_abs']:
 f=P/'sources'/name
 if not f.exists():continue
 h=Text();h.feed(f.read_text());(P/'sources'/(name+'.txt')).write_text(''.join(h.a))
