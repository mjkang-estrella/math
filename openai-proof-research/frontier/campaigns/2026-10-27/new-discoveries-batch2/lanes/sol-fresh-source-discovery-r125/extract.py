from pathlib import Path
import sys
from html.parser import HTMLParser
p=Path(__file__).resolve().parent
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,tag,attrs):
  if tag in ['script','style']:self.skip+=1
 def handle_endtag(self,tag):
  if tag in ['script','style']:self.skip-=1
 def handle_data(self,s):
  if not self.skip:self.out.append(s)
name=sys.argv[1] if len(sys.argv)>1 else 'source-imv'
s=Parser();s.feed((p/(name+'.html')).read_text());t=' '.join(s.out)
(p/(name+'.txt')).write_text(t)
for start,end in [('2 Subdivision','3 Complexity'),('6 Concluding','References'),('Proposition 26','Theorem 27')]:
 a=t.find(start);b=t.find(end,a+1);print(t[a:b][:20000])
if name=='complexity':
 a=t.find('NP-completeness',t.find('NP-completeness')+1);print(t[a:a+27000])
