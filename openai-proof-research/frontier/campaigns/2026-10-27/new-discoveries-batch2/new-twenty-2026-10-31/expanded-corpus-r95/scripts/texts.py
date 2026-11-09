from html.parser import HTMLParser
from pathlib import Path
import re
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.parts=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['math','script','style']:
   if t=='math':self.parts.append(dict(a).get('alttext',''))
   self.skip+=1
  if t in ['p','div','section','h1','h2','h3']:self.parts.append('\n')
 def handle_endtag(self,t):
  if t in ['math','script','style']:self.skip-=1
 def handle_data(self,d):
  if not self.skip:self.parts.append(d)
L=Path(__file__).resolve().parents[1]
for p in (L/'sources').glob('*.html'):
 if p.name.startswith('registry'):continue
 parser=Parser();parser.feed(p.read_text());s=' '.join(parser.parts);s=re.sub('[ \t]+',' ',s);p.with_suffix('.txt').write_text(s)
 matches=list(re.finditer('conjectur',s,re.I));(L/f'outputs/{p.stem}-conjectures.txt').write_text('\n\n'.join(s[max(0,m.start()-300):m.start()+1700] for m in matches))
