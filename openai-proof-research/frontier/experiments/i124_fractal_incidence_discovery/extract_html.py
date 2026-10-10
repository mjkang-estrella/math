"""Preparation helper, standard-library representation; never used to alter sealed files."""
from html.parser import HTMLParser
import re
class Extract(HTMLParser):
 def __init__(self):super().__init__();self.parts=[];self.skip=0;self.math=0
 def handle_starttag(self,t,a):
  if t in ('script','style'):self.skip+=1
  if t=='math':
   if not self.math:self.parts.append(dict(a).get('alttext',''))
   self.math+=1
  if t in ('p','div','section','h1','h2','h3','h4','li','tr','br'):self.parts.append('\n')
 def handle_endtag(self,t):
  if t in ('script','style'):self.skip=max(0,self.skip-1)
  if t=='math':self.math=max(0,self.math-1)
  if t in ('p','div','section','h1','h2','h3','h4','li','tr'):self.parts.append('\n')
 def handle_data(self,s):
  if not self.skip and not self.math:self.parts.append(s)
def extract(s):
 p=Extract();p.feed(s);return '\n'.join(t for l in ''.join(p.parts).splitlines() if (t:=re.sub(r'\s+',' ',l).strip()))+'\n'
if __name__=='__main__':
 import sys
 from pathlib import Path
 p=Path(sys.argv[1]);p.with_suffix('.txt').write_text(extract(p.read_text()))
