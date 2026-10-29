from html.parser import HTMLParser
from pathlib import Path
import sys
class P(HTMLParser):
 def __init__(s):super().__init__();s.math=0;s.out=[]
 def handle_starttag(s,t,a):
  d=dict(a)
  if t=='math':s.math+=1;s.out.append('$'+d.get('alttext','')+'$')
  if t in ['p','h2','h3','h6','section','div']:s.out.append('\n')
 def handle_endtag(s,t):
  if t=='math':s.math-=1
 def handle_data(s,d):
  if not s.math:s.out.append(d)
for f in sys.argv[1:]:
 p=P();p.feed(Path(f).read_text());Path(f).with_suffix('.txt').write_text(''.join(p.out))
