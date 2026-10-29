from pathlib import Path
from html.parser import HTMLParser
class P(HTMLParser):
 def __init__(self):super().__init__();self.a=[]
 def handle_data(self,s):self.a.append(s)
p=Path(__file__).resolve().parent
for f in (p/'sources').glob('*.html'):
 q=P();q.feed(f.read_text());s=' '.join(q.a);f.with_suffix('.txt').write_text(s)
 print('\nSOURCE',f.name)
 import re
 for m in re.finditer(r'Conjecture|Question|Problem|Theorem 1',s):print(s[max(0,m.start()-60):m.start()+1400])
