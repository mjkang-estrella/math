from pathlib import Path
import json,re
from html.parser import HTMLParser
D=Path(__file__).resolve().parents[1]
class T(HTMLParser):
 def __init__(self):super().__init__();self.x=[]
 def handle_data(self,s):self.x.append(s)
for label in ['arumugam']:
 p=D/'downloads'/label/'body'
 if p.exists():
  h=T();h.feed(p.read_text(errors='replace'));(p.parent/'text.txt').write_text('\n'.join(h.x))
for p in sorted((D/'downloads').glob('pool-*/body')):
 text=p.read_text(errors='replace');hits=[(i,l[:600]) for i,l in enumerate(text.splitlines(),1) if re.search(r'339235|1805\.04888|mobius|möbius|antimagic|Lau.*Shiu',l,re.I)]
 print(p.parent.name,'HITS',hits)
for p in sorted((D/'downloads').glob('github-query-*/body')):
 x=json.loads(p.read_text());print(p.parent.name,'count',x.get('total_count'),[(r['full_name'],r.get('description')) for r in x.get('items',[])])
