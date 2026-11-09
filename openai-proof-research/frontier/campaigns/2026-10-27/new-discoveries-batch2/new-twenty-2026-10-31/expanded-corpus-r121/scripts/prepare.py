from pathlib import Path
import json,hashlib,sys
from html.parser import HTMLParser
class Text(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  if t=="annotation":self.skip+=1
 def handle_endtag(self,t):
  if t=="annotation":self.skip-=1
 def handle_data(self,s):
  if not self.skip:self.out.append(s)
D=Path(__file__).resolve().parents[1]
for p in (D/'sources').glob('*.html'):
 s=Text();s.feed(p.read_text());(D/'sources'/p.with_suffix('.txt').name).write_text(' '.join(' '.join(s.out).split()))
for p in (D/'outputs').glob('inherited*'):
 o=json.loads(p.read_text());print(p.name)
 for k in ['accepted','excluded','held_candidates']:
  v=o.get(k,[])
  if isinstance(v,dict):print(k,json.dumps(v)[:10000]);continue
  for x in v:
   if isinstance(x,dict):print(k,{a:x[a] for a in ['mathdb_id','problem_ids','title','reason','status'] if a in x})
