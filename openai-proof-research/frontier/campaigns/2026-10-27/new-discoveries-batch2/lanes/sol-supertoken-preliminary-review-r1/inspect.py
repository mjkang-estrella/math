from review_tools import *
from html.parser import HTMLParser
class Text(HTMLParser):
 def __init__(self):super().__init__();self.parts=[]
 def handle_data(self,d):
  if d.strip():self.parts.append(d.strip())
for name in ['metric-successor','metric-arxiv','metric-primary']:
 p=Text();p.feed((R/'copy/sources'/ (name+'.html')).read_text()); lines=p.parts
 hits=[]
 for i,l in enumerate(lines):
  if any(s in l.lower() for s in ['conjecture 4.2','metric dimension','submitted','published online','april','december']):
   hits.append('\n'.join(lines[max(0,i-2):i+16]))
 out='\n\n'.join(hits)
 (R/(name+'-excerpts.txt')).write_text(out[:26000])
 print(name,out[:10500])
for name in ['ledger.json','prior-campaign-context.json']:
 d=json.loads((B/name).read_text())
 def walk(x):
  if isinstance(x,dict):
   if any('routine classical separation' in str(v) or 'substantive_adjudication'==k for k,v in x.items()):
    print(name,{k:v for k,v in x.items() if k in ['title','path','status','substantive_adjudication','proposed_result']})
   for v in x.values():walk(v)
  elif isinstance(x,list):
   for v in x:walk(v)
 walk(d)
d=json.loads((B/'lanes/sol-renyi-threshold-current-prior-review-r2/registry-audit.json').read_text())
print('registry keys',list(d))
for k,v in d.items():
 print(k,str(v)[:1300])
