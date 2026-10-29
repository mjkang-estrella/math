from pathlib import Path
from html.parser import HTMLParser
class TextParser(HTMLParser):
 def __init__(self): super().__init__();self.parts=[]
 def handle_data(self,data): self.parts.append(data)
import json, urllib.request, hashlib, datetime
here=Path(__file__).resolve().parent
B=here.parent.parent
out={}
for name in ['ledger.json','prior-campaign-context.json']:
 obj=json.loads((B/name).read_text());out[name]={'sha256':hashlib.sha256((B/name).read_bytes()).hexdigest(),'keys':list(obj),'content':obj}
(here/'context-reading.json').write_text(json.dumps(out,indent=2))
for p in (here/'sources').glob('*.html'):
 s=TextParser();s.feed(p.read_text());p.with_suffix('.txt').write_text(' '.join(s.parts))
for name,v in out.items():
 print(name)
 for k,x in v['content'].items():
  if isinstance(x,list):
   print(k, len(x))
   for r in x:
    if isinstance(r,dict): print({a:r[a] for a in ['id','title','name','reason','status'] if a in r})
  elif not isinstance(x,dict):print(k,x)
print('UTC',datetime.datetime.now(datetime.timezone.utc).isoformat())
