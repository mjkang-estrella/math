from pathlib import Path
import json,hashlib,re
P=Path(__file__).resolve().parent;R=next(x for x in P.parents if x.name=='openai-proof-research');B=P.parent.parent
files=[R/'AGENTS.md',B/'AGENTS.md',B/'NEXT.md',B/'ledger.json',B/'prior-campaign-context.json',R/'sources/upstream.json',R/'sources/CONTENTS.md']
res=[]
for f in files:
 b=f.read_bytes();s=b.decode();d=dict(file=str(f),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 if f.suffix=='.json':
  x=json.loads(s)
  def titles(x):
   if isinstance(x,dict):
    for k,v in x.items():
     if k in ['title','status','reason','one_family','note','held_candidates','excluded']:yield str(v)[:800]
     elif isinstance(v,(dict,list)):yield from titles(v)
   elif isinstance(x,list):
    for y in x:yield from titles(y)
  d['entries']=list(titles(x));print(f.name,len(d['entries']));print('\n'.join(d['entries'])[:9500])
 res.append(d)
(P/'context-read.json').write_text(json.dumps(res,indent=2))
