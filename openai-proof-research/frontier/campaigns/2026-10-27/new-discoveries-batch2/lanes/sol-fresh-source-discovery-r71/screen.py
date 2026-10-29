import pathlib,json,hashlib,re
from html.parser import HTMLParser
r=pathlib.Path(__file__).parent; project=next(p for p in r.parents if p.name=='openai-proof-research')
class Text(HTMLParser):
 def __init__(self):super().__init__();self.a=[]
 def handle_data(self,d): self.a.append(d)
for f in (r/'sources').glob('*.html'):
 p=Text();p.feed(f.read_text());f.with_suffix('.txt').write_text(' '.join(p.a))
patterns=re.compile('Murai|Takahashi|Cuong|Kien|Matsuoka|Truong|Chomicz|2609[.-]18136|2609[.-]39218|2609[.-]04000|pseudo.?frobenius|determinantal.*semigroup|semigroup.*determinantal',re.I)
res=[]
for lane,base in [('sol-fresh-source-discovery-r57','sources'),('sol-polyomino57-full-final-review-r1','live')]:
 for f in (r.parent/lane/base).glob('*.json'):
  if not any(t in f.name for t in ('tree','D5','Problems')):continue
  try:d=json.loads(f.read_text())
  except Exception:continue
  hits=[x for x in d.get('tree',[]) if patterns.search(x['path'])]
  res.append({'file':str(f.relative_to(project)), 'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'tree_sha':d.get('sha'),'truncated':d.get('truncated'),'hits':hits})
(r/'registry-screen.json').write_text(json.dumps(res,indent=2))
for x in res:
 print(x['file'],len(x['hits']))
 for v in x['hits']:print(v['path'])
# Read full control JSONs and capture hashes/counts, rather than truncate their bodies.
ctx=[]
for f in [r.parent.parent/'ledger.json',r.parent.parent/'prior-campaign-context.json']:
 d=json.loads(f.read_text());ctx.append({'file':str(f.relative_to(project)),'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'keys':list(d),'accepted_count':d.get('accepted_count')})
(r/'context-screen.json').write_text(json.dumps(ctx,indent=2))
