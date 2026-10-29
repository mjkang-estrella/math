import json,hashlib,re,gzip,sqlite3,sys
from pathlib import Path
from html.parser import HTMLParser
L=Path(__file__).resolve().parent;R=L.parents[5];B=L.parent.parent
class Text(HTMLParser):
 def __init__(self):super().__init__();self.parts=[]
 def handle_data(self,s):
  if s.strip():self.parts.append(s.strip())
if sys.argv[1]=='read':
 p=Text();p.feed((L/'sources/frank.html').read_text());(L/'sources/frank.txt').write_text('\n'.join(p.parts))
 for name in ['omega-head','openai-head','omega-compare']:
  j=json.loads((L/f'sources/{name}.json').read_text());print(name,j.get('sha'),j.get('status'),j.get('ahead_by'),len(j.get('files',[])),len(j.get('commits',[])))
  if name=='omega-compare':
   print('base',j['base_commit']['sha'],'mergebase',j['merge_base_commit']['sha'])
   (L/'registry-paths.txt').write_text('\n'.join(x['filename'] for x in j['files'])+'\n')
 for j in json.loads((L/'check-results.json').read_text()):
  if j['theta']==8 and j['a']==.5:print('diagnostic',j['m'],j['gain'])
 paths=[R/'AGENTS.md',B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B/'NEXT.md',B/'lanes/root-r131-r132-handback/DECISION.md',B/'lanes/root-r133-handback/DECISION.md']
 rec=[]
 for i,q in enumerate(paths):
  b=q.read_bytes();dest=f'sources/context-{i}{q.suffix}';(L/dest).write_bytes(b);rec.append(dict(path=str(q),copy=dest,sha256=hashlib.sha256(b).hexdigest(),mutable=q.name=='NEXT.md'))
  if q.suffix=='.json':
   j=json.loads(b);print(q.name,[(a.get('number'),a.get('title'),a.get('scope')) for a in j.get('accepted',[])])
 (L/'context-receipts.json').write_text(json.dumps(rec,indent=2)+'\n')
