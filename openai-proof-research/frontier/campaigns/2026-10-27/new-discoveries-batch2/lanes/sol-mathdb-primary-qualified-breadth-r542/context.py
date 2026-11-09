from pathlib import Path
import json
O=Path(__file__).resolve().parent;L=O.parent
for n in ['accepted-exclusions','historical-dispositions']:
 x=json.loads((L/'root-mathdb-accepted-exclusions-r304'/(n+'.json')).read_text());print(n, type(x).__name__)
 print(str(x)[:1500])
 ids={str(a['record']['mathdb_id']) for a in json.loads((O/'assigned-records.json').read_text())}
 def walk(x):
  if isinstance(x,dict):
   if any(str(k) in ids or (('id' in k) and str(v) in ids) for k,v in x.items()):print('MATCH',x)
   for v in x.values():walk(v)
  elif isinstance(x,list):
   for v in x:walk(v)
 walk(x)
 if n=='accepted-exclusions':
  def scopes(x):
   if isinstance(x,dict):
    if 'scope' in x:print('SCOPE',x.get('title',''),x['scope'])
    for v in x.values():scopes(v)
   elif isinstance(x,list):
    for v in x:scopes(v)
  scopes(x)
