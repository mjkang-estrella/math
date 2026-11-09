from pathlib import Path
import json
P=Path(__file__).parent;L=P.parent;ids=set(json.loads((L/'root-mathdb-breadth-intake-r709/reserved-ids-r710.json').read_text())['ids'])
def visit(x,path=''):
 if isinstance(x,dict):
  if any(str(v) in {str(i) for i in ids} for k,v in x.items() if k in ['mathdb_id','id','mathdb_related_id']):print(path,json.dumps(x,ensure_ascii=False)[:4000])
  for k,v in x.items():
   if str(k) in {str(i) for i in ids}:print(path+'/'+str(k),json.dumps(v,ensure_ascii=False)[:4000])
   else:visit(v,path+'/'+str(k))
 elif isinstance(x,list):
  for i,v in enumerate(x):visit(v,path+'/'+str(i))
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 p=L/'root-mathdb-accepted-exclusions-r304'/name
 print(name);visit(json.loads(p.read_text()))
 print('top keys',list(json.loads(p.read_text()))[:12])
print((L/'root-mathdb-breadth-intake-r709/frozen/sol-mathdb-primary-qualified-breadth-r704/failures.json').read_text())
