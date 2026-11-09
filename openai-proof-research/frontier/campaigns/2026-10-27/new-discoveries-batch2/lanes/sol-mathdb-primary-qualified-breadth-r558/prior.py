from pathlib import Path
import json
D=Path(__file__).resolve().parent;L=D.parent
x=json.loads((L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json').read_text())
for f in x['families']:print(f['number'],f.get('title'),f.get('scope'))
x=json.loads((L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json').read_text());print('historical sections',x.keys())
ids={str(r['record']['mathdb_id']) for r in json.loads((D/'assigned-records.json').read_text())}
def walk(x):
 if isinstance(x,dict):
  if str(x.get('mathdb_id',x.get('id'))) in ids: print('relevant history',x)
  for k,v in x.items():
   if k in ids:print('relevant history',k,v)
   walk(v)
 elif isinstance(x,list):
  for v in x:walk(v)
walk(x)
print((L/'root-mathdb-breadth-intake-r557/adjudications.json').read_text());print((L/'root-mathdb-breadth-intake-r557/hypothesis-queue.json').read_text())
