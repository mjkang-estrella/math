from pathlib import Path
import json
O=Path(__file__).parent;L=O.parent;ids={x['record']['mathdb_id'] for x in json.loads((O/'literal-records.json').read_text())}
paths=[L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L.parent/'ledger.json',L.parent/'prior-campaign-context.json']
out=[]
def visit(x,p):
 if isinstance(x,dict):
  direct=[]
  for k,v in x.items():
   if 'id' in k:
    vals=v if isinstance(v,list) else [v]
    direct.extend(z for z in vals if isinstance(z,int) and z in ids)
  if direct:out.append({'path':str(p),'matching_ids':direct,'entry':x})
  for v in x.values():visit(v,p)
 elif isinstance(x,list):
  for v in x:visit(v,p)
for p in paths:visit(json.loads(p.read_text()),p)
(O/'context-screen.json').write_text(json.dumps({'method':'exact assigned-ID structured matches only; not global semantic family clearance','matches':out,'r363':'Cayley364119 published33712 vs33710 excludes credit; decision read','adjudications':'r707 retire338290/339564/372627; park337963;338366 excluded with text/figure reconstruction and unread-journal limits','registry':'unavailable HOLD'},indent=2)+'\n');print((O/'context-screen.json').read_text())
