from pathlib import Path
import json,re
R=Path(__file__).resolve().parent;L=R.parent
ids={x['record']['mathdb_id'] for x in json.loads((R/'selected-records.json').read_text())}
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 x=json.loads((L/'root-mathdb-accepted-exclusions-r304'/name).read_text());matches=[]
 def visit(a):
  if isinstance(a,dict):
   if any(str(n) in json.dumps(a) for n in ids) and not any(isinstance(v,(dict,list)) for v in a.values()):matches.append(a)
   for v in a.values():visit(v)
  elif isinstance(a,list):
   for v in a:visit(v)
 visit(x);print(name,'matches',matches)
 (R/('dedup-'+name)).write_text(json.dumps({'matching_leaf_entries':matches,'limit':'Exact ID join only; not registry or source-family clearance'},indent=2)+'\n')
p=R/'primary/mccurley.txt';s=p.read_text(errors='replace');s='\n'.join(re.sub(r'\s+',' ',l).strip() for l in s.splitlines());(R/'primary/mccurley-normalized.txt').write_text(s)
for a,b in [(410,451),(952,1072)]:print('\nMCCURLEY',a,b,'\n'+'\n'.join(s.splitlines()[a:b]))
