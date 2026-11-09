import json,pathlib,re
L=pathlib.Path(__file__).resolve().parent;B=L.parent; ids=set(json.loads((L/'input-bindings.json').read_text())['reserved_ids']);matches=[]
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 p=B/'root-mathdb-accepted-exclusions-r304'/name;obj=json.loads(p.read_text())
 for key,val in obj.items():
  if isinstance(val,list):
   for row in val:
    hits=ids & set(map(int,re.findall(r'(?<!\d)\d{6}(?!\d)',json.dumps(row))))
    if hits:matches.append(dict(file=str(p),section=key,matched_ids=sorted(hits),entry=row))
(L/'historical-matches.json').write_text(json.dumps(matches,indent=2)+'\n');print(json.dumps(matches,indent=2))
