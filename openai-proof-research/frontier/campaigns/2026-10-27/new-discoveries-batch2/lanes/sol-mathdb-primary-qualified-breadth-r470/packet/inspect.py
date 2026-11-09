import pathlib,json
C=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2');B=C/'lanes'
for rel in ['root-mathdb-breadth-intake-r469/reserved-ids.json','root-mathdb-breadth-intake-r469/queue.json','root-mathdb-breadth-intake-r469/coverage-delta.json','root-mathdb-breadth-intake-r469/bindings.json','root-mathdb-accepted-exclusions-r304/accepted-exclusions.json','root-mathdb-accepted-exclusions-r304/historical-dispositions.json','pi-mathdb-full-corpus-inventory-r301/manifest.json']:
 d=json.loads((B/rel).read_text());print('\n',rel)
 if isinstance(d,dict):
  print('keys',list(d));
  for k,v in d.items():
   if k=='frozen_inputs': print(k,json.dumps(v))
   elif isinstance(v,list):print(k,'len',len(v),'first',json.dumps(v[:1])[:1800])
   elif isinstance(v,dict):print(k,'keys',list(v)[:20])
   else:print(k,str(v)[:180])
 else:print('len',len(d),'first',json.dumps(d[:1])[:3000])
