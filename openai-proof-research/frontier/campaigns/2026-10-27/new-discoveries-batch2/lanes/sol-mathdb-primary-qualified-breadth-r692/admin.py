exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split('out=[entry')[0])
ids=set(j(I/'reserved-ids-r692.json')['ids'])
for fn in ['accepted-exclusions.json','historical-dispositions.json']:
 x=j(L/'root-mathdb-accepted-exclusions-r304'/fn)
 def walk(v):
  if isinstance(v,dict):
   if (set(v.get('mathdb_ids',[]))|set(v.get('problem_ids',[]))|{v.get('mathdb_id')})&ids: print(fn,json.dumps(v,ensure_ascii=False)[:2500])
   for a in v.values():walk(a)
  elif isinstance(v,list):
   for a in v:walk(a)
 walk(x)
print('Read r304 full structured exclusions/dispositions; printed assigned matches only.')
for n in ['verification-receipt.json','focused-assignment.json']:print(n,j(I/n))
