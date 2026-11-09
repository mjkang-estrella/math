import pathlib,json
O=pathlib.Path(__file__).parent;L=O.parent;B=L.parent
ids=set(json.loads((L/'root-mathdb-breadth-intake-r447/reserved-ids.json').read_text())['ids'])
for n in ['accepted-exclusions.json','historical-dispositions.json']:
 j=json.loads((L/'root-mathdb-accepted-exclusions-r304'/n).read_text());print(n,'top keys',list(j) if isinstance(j,dict) else 'list')
 def walk(x,path=''):
  if isinstance(x,dict):
   for k,v in x.items():
    if str(k) in set(map(str,ids)):print(path,k,json.dumps(v,ensure_ascii=False))
    elif k in ['mathdb_id','id'] and v in ids:print(path,json.dumps(x,ensure_ascii=False))
    else:walk(v,path+'/'+k)
  elif isinstance(x,list):
   for i,v in enumerate(x):walk(v,path+'/'+str(i))
 walk(j)
for n in ['ledger.json','prior-campaign-context.json']:
 j=json.loads((B/n).read_text());print(n,'keys',list(j));print({k:v for k,v in j.items() if any(s in k for s in ['count','next','accepted','additional','total']) and not isinstance(v,(dict,list))})
