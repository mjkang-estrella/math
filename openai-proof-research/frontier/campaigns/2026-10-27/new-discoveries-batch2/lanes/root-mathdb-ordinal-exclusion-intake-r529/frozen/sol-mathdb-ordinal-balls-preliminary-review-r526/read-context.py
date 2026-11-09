import pathlib,json
D=pathlib.Path(__file__).resolve().parent;L=D.parent;P=L/'sol-mathdb-primary-qualified-breadth-r522'
for fn in ('records.json','dispositions.json','proposals.json'):
 data=json.loads((P/fn).read_text());print('\nTARGET',fn)
 def visit(x):
  if isinstance(x,dict):
   if any(str(v)=='366370' for k,v in x.items() if not isinstance(v,(dict,list))):print(json.dumps(x,indent=2));return
   for v in x.values():visit(v)
  elif isinstance(x,list):
   for v in x:visit(v)
 visit(data)
for lane,files in [('root-mathdb-accepted-exclusions-r304',['README.md','accepted-exclusions.json','historical-dispositions.json']),('root-mathdb-cayley-review-intake-r363',['DECISION.md','disposition.json']),('root-mathdb-candidate-intake-r525',['adjudications.json','DECISION.md'])]:
 for f in files:
  s=(L/lane/f).read_text();print('\nHISTORY',lane,f)
  if len(s)<14000:print(s)
  else:
   data=json.loads(s)
   # Exact scope screening, avoid unrelated scientific briefs.
   def screen(x):
    if isinstance(x,dict):
     if any(t in json.dumps(x).lower() for t in ('366370','ordinal','echelon','balls','cayley')) and len(json.dumps(x))<12000:print(json.dumps(x));return
     for v in x.values():screen(v)
    elif isinstance(x,list):
     for v in x:screen(v)
   screen(data)
print('LEDGER',[(x.name,len(x.read_bytes())) for x in (L.parent/'ledger.json',L.parent/'prior-campaign-context.json')])
