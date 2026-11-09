exec(open(__file__.replace('context.py','bind.py')).read().split('refs={}')[0])
p=L/'root-mathdb-cayley-review-intake-r363/DECISION.md';refs=j(P/'flat-bindings.json');refs.append(entry(p));write('flat-bindings.json',refs)
ids=set(j(I/'reserved-ids-r716.json')['ids'])
for n in ['ledger.json','prior-campaign-context.json']:
 d=j(B/n);print(n, str(d)[:900])
for n in ['accepted-exclusions.json','historical-dispositions.json']:
 d=j(L/'root-mathdb-accepted-exclusions-r304'/n)
 print(n,'schema',type(d).__name__)
 # Only assigned-ID or exact relevant family matches; no adjacent records.
 def walk(x):
  if isinstance(x,dict):
   if any(str(i) in json.dumps(x,ensure_ascii=False) for i in ids) and len(json.dumps(x))<12000:print(json.dumps(x,ensure_ascii=False));return
   for v in x.values():walk(v)
  elif isinstance(x,list):
   for v in x:walk(v)
 walk(d)
print('CAYLEY',p.read_text());print('ADJUDICATIONS',json.dumps(j(I/'adjudications.json')));print('HYPOTHESES',json.dumps(j(I/'hypothesis-queue.json')))
