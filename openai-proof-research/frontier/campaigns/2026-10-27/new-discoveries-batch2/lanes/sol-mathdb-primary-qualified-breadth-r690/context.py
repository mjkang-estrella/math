exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split('refs={}')[0])
bs=j(P/'flat-bindings.json');paths=[p for p in (L/'root-mathdb-cayley-review-intake-r363').iterdir() if p.is_file()]
for p in paths:bs.append(info(p))
(P/'flat-bindings.json').write_text(json.dumps(bs,indent=2)+'\n')
for name in ['adjudications.json','hypothesis-queue.json']:print(name,(I/name).read_text())
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 d=j(L/'root-mathdb-accepted-exclusions-r304'/name);print(name,'schema',type(d).__name__)
 ids=set(j(I/'reserved-ids-r690.json')['ids'])
 def walk(x):
  if isinstance(x,dict):
   if any(str(i) in json.dumps(x) for i in ids) and len(json.dumps(x))<4500:print(json.dumps(x,ensure_ascii=False))
   else:
    for y in x.values():walk(y)
  elif isinstance(x,list):
   for y in x:walk(y)
 walk(d)
for p in paths:
 if p.name.lower() in ['decision.md','summary.md']:print(p.name,p.read_text()[:10000])
for name in ['ledger.json','prior-campaign-context.json']:
 d=j(L.parent/name);print(name,'top-level keys',list(d) if isinstance(d,dict) else 'list', 'bound and loaded; no full dump')
