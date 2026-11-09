import pathlib,json,re,hashlib
L=pathlib.Path(__file__).parent; B=L.parent
paths=[s.split('  ',1)[1] for s in (L/'inputs-before.sha256').read_text().splitlines()]
rows=[]
def walk(x,p):
 if isinstance(x,dict):
  if 'url' in x or 'requested_url' in x:
   rows.append({'source':p,'receipt':x})
  for v in x.values(): walk(v,p)
 elif isinstance(x,list):
  for v in x: walk(v,p)
for p in paths:
 q=B/p
 if q.suffix in ('.json','.jsonl') and ('receipt' in p or 'access' in p or 'review.json' in p):
  try:
   t=q.read_text()
   if q.suffix=='.json': walk(json.loads(t),p)
   else:
    for line in t.splitlines():
     try: walk(json.loads(line),p)
     except ValueError: pass
  except (ValueError,UnicodeError): pass
(L/'prior-routes.json').write_text(json.dumps(rows,indent=2))
with (L/'prior-routes.tsv').open('w') as f:
 for r in rows:
  x=r['receipt']; f.write('\t'.join([r['source'],str(x.get('url',x.get('requested_url',''))),str(x.get('status',x.get('result',x.get('error','see receipt'))))])+'\n')
ledger=json.loads((B/'ledger.json').read_text())
def pick(x):
 if isinstance(x,dict):
  if str(x.get('mathdb_id')) in ['330264','352038','324342']: return [x]
  return sum([pick(v) for v in x.values()],[])
 if isinstance(x,list): return sum([pick(v) for v in x],[])
 return []
(L/'ledger-excerpts.json').write_text(json.dumps(pick(ledger),indent=2))
print('receipts',len(rows)); print((L/'ledger-excerpts.json').read_text())
