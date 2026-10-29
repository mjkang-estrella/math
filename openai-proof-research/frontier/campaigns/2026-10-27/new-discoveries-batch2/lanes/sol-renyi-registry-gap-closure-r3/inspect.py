import close,sys,collections,re
L=close.L;B=close.B
if sys.argv[1]=='summary':
 rows=close.load(L/'bodies.json')
 for k in ['baseline-relevant-path','missing-patch','semantic-hit']:
  rr=[r for r in rows if k in r['reasons']];print(k,len(rr))
  if k=='baseline-relevant-path':
   for r in rr:
    if re.search(r'renyi|rényi|fu.?li|09206|logconcav|reverseepi|entropyjump|entropyincrement|truncatedexp',r['path'],re.I):print(r['repo'],r['path'])
 for r in close.load(L/'patch-hits.json'):print('PATCH',r['path'],r['hits'])
else:
 for r in close.load(L/'bodies.json'):
  if r.get('status')=='ok' and (r['read']['hit_count'] or r['read']['opaque_candidates']):print(r['path'],r['source'],r['read'])
