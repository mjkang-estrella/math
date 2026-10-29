import close,collections,json,re,sys,pathlib
L=close.L;rows=close.load(L/'bodies.json')
if sys.argv[1]=='extend':
 new={};receipts=[]
 for r in rows:
  if '/context/' not in r['path'] or r['status']!='ok':continue
  obj=close.load(L/r['source']);sources={};atoms=set()
  for x in obj:
   sources[x['SourcePath']]=x['SourceSha256']
   for e in x['Entries']:
    atoms.add(e['AtomId'])
    for oc in e['Occurrences']:
     for g in oc.get('GoverningContext',[]):atoms.add(g['AtomId'])
  receipts.append(dict(context=r['path'],ref=r['ref'],sources=sources,atoms=sorted(atoms),disposition='JSON decoded completely; pointers to source text/atoms, not embedded encoded mathematical payload; fetch actual pointed-to source and primary/governing atoms'))
  for p in list(sources)+['Meta/Digestion/atoms/sha256/'+a for a in atoms]:
   key=r['repo']+'|'+r['ref']+'|'+p
   new[key]=dict(repo=r['repo'],ref=r['ref'],path=p,reasons=['context-payload'],blob=None,status='pending')
 old={r['repo']+'|'+r['ref']+'|'+r['path'] for r in rows};rows += [v for k,v in new.items() if k not in old]
 close.save('context-decoding.json',receipts);close.save('bodies.json',rows);print('context refs',len(receipts),'new payload bodies',len(new.keys()-old),'total',len(rows))
else:
 counts=collections.Counter(r['status'] for r in rows);print(counts)
 for r in rows:
  if r['status']=='ok' and (r['read']['hit_count'] or r['read']['opaque_candidates']):
   print(r['path'],r['source'],r['read']['hits'][:8],r['read']['opaque_candidates'])
