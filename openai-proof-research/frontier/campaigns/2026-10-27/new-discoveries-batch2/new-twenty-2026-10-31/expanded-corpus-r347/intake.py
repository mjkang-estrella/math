r=read(L/'reservation.json'); expected='e724eaaf62bab19049af6aa82db66a5eddca94df9a6c189064078ef27a0641b0'; assert sha(r)==expected
save('reservation-before.json',{'sha256':sha(r),'expected':expected,'matches':True,'sidecar':read(L/'reservation.sha256').decode()})
r=json.loads(r); ids=set(r['ids']); assert len(ids)==20
root=L.parents[4]
# Scalar-only shared status reads.
for base in [L.parent,L.parents[1]]:
 for name in ['ledger.json','STATUS.md']:
  f=base/name
  if f.is_file():
   b=read(f)
   if name.endswith('json'):
    d=json.loads(b); print('SCALARS',str(f),{k:v for k,v in d.items() if k in ['accepted_new','target']})
   else: print('STATUS scalar',str(f),re.findall(r'52\s*/\s*60',b.decode()))
corpus=L.parents[1]/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
found={}
for p in sorted(corpus.glob('mathdb-normalized-chunk-*.jsonl')):
 b=read(p); ch=sha(b)
 for i,line in enumerate(b.splitlines(keepends=True),1):
  row=json.loads(line); mid=row.get('mathdb_id',row.get('id'))
  if mid in ids or str(mid) in {str(x) for x in ids}:
   mid=int(mid); assert mid not in found; assert line.endswith(b'\n')
   write('literal/'+str(mid)+'.jsonl',line)
   statement=row.get('statement',''); statement=statement if isinstance(statement,str) else json.dumps(statement,ensure_ascii=False)
   found[mid]={'id':mid,'chunk':str(p),'one_based_line':i,'chunk_sha256':ch,'raw_sha256':sha(line),'final_newline':True,'statement_utf8_sha256':sha(statement.encode()),'record':row}
assert set(found)==ids
save('provenance.json',found)
for mid,x in found.items(): print(mid,json.dumps(x['record'],ensure_ascii=False))
# Exact completed allowlist only; protected path filtering precedes opening.
a=json.loads(read(L/'historical-results-allowlist.json')); matches=[]
for item in a:
 p=Path(item)
 if 'crown' in str(p).lower() or 'transitive-bunkbed-reach-bridge-formal-pi-r4' in str(p): continue
 if not p.is_file(): continue
 b=read(p); text=b.decode()
 hits=[str(i) for i in ids if str(i) in text]
 families=[row['source_url'].split('/')[-1] for row in r['rows'] if row['source_url'].split('/')[-1] in text]
 if hits or families: matches.append({'path':str(p),'ids':hits,'source_families':families,'content':json.loads(b)})
save('history-matches.json',matches); print('HISTORY MATCHES',[(m['path'],m['ids'],m['source_families']) for m in matches])
