exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split("bind(I/'manifest.json')")[0])
q=load(I/'queue-r702.json');ids={int(e['mathdb_id']) for e in q};out=[]
for p in sorted((R/'corpus').glob('mathdb-normalized-chunk-*.jsonl')):
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if int(r.get('id',r.get('mathdb_id',-1))) in ids:
   out.append({'chunk':str(p),'line':n,'record':r,'canonical_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(out)==50
(D/'literal-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
for i,e in enumerate(out):print(i,e['record'])
print('RESERVATIONS',load(I/'active-breadth-reservations.json'))
print('ADJUDICATIONS',load(I/'adjudications.json'))
print('HYPOTHESES',load(I/'hypothesis-queue.json'))
print('R363',(L/'root-mathdb-cayley-review-intake-r363/DECISION.md').read_text())
for rel in ['accepted-exclusions.json','historical-dispositions.json']:
 x=load(L/'root-mathdb-accepted-exclusions-r304'/rel);print('R304',rel,'schema',type(x).__name__,'matching assigned', {str(k):v for k,v in x.items() if str(k) in set(map(str,ids))} if isinstance(x,dict) else [e for e in x if str(e.get('mathdb_id',e.get('id'))) in set(map(str,ids))])
