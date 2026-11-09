exec((__import__('pathlib').Path(__file__).parent/'bind.py').read_text().split("assert bind(I/'manifest.json')")[0])
refs={e['path']:e for e in j(P/'flat-bindings.json')}
for rel in ['root-mathdb-accepted-exclusions-r304/accepted-exclusions.json','root-mathdb-accepted-exclusions-r304/historical-dispositions.json','root-mathdb-cayley-review-intake-r363/DECISION.md']:
 bind(L/rel)
(P/'flat-bindings.json').write_text(json.dumps(list(refs.values()),indent=2)+'\n')
for p in [B/'ledger.json',B/'prior-campaign-context.json',I/'adjudications.json',I/'hypothesis-queue.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md']:
 print(str(p),p.read_text()[:16000])
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 obj=j(L/'root-mathdb-accepted-exclusions-r304'/name);print(name,json.dumps(obj,ensure_ascii=False)[:11000])
q=j(I/'queue-r724.json');ids={r['mathdb_id'] for r in q};cov=j(I/'coverage-delta.json');assert len(cov)==8983
active=j(I/'active-breadth-reservations.json');seen=set()
for r in active:
 s=set(r['ids']);assert len(s)==50 and not s&seen and not s&set(map(int,cov)) and not s&set(r['protected_ids']);seen|=s
assert ids==set(j(I/'reserved-ids-r724.json')['ids']) and len(ids)==50
out=[]
for p in sorted((C/'corpus').glob('*.jsonl')):
 for n,l in enumerate(p.open(),1):
  r=json.loads(l)
  if r['mathdb_id'] in ids:
   out.append({'mathdb_id':r['mathdb_id'],'corpus_chunk':str(p.relative_to(C)),'corpus_line':n,'record':r,'canonical_record_sha256':h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()),'statement_utf8_sha256':h(r['statement'].encode())})
assert len(out)==50
out.sort(key=lambda x:[r['mathdb_id'] for r in q].index(x['mathdb_id']))
(P/'literal-records.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
for x in out:
 r=x['record'];print('\nID',r['mathdb_id'],r['title'],'SOURCE',r['source_url'],'\n'+r['statement'])
