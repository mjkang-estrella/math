exec((__import__('pathlib').Path(__file__).parent/'prepare.py').read_text().split('refs=')[0])
for e in j(P/'flat-bindings.json'):check(pathlib.Path(e['path']),e)
for n in ['adjudications.json','hypothesis-queue.json','reserved-ids-r726.json','active-breadth-reservations.json']:print(n,json.dumps(j(I/n)))
for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md']:
 print('CONTEXT',p.name,p.read_text()[:14000])
ids=set(j(I/'reserved-ids-r726.json')['ids']);out=[]
for p in sorted((C/'corpus').glob('*.jsonl')):
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   out.append({'corpus_path':str(p.relative_to(C)),'corpus_line':n,'record':r});print('RECORD',r['mathdb_id'],json.dumps(r,ensure_ascii=False))
assert len(out)==50
write('literal-records.json',out)
