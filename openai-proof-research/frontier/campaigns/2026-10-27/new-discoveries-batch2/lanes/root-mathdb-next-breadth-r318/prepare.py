import hashlib, json
from pathlib import Path

L=Path(__file__).resolve().parent
B=L.parent
inputs={
 'coverage.json':B/'root-mathdb-breadth-intake-r316/coverage-delta.json',
 'ranked.jsonl':B/'pi-mathdb-full-corpus-inventory-r301/tags/review-queue-top.jsonl',
}
(L/'frozen').mkdir(exist_ok=True)
bindings=[]
for name,source in inputs.items():
 data=source.read_bytes()
 target=L/'frozen'/name
 if target.exists(): assert target.read_bytes()==data
 else: target.write_bytes(data)
 bindings.append({'source':str(source),'copy':str(target.relative_to(L)),'sha256':hashlib.sha256(data).hexdigest()})
(L/'bindings.json').write_text(json.dumps(bindings,indent=2)+'\n')
rows=[json.loads(line) for line in (L/'frozen/ranked.jsonl').read_text().splitlines()]
covered=json.loads((L/'frozen/coverage.json').read_text())
selected=[]
seen=set()
for row in rows:
 ident=int(row['mathdb_id'])
 if str(ident) in covered or ident in seen: continue
 if row.get('status')!='open' or row.get('statement_completeness')!='full': continue
 selected.append(row)
 seen.add(ident)
 if len(selected)==50: break
assert len(selected)==50 and not seen.intersection(map(int,covered))
(L/'reserved-ids.json').write_text(json.dumps([r['mathdb_id'] for r in selected],indent=2)+'\n')
(L/'queue.json').write_text(json.dumps({'status':'prepared_not_assigned_not_reviewed','rows':selected,'selection':'First 50 full-labelled open records in the frozen heuristic queue outside every r316 coverage-overlay ID. No mathematical tractability, source validity, deduplication or novelty clearance is inferred.'},indent=2)+'\n')
manifest={str(p.relative_to(L)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in ('manifest.json','verification-receipt.json')}
(L/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'prepared_ids':len(selected),'overlap_with_previous_coverage':0,'assigned':False,'technical_review_added':0,'manifest_entries':len(manifest)}))
