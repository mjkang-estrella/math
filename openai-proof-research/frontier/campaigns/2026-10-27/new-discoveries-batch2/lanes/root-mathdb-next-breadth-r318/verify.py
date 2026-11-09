import hashlib,json
from pathlib import Path
L=Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
bindings=json.loads((L/'bindings.json').read_text())
for b in bindings:
 assert sha(Path(b['source']))==sha(L/b['copy'])==b['sha256']
manifest=json.loads((L/'manifest.json').read_text())
files={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in ('manifest.json','verification-receipt.json')}
assert files==set(manifest)
for name,value in manifest.items(): assert sha(L/name)==value,name
ids=json.loads((L/'reserved-ids.json').read_text())
covered=json.loads((L/'frozen/coverage.json').read_text())
assert len(ids)==len(set(ids))==50
assert not set(ids).intersection(map(int,covered))
queue=json.loads((L/'queue.json').read_text())
assert queue['status']=='prepared_not_assigned_not_reviewed'
assert ids==[r['mathdb_id'] for r in queue['rows']]
assert all(r['status']=='open' and r['statement_completeness']=='full' for r in queue['rows'])
result={'pass':True,'payload_files':len(manifest),'bindings':len(bindings),'reserved_ids':50,'overlap':0,'technical_reviews_added':0,'assigned':False}
(L/'verification-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
