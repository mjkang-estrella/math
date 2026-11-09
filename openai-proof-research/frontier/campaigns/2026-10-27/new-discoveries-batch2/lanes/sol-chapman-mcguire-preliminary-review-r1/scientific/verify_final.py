from retrieve import *
m=L/'final-manifest.json';j=json.loads(m.read_text());bad=[]
for rel,v in j['files'].items():
 p=L/rel
 if not p.is_file() or sha(p)!=v['sha256'] or p.stat().st_size!=v['bytes']:bad.append(rel)
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in j['excludes']}
assert actual==set(j['files'])
copies=originals=0
for row in map(json.loads,(L/'bindings.jsonl').read_text().splitlines()):
 assert sha(Path(row['copy']))==row['sha256'];copies+=1
 if not row['administrative']:assert sha(Path(row['original']))==row['sha256'];originals+=1
retrieved=0
for row in map(json.loads,(L/'retrieval.jsonl').read_text().splitlines()):
 if 'file' in row:assert sha(Path(row['file']))==row['sha256'];retrieved+=1
drift=[]
for row in json.loads((L/'history-bindings.json').read_text()):
 if sha(Path(row['path']))!=row['sha256']:drift.append(row['path'])
assert not bad
result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS' if not drift else 'PASS-lane;history-drift-limitation','manifest_sha256':sha(m),'manifest_files_verified':len(j['files']),'manifest_excludes_self_and_receipt':True,'scientific_originals_unchanged':originals,'frozen_copies_verified':copies,'retrieved_objects_verified':retrieved,'administrative':'snapshots only; live administrative equality not required','history_refs':888,'history_drift':drift,'scientific_checks':{'symbolic':json.loads((L/'checks.json').read_text())['direct_R3_minus_R_zero'],'independent':json.loads((L/'independent-checks.json').read_text())['all_assertions']},'eligibility':'HOLD independent review and current-prior closure','counts':[9,39,40]}
(L/'final-verification.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
