from pathlib import Path
import hashlib,json,datetime
O=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((O/'finalmanifest.json').read_text());exclude={'finalmanifest.json','verification-receipt.json'}
assert set(m['exclusions'])==exclude
assert set(m['files'])=={str(p.relative_to(O)) for p in O.rglob('*') if p.is_file() and str(p.relative_to(O)) not in exclude}
assert all(sha(O/n)==h for n,h in m['files'].items())
b=json.loads((O/'input-bindings.json').read_text())
assert all(sha(Path(x['original']))==sha(O/x['copy'])==x['sha256'] for x in b['scientific_inputs'])
r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','manifest_sha256':sha(O/'finalmanifest.json'),'manifest_entries_verified':len(m['files']),'scientific_original_copy_pairs_verified':len(b['scientific_inputs']),'manifest_exclusions':sorted(exclude),'administrative':'snapshots verified within manifest only; mutable originals deliberately not checked','verification':'separate guarded invocation after final writes; receipt is excluded by design'}
(O/'verification-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
