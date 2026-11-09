from pathlib import Path
import re,json,hashlib
p=Path(__file__).resolve().parent
log=(p/'strict-replay.log').read_text()
assert 'PASS strict replay;' in log
assert 'error:' not in log
allowed={'propext','Classical.choice','Quot.sound'}
rows=re.findall(r"depends on axioms: \[([^\]]*)\]",log)
assert len(rows)>=1100,len(rows)
for row in rows:
 assert {s.strip() for s in row.split(',') if s.strip()}<=allowed,row
bindings=json.loads((p/'input-bindings.json').read_text())
assert all(hashlib.sha256((p.parent/k).read_bytes()).hexdigest()==v for k,v in bindings.items())
source_hashes={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in (p/'formal').glob('*.lean')}
clean_hashes={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in (p/'clean-replay').glob('*.lean')}
assert source_hashes==clean_hashes
report={'strict_replay':'PASS','warnings_as_errors':True,'axiom_audit_entries':len(rows),'all_axioms_allowed':True,'source_matches_extraction':True,'all_immutable_input_hashes_still_match':True,'full_counterexample_endpoint':False}
(p/'strict-replay-result.json').write_text(json.dumps(report,indent=2))
r=json.loads((p/'results.json').read_text());r['strict_replay']=report;(p/'results.json').write_text(json.dumps(r,indent=2))
print(json.dumps(report,indent=2))
