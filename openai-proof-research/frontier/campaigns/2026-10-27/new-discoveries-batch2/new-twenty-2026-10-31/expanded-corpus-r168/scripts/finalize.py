import pathlib,json,hashlib,datetime,zipfile
D=pathlib.Path(__file__).resolve().parents[1];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((D/'results.json').read_text());ids=json.loads((D/'reservation.json').read_text())['ids'];assert set(map(int,r))==set(ids) and len(r)==20
for i,v in r.items():
 b=(D/f'raw/{i}.jsonl').read_bytes();assert b.endswith(b'\n');assert hashlib.sha256(b).hexdigest()==v['provenance']['raw_sha256'];assert hashlib.sha256(v['statement'].encode()).hexdigest()==v['provenance']['statement_utf8_sha256']
assert (D/'lean/SplitMatching.lean').read_bytes()==(D/'replay/SplitMatching.lean').read_bytes()==(D/'extracted-packet/lean/SplitMatching.lean').read_bytes()
assert (D/'lean/Audit.lean').read_bytes()==(D/'extracted-packet/lean/Audit.lean').read_bytes()
s=(D/'lean/SplitMatching.lean').read_text();import re
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b',s)
checks={}
for k in ['extracted-build','extracted-audit','extracted-checker']:
 p=D/f'logs/{k}.receipt.json';o=json.loads(p.read_text());assert o['returncode']==0;checks[k]=o
assert 'AUDITED_DECLARATIONS 69' in (D/'logs/extracted-audit.log').read_text()
r['381751']['formal_validation']={'endpoint':'SplitMatching381751.literal_counterexample','strict_extracted_build':'PASS','leanchecker_explicit_module':'PASS','module_origin_audit_declarations':69,'allowed_axioms':['propext','Classical.choice','Quot.sound'],'packet':'Lean-packet.zip','packet_sha256':sha(D/'Lean-packet.zip'),'cache_trust':'Pinned upstream cache reused; no full upstream rebuild claim'}
(D/'results.json').write_text(json.dumps(r,indent=2,ensure_ascii=False)+'\n')
v={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'id_entries':20,'raw_provenance_checks':'PASS','source_equality':'PASS','banned_proof_tokens':'NONE','formal_checks':checks,'packet_sha256':sha(D/'Lean-packet.zip'),'result':'candidate only; zero root-accepted credit','resource_deviations':'See SUMMARY.md; brief overlap and no-module help attempt retained'}
(D/'outputs/final-validation.json').write_text(json.dumps(v,indent=2))
manifest={str(p.relative_to(D)):sha(p) for p in D.rglob('*') if p.is_file() and p.name!='manifest-sha256.json' and p.suffix not in ['.olean','.ir','.ilean']}
(D/'outputs/manifest-sha256.json').write_text(json.dumps(manifest,indent=2))
print(json.dumps({'entries':20,'audit_declarations':69,'packet_sha256':v['packet_sha256'],'validation':'PASS'}))
