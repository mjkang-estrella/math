import json,hashlib
from pathlib import Path
r=Path(__file__).resolve().parent
p=r/'extracted/replay-receipt.json'
d=json.loads(p.read_text())
assert d['declaration_count']==31 and d['initial_own_prebuilt_artifacts']==0 and d['mathematical_compilelog_bytes']==0
assert len({q['name'] for q in d['declarations']})==31
for q in d['declarations']:
 assert q['actual_type'] and not(q['unsafe'] or q['partial'] or q['axiom'])
 assert set(q['transitive_axioms'])<={'propext','Classical.choice','Quot.sound'}
assert all(q['exit']==0 and q['kill'] is None for q in d['steps'])
endpoints={q['name']:q['actual_type'] for q in d['declarations'] if q['name'].endswith(('source_statement_negation','disjoint_nonempty_counterexample','literal_set_equality'))}
assert 'FactorialProduct.integer_source_statement_negation' in endpoints
s=r.parent/'sol-factorial-product-source-formal-r1'
assert (r/'extracted/logs/FullAudit.log').read_bytes()==(s/'logs/FullAudit.log').read_bytes()
o={'status':'ROOT_SOURCE_ONLY_EXTRACTED_REPLAY_PASS','declarations':31,'mathematical_modules':1,'archive_sha256':d['archive_sha256'],'receipt_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'actual_audit_byte_identical_to_worker':True,'peak_group_rss_kib':max(q['peak_group_rss_kib'] for q in d['steps']),'endpoints':endpoints,'credit':0,'counts':[8,38]}
(r/'ROOT-REPLAY.json').write_text(json.dumps(o,indent=2)+'\n')
print(json.dumps({k:v for k,v in o.items() if k!='endpoints'}))
