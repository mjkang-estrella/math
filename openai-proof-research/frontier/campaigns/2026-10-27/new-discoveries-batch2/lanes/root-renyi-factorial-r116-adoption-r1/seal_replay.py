import json,hashlib
from pathlib import Path
r=Path(__file__).resolve().parent
p=r/'extracted/replay-receipt.json'
d=json.loads(p.read_text())
assert d['declaration_count']==104 and len(d['modules'])==11
names={q['name']:q for q in d['declarations']}
for n in ['Renyi.every_order_counterexample','Renyi.not_source_threshold']:
 assert n in names and names[n]['actual_type']
for q in names.values():
 assert not(q['unsafe'] or q['partial'] or q['axiom'])
 assert set(q['axioms'])<={'propext','Classical.choice','Quot.sound'}
assert all(q['exit']==0 and q['kill'] is None for q in d['steps'])
receipt={'status':'ROOT_FRESH_EXTRACTED_REPLAY_PASS','modules':11,'declarations':104,
 'receipt_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),
 'archive_sha256':d['archive_sha256'],'endpoints':{n:names[n]['actual_type'] for n in names if n in ['Renyi.every_order_counterexample','Renyi.not_source_threshold']},
 'peak_group_rss_kib':max(q['peak_group_rss_kib'] for q in d['steps']),
 'credit':0,'counts':[8,38],'next':'Manuscript and deterministic packet, then independent final review'}
(r/'ROOT-REPLAY.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
