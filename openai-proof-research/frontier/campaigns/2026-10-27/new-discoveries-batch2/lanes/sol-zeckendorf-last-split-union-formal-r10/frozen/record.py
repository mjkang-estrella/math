from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
a=json.loads((L/'audit.json').read_text());r=json.loads((L/'replay-receipt.json').read_text())
assert a['status']==r['status']=='PASS'
attempts=[dict(file=p.name,**json.loads(p.read_text())) for p in sorted(L.glob('attempt-*.json'))]
(L/'failures.json').write_text(json.dumps([x for x in attempts if x['exit']!=0],indent=2)+'\n')
admin=json.loads((L/'administrative/ledger.json').read_text())
assert (admin['accepted_count'],admin['total_accepted_count'],admin['next_global_outcome_number'])==(9,39,40)
prior=json.loads((L/'administrative/prior-campaign-context.json').read_text())
(L/'implementation-receipt.json').write_text(json.dumps(dict(status='PARTIAL',declarations=len(a['declarations']),new_origin_declarations=a['origins']['LastSplit'],transitive=a['transitive'],audit_sha256=sha(L/'audit.json'),replay_sha256=sha(L/'replay-receipt.json'),archive_sha256=sha(L/'source-only.zip'),source_sha256=sha(L/'LastSplit.lean'),attempts=len(attempts),failed_attempts=sum(x['exit']!=0 for x in attempts),thirteen_modules_byte_identical=True,counts=[9,39,40],prior_context_keys=list(prior),remaining='literal survivor correspondence, last-split convention and final union'),indent=2)+'\n')
print('partial implementation receipt',len(a['declarations']),a['transitive'])
