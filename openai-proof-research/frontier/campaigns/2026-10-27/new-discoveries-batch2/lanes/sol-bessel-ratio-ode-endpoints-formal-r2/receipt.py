import json,hashlib,tarfile
from pathlib import Path
L=Path(__file__).resolve().parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
R=L/'fresh-replay'
manifest=json.loads((L/'component-manifest.json').read_text())
assert all(H(L/n)==h and H(R/n)==h for n,h in manifest.items())
runs=[json.loads(s) for s in (R/'runs.jsonl').read_text().splitlines()]
assert len(runs)==8 and all(r['rc']==0 and r['kill_reason'] is None for r in runs)
assert all(r['peak_group_rss']<2800*1024**2 and r['seconds']<230 for r in runs)
assert (R/'audit.log').read_text().rstrip().endswith('AUDIT_TOTAL 106')
assert len((R/'declaration-names.txt').read_text().splitlines())==106
assert H(R/'audit.log')==H(L/'audit.log')
with tarfile.open(L/'component.tar.gz') as t:
 assert not any('.olean' in n or n.endswith('.ilean') for n in t.getnames())
base=L.parent/'sol-bessel-ratio-series-formal-r1/component.tar.gz'
assert H(base)==H(L/'base-component.tar.gz')
p=json.loads((L/'provenance.json').read_text())
for n,h in p['core_sha256'].items():assert H(L/n)==h
receipt=dict(status='PASS: all five closed propositions and eventual W positivity',credit=0,novelty='HOLD',root_counts=[7,37],base_sha256=H(base),archive_sha256=H(L/'component.tar.gz'),manifest_sha256=H(L/'component-manifest.json'),fresh_replay='fresh-replay',all_eight_replay_runs_pass=True,audit_declarations=106,audit_sha256=H(R/'audit.log'),declaration_names_sha256=H(R/'declaration-names.txt'),dependencies_sha256=H(R/'dependencies.txt'),replay_runs_sha256=H(R/'runs.jsonl'),peak_replay_group_rss=max(r['peak_group_rss'] for r in runs),allowed_axioms=['propext','Classical.choice','Quot.sound'],remaining_requested_formal_gaps=[],outside_assignment=['global one-crossing','source theorem unimodality','novelty and source acceptance'],protocol_limits='See SUMMARY.md: early helper monitoring/freeze deviations and one accidental stricter AS cap failure')
(L/'delivery-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
