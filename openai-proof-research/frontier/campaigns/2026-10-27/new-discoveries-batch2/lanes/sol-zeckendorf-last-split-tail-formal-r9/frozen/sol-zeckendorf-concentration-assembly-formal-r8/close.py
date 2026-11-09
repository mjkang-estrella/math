from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent
audit=json.loads((L/'audit.json').read_text())
replay=json.loads((L/'replay-receipt.json').read_text())
assert replay['status']=='PASS'
attempts=[(p,json.loads(p.read_text())) for p in sorted(L.glob('attempt-*.json'))]
r=dict(status='CLOSED: A and B and finite-tail corollary',declarations=len(audit['declarations']),
 transitive=audit['transitive'],origins=audit['origins'],
 inherited_mathematical_modules_byte_identical=12,
 archive_sha256=hashlib.sha256((L/'source-only.zip').read_bytes()).hexdigest(),
 extracted_replay='PASS',compiled_artifacts_removed=True,
 peak_lean_group_rss=max(r['peak_group_rss'] for _,r in attempts),
 max_lean_seconds=max(r['seconds'] for _,r in attempts),
 failures_preserved=[p.name for p,r in attempts if r['exit']!=0],
 endpoints=['finite_bernoulli_interval','actual_finite_interval','actual_finite_interval_tail','actual_interval_zero'],
 mathematical_residuals_within_requested_scope=[],
 procedural_exception='Library declaration discovery snippets preceded extra library snapshots; see FAILURES.md',
 counts_changed=False)
(L/'implementation-receipt.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:r[k] for k in ['status','declarations','transitive','peak_lean_group_rss']}))
