from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent
aud=json.loads((L/'audit.json').read_text())
rep=json.loads((L/'replay-receipt.json').read_text())
assert rep['status']=='PASS'
assert not [p for p in L.rglob('*') if p.suffix in {'.olean','.ilean','.ir','.o','.so','.pyc'}]
attempts=[(p,json.loads(p.read_text())) for p in sorted(L.glob('attempt-*.json'))]
fail=[str(p.relative_to(L)) for p,r in attempts if r['exit']!=0]
r=dict(status='PARTIAL: certified components PASS; requested interval bounds OPEN',
 declarations=len(aud['declarations']),transitive=aud['transitive'],origins=aud['origins'],
 all_eleven_inherited_modules_byte_identical=True,
 archive_sha256=hashlib.sha256((L/'source-only.zip').read_bytes()).hexdigest(),
 extracted_replay='PASS',compiled_artifacts_removed=True,
 peak_lean_group_rss=max(r['peak_group_rss'] for _,r in attempts),
 max_lean_seconds=max(r['seconds'] for _,r in attempts),
 failures_preserved=fail,
 closed=['actual length/parameter applicability','actual rational/real length pushforwards','actual real normalized cell mixture','finite thinning vector mass identity','all fair-binomial atoms rational squared bound'],
 residuals=['finite U cardinality first/second moments and variance inequality','finite Chebyshev','conditional fair subset cardinality law','interval atom count and generic Poisson-binomial bound','mu-to-L monotonicity and actual good/bad mixture upper bound','combination with actual_finite_tail'],
 counts_changed=False)
(L/'implementation-receipt.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:r[k] for k in ['status','declarations','transitive','peak_lean_group_rss','max_lean_seconds']}))
