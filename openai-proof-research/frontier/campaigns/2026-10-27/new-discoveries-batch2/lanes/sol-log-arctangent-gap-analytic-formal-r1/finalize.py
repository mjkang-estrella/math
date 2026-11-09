import hashlib,json,pathlib,re,resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(35,35))
b=pathlib.Path(__file__).resolve().parent
root=b.parent/'root-log-arctangent-formal-r1'
hashfile=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
freeze=json.loads((b/'analytic-bridge-freeze.json').read_text())
after={p:hashfile(b/p) for p in freeze['hashes']}
assert after==freeze['hashes']
assert all(hashfile(root/p)==h for p,h in after.items())
(b/'hash-after.json').write_text(json.dumps(after,indent=2)+'\n')
lean=pathlib.Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
mathlib=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib')
assert hashfile(lean)=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
assert (mathlib/'.git/HEAD').read_text().strip()=='d13f23b723b8a846827a245b89c10fc7d3f11612'
mods=['MeanSourceDefs','Stolarsky','Transfer','MeanAnalyticDefs','MeanDerivatives','GapAnalytic','Centered','GapMonotonicity']
for m in mods:
 assert hashfile(b/'formal'/(m+'.lean'))==hashfile(b/'fresh-source-replay'/(m+'.lean'))
 s=(b/'formal'/(m+'.lean')).read_text()
 assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',s)
 assert 'set_option autoImplicit false' in s and 'set_option warningAsError true' in s
receipts={p.stem:json.loads(p.read_text()) for p in sorted((b/'logs').glob('fresh-source-replay-*.json'))}
assert len(receipts)==9
assert all(r['exit']==0 and r['sampled_group_peak_rss']<3*1024**3 and r['termination_reason'] is None for r in receipts.values())
names=json.loads((b/'declaration-inventory.json').read_text())
audit=(b/'logs/fresh-source-replay-AllAudits.log').read_text()
reported=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",audit)
assert [n for n,a in reported]==names
for n,ax in reported: assert set(ax.split(', ')) <= {'propext','Classical.choice','Quot.sound'}
deps=sorted({line[7:] for m in mods for line in (b/'formal'/(m+'.lean')).read_text().splitlines() if line.startswith('import ')})
p=dict(date='2026-10-29',status='COMPLETE conditional analytic bridge; E positivity remains external',credit=0,counts=dict(additional=3,target_additional=30,total=33,target_total=60),lean_binary=str(lean),lean_sha256=hashfile(lean),mathlib=str(mathlib),mathlib_HEAD=(mathlib/'.git/HEAD').read_text().strip(),pin_verification='SHA256 binary plus direct read of detached mathlib .git/HEAD; no git commands',frozen_hashes_before=freeze['hashes'],frozen_hashes_after=after,new_sources={m+'.lean':hashfile(b/'formal'/(m+'.lean')) for m in mods[5:]},dependencies=deps,modules=8,declarations=98,new_declarations=25,axiom_audits=98,allowed_axioms=['propext','Classical.choice','Quot.sound'],fresh_replay=dict(source_only=True,copied_local_oleans=False,upstream_dependency_oleans=True,receipts=receipts,maximum_sampled_group_peak_rss=max(r['sampled_group_peak_rss'] for r in receipts.values()),wall_limit_seconds_per_invocation=180,rss_ceiling_bytes=3*1024**3,serial=True),diagnostics=dict(exact_numerical_diagnostics='none needed; all mathematics checked by Lean',finalize_AS_bytes=512*1024**2,finalize_CPU_seconds=35,BLAS_threads=1),endpoints=['LogArctangentSource.gap_strictMono_of_E_pos','LogArctangentSource.sourceClaim_of_E_pos'],remaining_premise='∀ t : ℝ, 0 < t → 0 < LogArctangentMean.E t',analytic_gaps=[],failures='See SUMMARY.md development failures; failed development logs were overwritten by the copied root monitor, and are not claimed archived. All fresh replay logs retained.',commands=['python3 compile.py formal -o <Module>.olean <Module>.lean','python3 replay.py','timeout 45s env OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1 python3 finalize.py'])
(b/'provenance.json').write_text(json.dumps(p,indent=2)+'\n')
(b/'receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
print('PASS: 8 modules, 98 type/axiom audits; frozen inputs before/after and Lean/mathlib pins verified')
print('Peak sampled process-group RSS:',p['fresh_replay']['maximum_sampled_group_peak_rss'])
