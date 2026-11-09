from pathlib import Path
import hashlib,json,re
root=Path('.')
mods=['Base','Bridges','CountBase']+[f'S{i:02}' for i in range(20)]+[f'T{i:02}' for i in range(21)]+['Counts','Controls','Endpoint','Audit']
records=[]
for m in mods:
 assert Path(f'replay/logs/{m}.strict.ok').exists(), m
 for kind in ['strict','checker']:
  p=Path(f'replay/logs/{m}.{kind}.log');s=p.read_text()
  assert re.search(r'Exit status: 0\s*$',s), str(p)
  rss=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',s)[1])
  cpu=float(re.search(r'User time \(seconds\): ([0-9.]+)',s)[1])+float(re.search(r'System time \(seconds\): ([0-9.]+)',s)[1])
  assert rss < 6291456 and cpu < 120,(m,kind,rss,cpu)
  records.append(dict(module=m,phase=kind,exit_status=0,max_rss_kib=rss,cpu_seconds=round(cpu,2),log=str(p)))
audit=Path('replay/logs/Audit.strict.log').read_text()
assert 'flagged=[]' in audit
assert "'Smyth1512.not_conjecture15' depends on axioms: [propext, Classical.choice, Quot.sound]" in audit
assert Path('replay/logs/source-scan.log').read_text()==''
for p in Path('src').glob('*.lean'):
 assert p.read_bytes()==(Path('replay/src')/p.name).read_bytes(),p
result=dict(status='formalization_complete_pending_root_review',accepted=False,credit=0,mathdb_id=332037,theorem='Smyth1512.not_conjecture15',statement='¬ Smyth1512.Conjecture15',parameters=dict(A=3,a=20,B=2,b=19),card_S=1137,card_T=1134,lean_version='4.34.1',mathlib_revision='d13f23b723b8a846827a245b89c10fc7d3f11612',source_zip_sha256=hashlib.sha256(Path('source-only.zip').read_bytes()).hexdigest(),fresh_extraction='replay',modules=len(mods),strict_compilations=len(mods),explicit_module_leanchecker_passes=len(mods),axioms=['propext','Classical.choice','Quot.sound'],metadata_flagged=[],nonvacuity='A = B = a = b = 1; identity injection; nonempty_control',source_scan='pass',caps=dict(rss_kib=6291456,lean_M=3500,cpus=[0,1],cpu_seconds=120,wall_seconds=140,malloc_arena_max=2),max_observed_rss_kib=max(r['max_rss_kib'] for r in records),max_observed_cpu_seconds=max(r['cpu_seconds'] for r in records),checks=records,limitations=['No acceptance or novelty determination in this lane','Published journal body not checked','Independent fidelity review belongs to root'])
Path('results.json').write_text(json.dumps(result,indent=2)+'\n')
summary=f'''# Smyth formalization handback

Completed the Lean formalization lane for MathDB 332037. Status: pending root review; no acceptance and zero credit claimed.

- Endpoint: `Smyth1512.not_conjecture15 : ¬ Smyth1512.Conjecture15` in `src/Endpoint.lean`.
- Literal universal definitions preserve the source quantifiers and domain-dominates-image orientation.
- The eight-generator down-set has checked cardinalities |S| = 1137 and |T| = 1134 at (A,a,B,b) = (3,20,2,19).
- Non-increasing rearrangement is proved sorted and a permutation. A nonempty identity-injection instance supplies the non-vacuity control.
- Fresh extracted replay: all {len(mods)} modules compiled with warnings as errors, and all {len(mods)} explicit-module leanchecker calls passed. Logs are in `replay/logs`; the driver transcript is `logs/fresh-replay-driver.log`.
- Endpoint axioms: propext, Classical.choice, Quot.sound. Local declaration metadata: no flags. Mathematical source scan: clean.
- Maximum per-call observed RSS: {result['max_observed_rss_kib']} KiB; maximum CPU time: {result['max_observed_cpu_seconds']} seconds. Every call ran under the prescribed watchdog, affinity and limits.

Deliverables: `source-only.zip`, `PROOF.md`, `STATEMENT-CORRESPONDENCE.md`, `REPRODUCE.md`, `results.json`, and full replay logs. Source zip SHA256: `{result['source_zip_sha256']}`.

Development limitations and failures are recorded in `logs/development-incidents.md`, `logs/CountsTest.log`, `logs/Audit-before-structural.log`, and `replay-failed-structural/logs`. No resource limit was increased. The final enumerator uses Nat.rec directly to avoid compiler-generated unsafe recursion helpers.

Root must reconcile the independent source-fidelity review and novelty requirements before any acceptance. This lane used only cached source material and did not inspect the published journal body.
'''
Path('SUMMARY.md').write_text(summary)
print(json.dumps({k:result[k] for k in ['status','modules','max_observed_rss_kib','max_observed_cpu_seconds','source_zip_sha256']},indent=2))
