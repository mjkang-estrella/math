import os,resource,signal
for key in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):os.environ[key]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(25,25));signal.alarm(40)
from pathlib import Path
import json,hashlib,re,shutil,datetime
from fractions import Fraction
L=Path(__file__).parent;B=L.parent.parent;utc=datetime.datetime.now(datetime.timezone.utc).isoformat();digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Compare candidate replay semantically (timestamps deliberately differ).
a=json.loads((B/'lanes/sol-bbg-full-tail-r2/checks.json').read_text());b=json.loads((L/'input/checks.json').read_text());keys=['finite_upper','tail_upper','total_upper','finite_hits','finite_rows','tail_rows','pi_lower_scaled','pi_upper_scaled','pi_scale','remote_upper']
assert all(a[k]==b[k] for k in keys)
(L/'replay-comparison.json').write_text(json.dumps(dict(status='PASS',keys=keys,total_upper=a['total_upper'],original_sha256=digest(B/'lanes/sol-bbg-full-tail-r2/checks.json'),copied_replay_sha256=digest(L/'input/checks.json')),indent=2))
# Preserve own copies of bounded inherited registries and delta evidence.
cache=B/'lanes/sol-fresh-analysis-source-r22/sources';P=B/'lanes/sol-polyomino57-current-prior-review-r2';screen=[]
files=[cache/n for n in ['omega-D5-current-tree.json','omega-Problems-current-tree.json','openai-openai-preprints-tree.json','aim-full-current-tree.json','count-count-full-tree.json']]+[P/'sources/omega-latest-delta.diff',P/'input/sol-polyomino57-preliminary-review-r1/sources/omega-new-delta.diff',L/'input/sources/omega-delta.txt']
patterns=re.compile(r'borwein|boppana|sinusoidal|373621|2603[./]14548|2007[./]11017|borweinsineseries',re.I)
for i,p in enumerate(files):
 target=L/'sources'/('registry-'+str(i)+'-'+p.name);shutil.copyfile(p,target);txt=target.read_text(errors='replace')
 if p.suffix=='.json':
  d=json.loads(txt);paths=[r['path'] for r in d['tree']];matches=[s for s in paths if patterns.search(s)];detail=dict(entries=len(paths),truncated=d.get('truncated'),matches=matches)
 else:detail=dict(diff_headers=len(re.findall('^diff --git ',txt,re.M)),matches=[s[:500] for s in txt.splitlines() if patterns.search(s)])
 screen.append(dict(original=str(p),copy=str(target.relative_to(L)),sha256=digest(target),**detail))
heads={}
for n in ['openai.html','aim-current.html','count-current.html','omega-current.html']:
 txt=(L/'sources'/n).read_text();heads[n]=sorted(set(re.findall(r'"currentOid":"([0-9a-f]{40})"',txt)))
(L/'registry-screen.json').write_text(json.dumps(dict(utc=utc,current_root_heads=heads,coverage='inherited complete scoped snapshots plus bounded deltas, not complete current body coverage',files=screen),indent=2))
# Frozen originals, including exact path inventory.
before=json.loads((L/'hash-before.json').read_text());after=[]
for row in before['files']:
 p=Path(row['path']);h=digest(p);assert h==row['sha256'];after.append(dict(path=str(p),sha256=h,bytes=p.stat().st_size))
assert {str(p) for p in (B/'lanes/sol-bbg-full-tail-r2').rglob('*') if p.is_file()}=={r['path'] for r in before['files']}
(L/'hash-after.json').write_text(json.dumps(dict(utc=utc,status='PASS_UNCHANGED',files=after),indent=2))
receipt=json.loads((L/'independent-receipt.json').read_text());assert Fraction(receipt['total_upper'])<Fraction(2163292,1000000)<Fraction(21635,10000)<Fraction(receipt['Ei_lower'])
provenance=dict(utc=utc,role='SOLO independent adversarial preliminary review; no children',recommendation='HOLD',source='PASS',ordinary_math='PASS',bounded_novelty_substantive='HOLD',unconditional_formal_feasibility='HOLD',credit=0,counts=dict(additional=5,total=35),frozen_files_unchanged=len(after),fresh_check=dict(script='independent.py',receipt='independent-receipt.json',sha256=digest(L/'independent.py'),method=receipt['method'],wall_seconds=receipt['wall_seconds'],hits=receipt['hits']),candidate_replay='replay-comparison.json',resource_limits=dict(AS=512*1024**2,CPU_seconds=240,wall_seconds=280,BLAS_threads=1),source_receipts=['http-receipts.json','http-followup.json','http-primary.json'],registry='registry-screen.json',access_limits=['ResearchGate prior403 respected; complete companion body unread','MathDB API prior403 not repeated','AoPS web reader returned FAQ instead of discussion','MO body read through web before subsequent direct403; no requests after403','Initial two guessed GitHub registry URLs404 recorded, corrected using actual cached addresses','No complete new current registry tree; path/README screen does not prove absence'],formal_obstacle='No unconditional kernel global approximation bound exhibited; AxiomMath endpoint explicitly assumes PiIrrBound',strongest_countercase='Classical packing/known irrationality plus certified arithmetic may be routine correction of a weak numerical guess; no located prior complete separator, substantive HOLD rather than automatic FAIL',external_mutations=False,git_operations=False,browser_tabs=False,children=False)
provenance['artifacts']=[dict(path=str(p.relative_to(L)),sha256=digest(p),bytes=p.stat().st_size) for p in sorted(L.rglob('*')) if p.is_file() and 'input' not in p.relative_to(L).parts and p.name!='provenance.json']
(L/'provenance.json').write_text(json.dumps(provenance,indent=2));print(json.dumps(dict(status='DONE',recommendation='HOLD',frozen_files=len(after),heads=heads,screen=[{k:v for k,v in r.items() if k in ['copy','entries','diff_headers','matches']} for r in screen]),indent=2))
