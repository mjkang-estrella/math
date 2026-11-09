from pathlib import Path
import os,json,hashlib,datetime,shutil
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research')
R=P/'frontier/campaigns/2026-10-14/t177c143-proof-r1'
A=P/'frontier/campaigns/2026-10-14/fresh-structural-discovery-r143'
E={'MANIFEST.json','FINAL.json','REPORT.md','SHA256SUMS'}
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def dump(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2)+'\n')
def blocked(s):
 s=s.lower()
 return (any(x in s for x in ['t177c143','t373e135','k369r134','t088p133'])
  or ('analytic' in s and any(x in s for x in ['r135','r136','r137']))
  or ('arithmetic' in s and 'r107' in s)
  or ('structural' in s and 'r144' in s))
assert not any((R/n).exists() for n in ['MANIFEST.json','FINAL.json','SHA256SUMS'])
obs=json.loads((R/'packet/private/current-originals-observation.json').read_text())
changes=[]
for x in obs['files']:
 rel=x['original'];assert not any(blocked(s) for s in Path(rel).parts)
 b=(P/rel).read_bytes()
 if sha(b)!=x['sha256']:
  q=R/'packet/private/current-originals-at-seal'/rel;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
  changes.append({'path':rel,'earlier_sha256':x['sha256'],'seal_sha256':sha(b),'copy':str(q.relative_to(R))})
for x in json.loads((R/'packet/private/incoming-observation.json').read_text())['files']:
 p=A/x['path'];b=p.read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256']
dump(R/'packet/private/final-original-observation.json',{'time':now(),'incoming_author_files_equal_intake':89,'named_originals_checked':len(obs['files']),'equal_prior_reviewer_observation':len(obs['files'])-len(changes),'changes':changes,'meaning':'Late bounded observations only; no initial or whole-parent preservation claim.'})
# Same read-only verifier whose bytes were read and whose copied controls passed.
v=(R/'packet/private/incoming-author/packet/public/verify.py').read_bytes()
assert sha(v)=='7c0ed9a9bf221dfdff1468f93e6300f6ed875b7feeeb885876f54744003a88d8'
(R/'packet/public/verify.py').write_bytes(v)
# The final invocation will execute this disposable copy, not original-author code.
(R/'work/final-verifier-copy.py').write_bytes(v)
rows=[];rejected=[]
for d,ds,fs in os.walk(R,topdown=True,followlinks=False):
 good=[]
 for s in ds:
  if blocked(s):rejected.append(str(Path(d)/s));continue
  assert not (Path(d)/s).is_symlink();good.append(s)
 ds[:]=good
 for s in fs:
  if blocked(s):rejected.append(str(Path(d)/s));continue
  p=Path(d)/s;assert not p.is_symlink()
  rel=p.relative_to(R).as_posix()
  if rel in E:continue
  b=p.read_bytes();rows.append({'path':rel,'bytes':len(b),'sha256':sha(b)})
assert not rejected,'Forbidden component pruned before descent/read; cannot seal exact root containing such members.'
rows.sort(key=lambda x:x['path'])
dump(R/'MANIFEST.json',{'format':'r143-exact-files-v1','role':'T177C143 first independent correctness review','scope':'Every payload file in the exclusive review root, including private incoming copies and disposable controls; excludes exactly four root envelopes. Nested manifests are incoming/control evidence, not additional review inventories.','envelopes':sorted(E),'files':rows})
dump(R/'FINAL.json',{'candidate':'T177C143','round':'first independent correctness review','verdict':'PASS','scope':'Entire unchanged universal finite (A),(B), all stochastic nonlinear sections/grand couplings and pairs, exact Source177 d>=3/admissible odd primes/all m>=2, all finite (C), both logarithmic constants and uniform ordinary-cofilling/L1 fibre-metric separation.','required_mathematical_repairs':[],'unresolved_frozen_clauses':[],'stipulated_source_pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','runner':'Codex / GPT-6.1-Sol / high / default service tier','sealed':now(),'publication':'STOPPED','contribution_verdict':None,'other_gates_assigned':False,'review_path':'packet/public/review.md','reading_limits_path':'packet/public/reading-and-evidence-limits.md','manifest_sha256':sha((R/'MANIFEST.json').read_bytes()),'report_sha256':sha((R/'REPORT.md').read_bytes()),'verifier_path':'packet/public/verify.py','verifier_sha256':sha(v),'reviewed_scope_path':'packet/private/incoming-author/packet/public/frozen-scope.md','reviewed_scope_sha256':'cc916afef1373c1b3c0abdee271a4c2769f887f664e8c9b2b16b1b381c0de221','payload_files':len(rows),'limitations':'Bounded primary/history reads; initial unguarded filename traversal, later derivative false admissions, late original captures and mutable ledger observations disclosed. No perfect isolation, priority or whole-parent certificate. Artifact checks are not mathematical gates.'})
anchors={n:sha((R/n).read_bytes()) for n in ['FINAL.json','MANIFEST.json','REPORT.md']}
(R/'SHA256SUMS').write_text(''.join(anchors[n]+'  '+n+'\n' for n in anchors))
print(json.dumps({'payload_files':len(rows),'payload_bytes':sum(x['bytes'] for x in rows),'final_original_observation_changes':changes,'anchors':anchors},indent=2))
