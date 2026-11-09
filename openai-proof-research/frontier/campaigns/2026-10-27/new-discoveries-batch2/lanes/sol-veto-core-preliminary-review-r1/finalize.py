from pathlib import Path
import hashlib,json,datetime
O=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
b=json.loads((O/'input-bindings.json').read_text());checks=[]
for x in b['scientific_inputs']:
    a=sha(Path(x['original']));c=sha(O/x['copy'])
    checks.append(dict(x,original_after_sha256=a,copy_after_sha256=c,unchanged=a==c==x['sha256']))
assert all(x['unchanged'] for x in checks)
(O/'before-after-hashes.json').write_text(json.dumps({'utc':now(),'freeze_utc':b['utc'],'all_unchanged':True,'checks':checks,'administrative':'snapshot only; no live-original hash binding'},indent=2)+'\n')
guard=O.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
prov={'utc':now(),'review':'review.md','decisions':{'SOURCE':'PASS','MATH':'PASS ordinary','SUBSTANTIVE':'recommend EXCLUDE as complete routine source-proof adaptation; root adjudicates','NOVELTY':'bounded HOLD; no identical prior theorem claimed','FORMAL_FEASIBILITY':'favorable; no Lean performed'},'guard':{'path':str(guard.resolve()),'sha256':sha(guard),'AS_and_sampled_group_RSS_bytes':512*1024*1024,'CPU_seconds':210,'wall_seconds':230,'environment':{'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'},'limits':'RSS sampled, unsampled transients not excluded'},'scientific_bindings':'input-bindings.json','before_after':'before-after-hashes.json','live_primary_http':'http.jsonl','cached_prior_provenance':'frozen/provenance.json','cached_prior_chronology':'frozen/source-versions.json','own_exact_checker':'check.py','own_checker_results':'check-results.json','failures':['initial-failure.txt','check-initial-failed.py'],'procedural_exceptions':['Initial unguarded broad read-only rg discovery; truncated tool output retained in conversation.','Candidate proof read once under guard before freezing; subsequent analysis used frozen copies.'],'administrative':{'snapshot_only':True,'scientific_live_binding':False,'counts':'9 additional /39 total,next40','root_alone_accepts_counts_stages':True},'external_actions':{'git':False,'browser':False,'messages_posts_uploads':False,'MathDB_edits':False,'children':False},'manifest_exclusions':['finalmanifest.json','verification-receipt.json'],'limits':['Numerical/exact finite diagnostics are not full proof.','No broad scout or complete history/registry clearance.','Denied routes not retried.','No separately authenticated journal publication versions.']}
(O/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
exclude={'finalmanifest.json','verification-receipt.json'}
files={str(p.relative_to(O)):sha(p) for p in sorted(O.rglob('*')) if p.is_file() and str(p.relative_to(O)) not in exclude}
(O/'finalmanifest.json').write_text(json.dumps({'utc':now(),'algorithm':'SHA256','exclusions':sorted(exclude),'files':files},indent=2)+'\n')
print(json.dumps({'utc':now(),'scientific_inputs_unchanged':len(checks),'manifest_entries':len(files)}))
