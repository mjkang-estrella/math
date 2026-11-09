from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
bindings=json.loads((L/'bindings.json').read_text())['items']+json.loads((L/'history-bindings.json').read_text())
checks=[]
for b in bindings:
 r={'original':b['original'],'copy':b['copy'],'sha256':b['sha256'],'copy_matches':sha(L/b['copy'])==b['sha256']}
 if b['category']=='frozen':r['original_matches']=sha(Path(b['original']))==b['sha256']
 checks.append(r)
assert all(r['copy_matches'] and r.get('original_matches',True) for r in checks)
access=[]
for line in (L/'access.jsonl').read_text().splitlines():
 r=json.loads(line)
 if 'sha256' in r:assert sha(L/(r['label']+'.body'))==r['sha256']
 access.append(r)
(L/'source-postcheck.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'checks':checks,'access_bodies_checked':len(access),'status':'PASS'},indent=2))
ledger=json.loads((L/'admin/new-discoveries-batch2/ledger.json').read_text());prior=json.loads((L/'admin/new-discoveries-batch2/prior-campaign-context.json').read_text())
assert [ledger[k] for k in ['accepted_count','total_accepted_count','next_global_outcome_number']]==[9,39,40]
(L/'administrative-read.json').write_text(json.dumps({'counts':[9,39,40],'ledger_keys':list(ledger),'prior_context_keys':list(prior),'mode':'snapshot only; no live-admin postcondition'},indent=2))
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
(L/'provenance.json').write_text(json.dumps({'lane':str(L),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'guard':str(guard),'guard_sha256':sha(guard),'caps':{'AS_bytes':512*1024**2,'group_RSS_bytes':512*1024**2,'CPU_seconds':210,'wall_seconds':230},'environment':{'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'},'scientific_binding':'bindings.json and history-bindings.json; source-postcheck.json','main_primary_url':'https://arxiv.org/pdf/1909.01306v1','primary_posted':'2019-09-03T16:57:56Z','published_primary_page':'https://link.springer.com/chapter/10.1007/978-3-030-67996-5_19','published_first_online':'2021-08-12','published_full_body_read':False,'current_registry_head':None,'bounded_novelty_clearance':False,'inherited_receipts':'frozen/sol-wide-cross-family-mechanisms-r263/retrieval.jsonl and bindings.jsonl; references reused, no recursive history copying','credit_requested':0,'no_shared_mutations':True},indent=2))
exclude={'final-manifest.json','verification-receipt.json'}
files=[p for p in L.rglob('*') if p.is_file() and p.name not in exclude]
(L/'final-manifest.json').write_text(json.dumps({'files':[{'path':str(p.relative_to(L)),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(files)],'excludes':sorted(exclude)},indent=2))
print('Source postcheck PASS; manifest written',len(files))
