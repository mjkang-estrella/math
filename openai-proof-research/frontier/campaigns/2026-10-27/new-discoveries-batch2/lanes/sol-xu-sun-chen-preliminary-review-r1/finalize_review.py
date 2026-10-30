"""Recheck frozen originals/copies, record provenance, and hash final lane files.
Run only through the unchanged designated helper_guard.py.
"""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json
L=Path(__file__).resolve().parent
B=L.parent.parent
def now(): return datetime.now(timezone.utc).isoformat()
def digest(data): return hashlib.sha256(data).hexdigest()
def save(name,data): (L/name).write_text(json.dumps(data,indent=2)+'\n')
freeze=B/'lanes/root-r160-preliminary-freeze-r1/review-freeze.json'
raw=freeze.read_bytes()
assert raw==(L/'review-freeze.json').read_bytes()
before=json.loads((L/'frozen-before.json').read_text())
assert digest(raw)==before['freeze_sha256']
m=json.loads(raw); rows=[]
for a in m['files']:
    p=Path(a['path']); q=L/'frozen'/p.relative_to(m['root'])
    u=p.read_bytes(); v=q.read_bytes()
    assert len(u)==len(v)==a['bytes'] and digest(u)==digest(v)==a['sha256']
    rows.append({'original':str(p),'copy':str(q),'bytes':len(u),'sha256':digest(u),'identical':True})
assert len(rows)==28
guard=B/'lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
gh=digest(guard.read_bytes())
assert gh=='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45'
save('frozen-after.json',{'utc':now(),'freeze_sha256':digest(raw),'originals_and_copies_verified':28,'all_pass':True,'files':rows})
root=B.parents[3]
context=[root/'AGENTS.md',B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B/'NEXT.md']
assert all(p.exists() for p in context)
result=json.loads((L/'independent-results.json').read_text())
assert result['status']=='PASS' and result['minimum']==584325
save('provenance.json',{
 'utc_finalized':now(),'role':'solo independent adversarial preliminary review; parent alone adjudicates',
 'lane':str(L),'frozen_root':m['root'],'freeze_path':str(freeze),'freeze_sha256':digest(raw),
 'counts':{'additional':9,'total':39,'next':40,'mutated':False},
 'verdicts':{'source':'PASS','math':'PASS with corrected prose minimum','substantive':'FAIL: routine source-method adaptation','novelty':'HOLD: bounded evidence, no global clearance','formal_feasibility':'plausible, not validated; no Lean run'},
 'guard':{'path':str(guard),'sha256':gh,'AS_MiB':512,'sampled_group_RSS_MiB':512,'CPU_s':210,'wall_s':230,'nominal_sampling_ms':40,'caps_raised':False,'sampling_limit':'between-sample spikes cannot be excluded'},
 'environment':{'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'},
 'reproduce':['OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python '+str(guard)+' python '+str(L/'independent_checks.py'),'OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python '+str(guard)+' python '+str(L/'finalize_review.py')],
 'rules_and_context_read':[{'path':str(p),'sha256':digest(p.read_bytes())} for p in context],
 'independent_method':'General rational family derivative; dense exact arithmetic; monic synthetic divisions; exact source cubic control; full written calculus; visual source inspection',
 'root_receipts_used_as_validation':False,'candidate_script_executed':False,
 'live_source_receipt':'live-source-receipt.json','source_images':['journal-page-88.png','journal-page-89.png','journal-page-93.png','journal-page-94.png'],
 'bounded_prior_coverage':{'fresh':'journal PDF only','inherited_registry_heads':{'omega':'b62773edfb6a6f7806de09b593b2e3b6834685c7','openai':'4eaee87548250b2682affda7d05d947c05554bae'},'gaps':['aa026->a19a and a19a->490f older intervals capped at 300 paths','lexical screens are not semantic clearance','no exhaustive specialist literature audit'],'earlier_exact_public_proof_claimed':False},
 'failures':'failures.json','protocol_deviations':[],
 'restrictions_observed':['writes only assigned lane','no git','no shared/candidate mutations','no counts change','no external messages/uploads','no browser tabs','no children','no Lean/manuscript investment']})
files=[]
for p in sorted(L.rglob('*')):
    if p.is_file() and p.name!='final-hashes.json':
        d=p.read_bytes();files.append({'path':str(p.relative_to(L)),'bytes':len(d),'sha256':digest(d)})
save('final-hashes.json',{'utc':now(),'excludes':'final-hashes.json itself only (no circular hash)','files':files})
print(json.dumps({'utc':now(),'frozen_files':28,'lane_files_hashed':len(files),'guard_sha256':gh,'review_sha256':digest((L/'review.md').read_bytes()),'all_pass':True}))
