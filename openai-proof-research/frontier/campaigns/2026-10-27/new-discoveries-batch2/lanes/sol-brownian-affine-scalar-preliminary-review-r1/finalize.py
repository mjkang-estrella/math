from pathlib import Path
import json, hashlib, datetime
p=Path(__file__).resolve().parent
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
def write(n,x):(p/n).write_text(json.dumps(x,indent=2)+'\n')
freeze=json.loads((p/'freeze-before.json').read_text())
comparison=[]
for r in freeze['inputs']:
    orig=Path(r['original']);copy=p/r['copy']
    comparison.append({'original':r['original'],'copy':r['copy'],
                       'expected':r['sha256'],'original_now':sha(orig),'copy_now':sha(copy),
                       'role':'administrative snapshot only' if orig.name.startswith('context-') else 'immutable review input'})
bad=[r for r in comparison if not r['expected']==r['original_now']==r['copy_now']]
write('freeze-after.json',{'utc':now(),'status':'FAIL' if bad else 'PASS','records':comparison,'failures':bad,
                         'administrative':'Live ledger/NEXT/prior context not rebound or checked as scientific dependencies.'})
assert not bad,bad
root=json.loads((p/'frozen/root-r187-handback/review-freeze.json').read_text())
root_checks=[]
for r in root['files']:
    q=Path(r['path'])
    if 'sol-fresh-source-discovery-r187' not in str(q):continue
    local=p/'frozen/sol-fresh-source-discovery-r187'/q.name
    # Root entries are paths, so preserve relative subdirectories.
    rel=str(q).split('/sol-fresh-source-discovery-r187/',1)[1]
    local=p/'frozen/sol-fresh-source-discovery-r187'/rel
    root_checks.append({'path':str(q),'expected':r['sha256'],'actual':sha(local)})
assert all(x['expected']==x['actual'] for x in root_checks)
write('root-freeze-comparison.json',{'utc':now(),'status':'PASS','records':root_checks})
worker=p/'frozen/sol-fresh-source-discovery-r187'
http=[json.loads(x) for x in (worker/'http.jsonl').read_text().splitlines()]
fresh=[json.loads(x) for x in (p/'fresh-http.jsonl').read_text().splitlines()]
sources=[]
for name in ['brownian','salminen','mayerhofer','magaldi-old']:
    for suffix in ['pdf','txt']:
        q=worker/'sources'/f'{name}.{suffix}'
        sources.append({'path':str(q.relative_to(p)),'sha256':sha(q),'bytes':q.stat().st_size,
                        'retrieval':next((x for x in http if x.get('name')==name+'.pdf'),None)})
failures=[x for x in http+fresh if 'error' in x]
write('failures.json',{'utc':now(),'inherited_and_new_retrieval_failures':failures,
 'inherited_large_access_receipt':'frozen/sol-fresh-source-discovery-r187/inherited-access.json',
 'new_checker_failures':[],'limits':['Publisher Grandits 403 not retried; body HOLD.',
 'Registry locally blocked attempt was an AssertionError, not a server response.',
 'Denied historical routes and capped intervals remain parked.',
 'Fresh Crossref query is metadata only and supplies no novelty clearance.']})
admin=[]
for q in sorted((p/'administrative').iterdir()):
    admin.append({'snapshot':str(q.relative_to(p)),'sha256':sha(q),'scientific_dependency':False})
write('provenance.json',{'utc':now(),'role':'independent preliminary review; solo',
 'counts_snapshot':{'additional':9,'total':39,'next':40},'administrative':admin,
 'source_bodies':sources,'fresh_requests':fresh,
 'source_versions':{'Dumaz-Magaldi':'2603.27602v1, submitted 2026-03-29 09:47:24 UTC; internal date 2026-03-31; current abs v1 only',
 'Salminen-Yor':'1012.2038v1, submitted 2010-12-09 15:52:37 UTC; internal date 2018-10-27; current abs v1 only',
 'Mayerhofer':'Risks 7(4)105, published 2019-10-18, actual published body in EconStor PDF',
 'Magaldi':'2411.13972v1, 2024-11-21',
 'Grandits':'Crossref online 2025-11-18, print 2026-08-09; body unread; publisher 403 HOLD'},
 'checker':{'script':'checker.py','evidence':'checker-evidence.json','symbolic_identities':9,'exact_rational_cases':125,'status':'PASS','sampled_peak_group_rss':52940800,'guard_exit':0,'guard_wall_seconds':0.28090676793362945,'limit':'algebra diagnostics only'},
 'guard':{'path':'/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',
 'sha256':'825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45',
 'AS_MiB':512,'sampled_group_RSS_MiB':512,'CPU_seconds':210,'wall_seconds':230,
 'environment':{'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'},'caps_raised':False,'sampling_limit':'Unsampled transients not ruled out'},
 'gates':{'SOURCE':'PASS scalar only','MATH':'PASS ordinary proof','SUBSTANTIVE':'recommend exclude routine classical adaptation','NOVELTY':'HOLD'},
 'scope':'Equation (6) only; no joint Conjecture 1.4 proof',
 'actions':{'children':0,'git':False,'browser':False,'messages_posts_uploads':False,'MathDB_edits':False,'Lean':False,'manuscript':False,'shared_edits':False},
 'limits':['Grandits body unread','Current registry/history incomplete','Bounded metadata screen cannot clear all history','No worldwide priority claim','No formal proof or acceptance']})
excluded=['finalmanifest.json','manifest-verification.json']
entries=[]
for q in sorted(p.rglob('*')):
    if q.is_file() and str(q.relative_to(p)) not in excluded:
        entries.append({'path':str(q.relative_to(p)),'sha256':sha(q),'bytes':q.stat().st_size})
write('finalmanifest.json',{'utc':now(),'explicit_exclusions':excluded,'reason':'Self-hash recursion and separately written verification receipt are intentionally excluded.','files':entries})
print(json.dumps({'status':'PASS','frozen_pairs':len(comparison),'root_freeze_matches':len(root_checks),'manifest_files':len(entries)}))
