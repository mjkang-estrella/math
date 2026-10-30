import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent
G=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def record(p):return {'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)}
support=[]
for p in [G,L.parent/'root-clique-corona-preliminary-adoption-r1/review-freeze.json',L.parent/'root-r168-preliminary-freeze-r1/review-freeze.json',L.parent/'sol-steiner-gp-offline-citation-closure-r4/review.md',L.parent.parent/'ledger.json',L.parent.parent/'prior-campaign-context.json',L.parent.parent/'NEXT.md']:
 b=p.read_bytes();digest=sha(p);matches=list((L/'frozen').glob(digest+'-*'))
 q=matches[0] if matches else L/'frozen'/(digest+'-'+p.name)
 if not matches:q.write_bytes(b)
 support.append(dict(record(p),copy=str(q)))
frozen=json.loads((L/'before-freeze.json').read_text())
for e in frozen['files']+support:
 for p in [pathlib.Path(e['path']),pathlib.Path(e['copy'])]:assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256'],str(p)
(L/'after-freeze.json').write_text(json.dumps({'utc':now(),'status':'PASS','frozen_records':len(frozen['files']),'support':support,'unique_frozen_copies':len(set(x['copy'] for x in frozen['files']))},indent=2)+'\n')
access=[json.loads(x) for x in (L/'access.jsonl').read_text().splitlines()]
for e in access:assert sha(L/'retrieved'/e['name'])==e['sha256']
delta=json.loads((L/'retrieved/omega-fixed-delta.json').read_text())
coverage=json.loads((L/'registry-coverage.json').read_text())
assert delta['base_commit']['sha']==coverage['base'] and delta['merge_base_commit']['sha']==coverage['base']
assert delta['total_commits']==len(delta['commits'])==22
assert delta['commits'][-1]['sha']==coverage['head']
assert len(delta['files'])==11 and all('patch' in f for f in delta['files'])
checks={'utc':now(),'status':'PASS','frozen_records_verified':len(frozen['files']),'unique_payload_copies':len(set(x['copy'] for x in frozen['files'])),'support_records':len(support),'access_receipts_verified':len(access),'delta_files':11,'delta_commits':22,'delta_complete_as_saved_fixed_comparison':True,'new_2016_body_pages_read':0,'eligibility':'HOLD','no_math_reaudit':True}
(L/'checks.json').write_text(json.dumps(checks,indent=2)+'\n')
provenance={'utc':now(),'guard':record(G),'limits':{'AS_bytes':536870912,'group_RSS_bytes':536870912,'CPU_seconds':210,'wall_seconds':230},'environment':{'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'},'access':access,'scientific_body_coverage':{'2016_DOI_10.1016/j.dam.2015.09.021':'NO BODY OBTAINED; zero pages; institutional metadata and abstract read only','2017_survey':'Inherited completed full-body reading; saved reference24 read to identify exact 2016 title/authors; no substitute claim','candidate_and_completed_review':'Read; inherited source/math PASS; no new mathematical review','generic_2006_published_successor':'Not newly retrieved/read; no exclusion claimed and no necessity shown for expanding scope'},'registry':coverage,'failures':['Native initial inventory and combined reads were overbroad/truncated; no helper/hash/retrieval/math ran outside guard. Later decisive identity and access excerpts separately read.','A mistaken native survey path under sources/ produced exact rg IO error (os error 2); actual survey.txt read at lane root.','DuckDuckGo HTTP202 human challenge; response retained and no retry or challenge interaction.','All three Bing responses were irrelevant first-token results (On, independence, 10); no negative literature inference.','2016 body acquisition failed; institutional page supplies metadata only.','Earlier exact ScienceDirect HTTP Error 403: Forbidden and GitHub API403 preserved within frozen predecessor provenance; not retried.'],'boundary':'No GitHub/ScienceDirect/Google request, browser, public mutation, git operation, formal work, child agent, ledger/count or other-lane write.'}
(L/'provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
exclude={'final-verified-manifest.json','manifest-verification.json','close.log','verifier.log'}
files=[dict(record(p),path=str(p.relative_to(L))) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in exclude]
(L/'final-verified-manifest.json').write_text(json.dumps({'utc':now(),'files':files,'exclusions':sorted(exclude),'note':'No self hash; verification receipt separately binds this manifest. Logs are mutable replay outputs.'},indent=2)+'\n')
print(json.dumps(checks))
