import pathlib,json,hashlib,datetime,shutil
out=pathlib.Path(__file__).resolve().parent;batch=out.parent.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
freeze=batch/'lanes/root-lasso-review-freeze-r1/review-freeze.json'
f=json.loads(freeze.read_text());src=pathlib.Path(f['source_lane'])
checks={n:{'expected':h,'original':sha(src/n),'copy':sha(out/'candidate-copy'/n)} for n,h in f['files'].items()}
assert len(checks)==49 and all(v['expected']==v['original']==v['copy'] for v in checks.values())
(out/'after.json').write_text(json.dumps({'utc':now(),'all_49_originals_and_copies_match':True,'files':checks},indent=2))
pre=out.parent/'sol-lasso-max-preliminary-review-r1'
for n in ['comparison-arxiv.pdf','comparison-arxiv.txt','http-provenance.json']:
 shutil.copyfile(pre/n,out/'preliminary-evidence'/n)
ledger=batch/'ledger.json';j=json.loads(ledger.read_text())
(out/'final-context.json').write_text(json.dumps({'utc':now(),'ledger_sha256':sha(ledger),'accepted_count':j['accepted_count'],'total_accepted_count':j['total_accepted_count'],'candidate_credit':0,'reviewer_changed_ledger':False},indent=2))
sources=json.loads((out/'candidate-copy/provenance.json').read_text())['sources']
for s in sources:
 s['evidence_file']='candidate-copy/'+s.pop('file')
 s['hash_verified']=sha(out/s['evidence_file'])==s['sha256']
extra=[{'url':'https://arxiv.org/pdf/2311.12685v1','publication_date':'2023-11-21','file':'preliminary-evidence/comparison-arxiv.pdf','sha256':sha(out/'preliminary-evidence/comparison-arxiv.pdf'),'status':'actual cached preprint; Sections 3.2 and 4.2 read, no published-version clearance'},
 {'url':'https://academic.oup.com/jrsssb/article/87/5/1457/8139083','doi':'10.1093/jrsssb/qkaf026','revision_received_date':'2025-04-23','accepted_date':'2025-04-26','advance_publication_date':'2025-05-20','issue_date':'2025-11','status':'indexed partial primary text only; no complete equation-faithful VoR; existing challenge not retried'},
 {'url':'https://repository.lib.ncsu.edu/bitstreams/bda92a35-7e64-4c59-8ceb-da4a9f33c1a3/download','publication_year':2023,'title':'Optimal Design and Analysis Approaches for Supersaturated Screening with the Lasso','author':'Herschel Kade Young','status':'indexed primary title-page year; actual full body unavailable, challenged endpoint not retried'},
 {'url':'https://scholarlycommons.henryford.com/publichealthsciences_articles/610/','doi':'10.1080/00949655.2025.2474635','publication_date':'2025-03-25','journal':'J Stat Comput Simul 95(9):1928-1943','status':'primary indexed bibliographic record; distinct SSD/OA comparison full body unavailable'}]
for x in extra:x['review_observation_date']='2026-10-29'
prov={'utc':now(),'verdict':'HOLD; recommend exclusion of current source-discovery nomination; preserve math','candidate_credit':0,
 'mandatory_report':'review.md','freeze':{'file':str(freeze),'sha256':sha(freeze),'files':49,'before':'before.json','after':'after.json','originals_and_copies_unchanged':True},
 'sources':sources,'additional_sources':extra,
 'prior_review':{'path':str(pre/'review.md'),'sha256':sha(pre/'review.md'),'read_full':True,'evidence':'preliminary-evidence/'},
 'search_evidence':{'file':'search-evidence.json','sha256':sha(out/'search-evidence.json'),'date':'2026-10-29','limits':'Indexed excerpts, missing equations/sections, not complete source bodies. Search engine recency not publication chronology.'},
 'registries':json.loads((out/'registry-screen.json').read_text()),
 'actual_registry_bodies':json.loads((out/'registry-bodies-provenance.json').read_text())+json.loads((out/'registry-more-bodies-provenance.json').read_text()),
 'resources':{'address_space_bytes':536870912,'group_rss_bytes':536870912,'group_cpu_seconds':210,'wall_seconds':230,'sampling_ms':40,'blas_threads':1,'guard':'helper_guard.py','guard_matches_r70':sha(out/'helper_guard.py')==sha(out.parent/'sol-fresh-source-discovery-r70/capped_run.py'),'caps_raised':False},
 'access_limits':['Recorded publisher challenge, watermark failure, dissertation verification HTML and author comparison HTML preserved; no repeated direct requests','No browser/account/proxy/token bypass/contact/external writes','No full VoR, dissertation or distinct SSD/OA comparison acquired','No complete semantic registry audit or universal priority conclusion','Historical behind API response not treated as current absence'],
 'substantive_adjudication':{'bridge':'Lemma2 p3 k2 mixed signs, full-matrix boundary -1/2, zero inactive mean and vanishing Schur variance, uniform density-envelope cubic maximum','countercase':'Does exceed every orthogonal tuning, unlike source fixed-lambda failures; no identical printed theorem claimed','recommendation':'Routine-bridge objection sustained at campaign threshold; no investment without bona fide attributable full question; root decides'},
 'actions':{'solo':True,'children':False,'git':False,'shared_or_other_lane_writes':False,'browser':False,'account':False,'contact':False,'posting':False,'upload':False,'lean':False,'paper':False,'count_changes':False}}
(out/'provenance.json').write_text(json.dumps(prov,indent=2))
manifest={str(p.relative_to(out)):sha(p) for p in out.rglob('*') if p.is_file() and p.name not in ['ARTIFACT-HASHES.json','finalize-guard.json','finalize.log']}
(out/'ARTIFACT-HASHES.json').write_text(json.dumps(manifest,indent=2))
print('PASS: 49 originals and 49 copies unchanged; provenance and artifact hashes written; root ledger observed at',j['total_accepted_count'],'candidate credit 0')
