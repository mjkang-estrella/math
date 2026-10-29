from pathlib import Path
import json,hashlib,datetime,re
P=Path(__file__).resolve().parent; B=P.parent.parent; S=P.parent/'sol-fresh-source-discovery-r79'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
f=json.loads((P.parent/'root-lasso-review-freeze-r1/review-freeze.json').read_text())
for n,h in f['files'].items():
 assert sha(S/n)==h,n
 assert sha(P/'candidate-copy'/n)==h,n
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
(P/'after.json').write_text(json.dumps({'utc':now,'original_count':len(f['files']),'all_original_and_copy_hashes_match':True,'freeze_sha256':sha(P.parent/'root-lasso-review-freeze-r1/review-freeze.json')},indent=2))
rx=re.compile(r'2303[._-]?16843|stallrich|lassosign|lasso.sign.recover',re.I)
registry={}
for repo in ['omega','openai']:
 p=P.parent/'root-edge-irregulator-current-prior-r1'/(repo+'-tree.txt')
 hits=[l for l in p.read_text().splitlines() if rx.search(l)]
 registry[repo]={'input':str(p),'sha256':sha(p),'regex':rx.pattern,'hits':hits,'scope':'Dated filename screen only; not semantic/body absence'}
(P/'registry-screen.json').write_text(json.dumps(registry,indent=2))
http=json.loads((P/'http-provenance.json').read_text())
for r in http:
 if r['name'].endswith('delta'):
  d=json.loads((P/(r['name']+'.body')).read_text());r.update(comparison_status=d['status'],ahead_by=d['ahead_by'],behind_by=d['behind_by'],permalink_url=d['permalink_url'])
provenance={
 'utc':now,'verdict':'HOLD','credit':0,'counts_unchanged':[7,37],
 'input_freeze':{'path':str(P.parent/'root-lasso-review-freeze-r1/review-freeze.json'),'sha256':sha(P.parent/'root-lasso-review-freeze-r1/review-freeze.json'),'before':'before.json','after':'after.json','own_copy':'candidate-copy','files':49},
 'primary_preprint':{'url':'https://arxiv.org/pdf/2303.16843','file':'candidate-copy/lasso.pdf','sha256':sha(P/'candidate-copy/lasso.pdf'),'version':'v3 2025-04-24','read':'actual frozen text model/KKT/Sections2.2,3,3.2/Lemma2/supplement independence'},
 'new_actual_body':{'url':'https://arxiv.org/pdf/2311.12685v1','file':'comparison-arxiv.pdf','sha256':sha(P/'comparison-arxiv.pdf'),'observed_utc':datetime.datetime.fromtimestamp((P/'comparison-arxiv.pdf').stat().st_mtime,datetime.timezone.utc).isoformat(),'headers':'comparison-arxiv.headers','status':'HTTP200 actual PDF, relevant Sections1,3.2,4.2,5 read; not distinct SSD/OA comparison or published-version clearance'},
 'http_observations':http,
 'blocked_prior_routes':json.loads((P/'candidate-copy/provenance.json').read_text())['failed_probes'],
 'access_policy':'Prior challenged publisher/watermark/thesis endpoints not retried; no proxies, challenge solving, browser, accounts or external mutations. Author base page returned generic Miami site HTML, not actual paper.',
 'author_page':{'url':'https://sites.miamioh.edu/byran-smucker/','file':'author.html','sha256':sha(P/'author.html'),'headers':'author.headers','observed_utc':datetime.datetime.fromtimestamp((P/'author.html').stat().st_mtime,datetime.timezone.utc).isoformat()},
 'web_searches':{'utc_date':'2026-10-29','queries':['"qkaf026" pdf','"Kade Young" "lasso" thesis 2025','"SSDs_vs__OAs" Smucker','"A Comparison of Supersaturated Designs and Orthogonal Arrays" pdf','"Optimal Design and Analysis Approaches" pdf -site:repository.lib.ncsu.edu','"lasso" "sign recovery" "orthogonal" "counterexample" maximum design','"Stallrich" "orthogonal" "conjecture" lasso maximum','"An optimal design framework for lasso sign recovery" filetype:pdf -site:watermark02.silverchair.com -site:arxiv.org -site:academic.oup.com -site:0-academic-oup-com.legcat.gov.ns.ca'], 'body_hashes':None,'limitation':'Search snippets not substituted for target/closest bodies; results not independently byte-frozen'},
 'other_web_reads':[{'url':'https://jonstallrich.com/research/','status':'web tool inaccessible; not retried'},{'url':'https://sites.miamioh.edu/byran-smucker/research/','status':'web tool inaccessible; not retried'},{'url':'https://jonstallrich.com/','status':'public landing page only'},{'url':'https://statistics.sciences.ncsu.edu/2023/12/08/its-a-celebration-fall-2023-commencement/','status':'primary search evidence for2023 dissertation chronology; no dissertation body'}],
 'checker':{'script':'checker.py','result':'checker-results.json','guard':'checker-guard.json','status':'PASS finite rational checks only','not_formal':True,'failures_or_corrections':['No checker arithmetic failure. Worker tautological cubic check preserved, independently replaced by derivative/four-point checks.','HTTP helper initially summarized Omega total_commits0 without status. Actual behind/70673 relation explicitly corrected; no freshness clearance.','2025 thesis label corrected to2023 on primary chronology evidence, body still HOLD.']},
 'resources':{'copied_from':str(P.parent/'sol-fresh-source-discovery-r70/capped_run.py'),'wrapper_sha256':sha(P/'capped_run.py'),'AS_bytes':536870912,'group_RSS_bytes':536870912,'CPU_seconds':210,'wall_seconds':230,'sample_ms':40,'BLAS_threads':1,'limitation':'RSS sampled, unsampled transients not excluded'},
 'actions':{'solo':True,'children':False,'git':False,'shared_writes':False,'browser':False,'external_writes':False},
 'registry_screen':'registry-screen.json','current_omega_limit':'Observed API main is behind supplied snapshot, not a complete current forward delta; 17:56 head75fa71fb not audited',
}
(P/'provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
files={str(p.relative_to(P)):sha(p) for p in sorted(P.rglob('*')) if p.is_file() and p.name not in ['artifact-hashes.json','seal.log','seal-guard.json']}
(P/'artifact-hashes.json').write_text(json.dumps(files,indent=2)+'\n')
print(json.dumps({'status':'sealed','freeze_files':49,'after_unchanged':True,'registry_matches':{k:len(v['hits']) for k,v in registry.items()}}))
