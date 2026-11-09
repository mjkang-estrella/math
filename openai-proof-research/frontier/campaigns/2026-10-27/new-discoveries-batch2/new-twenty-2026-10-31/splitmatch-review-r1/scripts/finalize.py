from pathlib import Path
import json,hashlib,datetime
L=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/splitmatch-review-r1')
assert (L/'inputs-before.sha256').read_bytes()==(L/'inputs-after.sha256').read_bytes()
assert not (L/'logs/endpoint-spec.log').read_text().strip()
assert (L/'logs/replay-driver.exit').read_text().strip() == '0'
r={
 'mathdb_id':381751,'role':'independent adversarial reviewer','recommendation':'EXCLUDE','discovery_credit':0,'root_acceptance':False,
 'reason':'Exact witness is obtained from four source K4 blocks by two colour-preserving 2-switches; a short parity argument retains the all-odd obstruction. This meets the binding short-augmentation exclusion precedent.',
 'gates':{
  'A':{'verdict':'PASS','reason':'Published Conjecture 3 and arXiv v2 Conjecture 1.3 match the literal MathDB statement. Existential non-K4 component; disjoint perfect matchings; sum n-1. Absent in v1, whose conjectures are bipartite.'},
  'B':{'verdict':'PASS','reason':'Own spectrum enumeration and all 25088 prescribed-count selections agree; no witness. Complete ordinary parity proof; full fixed-A checks through order 8 and 30 random triples each at 10,12,14.'},
  'C':{'verdict':'QUALIFIED_PASS','reason':'Strict extracted compile and explicit-module checker pass, 69 declarations audited. General endpoint specification compiles, but literal general negation and graph-matching/selector, component-isomorphism, relabelling bridges remain unproved.'},
  'D':{'verdict':'FAIL','reason':'Bounded live search located no exact prior refutation; relevant author thesis body unread, so material prior-art clearance is incomplete.'},
  'E':{'verdict':'FAIL','reason':'Short augmentation of the source K4 family: delete C edges 13,46 and insert 14,36 in each pair; source all-odd tuple unchanged.'}},
 'literal_lean_endpoint':{'name':'SplitMatchingLiteral.not_Conjecture3','type':'¬ SplitMatchingLiteral.Conjecture3','specification':'build/EndpointSpec.lean','specification_strict_compile_exit_code':0,'theorem_proved':False,'current_fixed_endpoint':'SplitMatching381751.literal_counterexample'},
 'checks':{'prepare_exit_code':0,'mathcheck_exit_code':0,'strict_splitmatching_exit_code':0,'strict_audit_exit_code':0,'explicit_module_leanchecker_exit_code':0,'leanchecker_module':'SplitMatching','audit_declarations':69,'allowed_axioms':['propext','Classical.choice','Quot.sound'],'original_chunk_line_785_verified':True,'candidate_inputs_unchanged':True},
 'input_hashes':{'before':'inputs-before.sha256','after':'inputs-after.sha256','manifest_sha256':hashlib.sha256((L/'inputs-before.sha256').read_bytes()).hexdigest(),'packet_sha256':'26696a02df86785f733fc4242447abdd1b2206aeff0f8300183c14d84d132ca5','raw_sha256':'4c8663f7a856dca56d8f0dd56d64f27f0b2990fcc5038627aa6f5118b6ace35f'},
 'prior_art':{'date':'2026-11-04','pool_head':'01db1d7049cf9668bda1e9e106875ee1278b43e6','pool_candidate_blobs':10,'github_repository_queries':3,'github_results':[0,0,0],'published_openalex_id':'W4385357696','published_citing_works':1,'separate_arxiv_record_found':False,'thesis_fulltext_read':False,'novelty_certified':False},
 'missing_evidence':['Full legitimate inspection of Fabian thesis Chapter 5 and relevant surrounding remarks for prior-art clearance.','If root overrides substantive exclusion: proof of the specified literal general negation, including all selector/matching, count, component and relabelling bridges.'],
 'process':{'limits_wrapper':'scripts/cap.sh','python_isolated':True,'cpu_affinity_count':2,'cpu_seconds':120,'wall_seconds':140,'rss_watchdog_gib':6,'MALLOC_ARENA_MAX':2,'lean_memory_flag':'-M3500','heavy_jobs_serialized':True,'background_jobs_remaining':False,'tls_verification_disabled':False,'access_deviation':'DNB alternative-route attempt followed redirect to institutional record after web fetch of that record returned 429; it returned a bot challenge. No challenge was solved or bypassed and no further request made.'},
 'artifacts':{'review':'REVIEW.md','math':'mathcheck.json','scripts':'scripts/','replay_driver':'scripts/replay.sh','logs':'logs/','download_receipts':'downloads/*/receipt.json','web_log':'web-search-notes.md'}}
r['checks']['offline_replay_driver_exit_code'] = 0
r['checks']['replay_logs'] = 'logs/replay-*.log'
r['input_hashes']['manifest_entries'] = 111
r['input_hashes']['dependency_hashes'] = 'dependencies.sha256'
p = L/'downloads/thesis-dnb/receipt.json'
x = json.loads(p.read_text()); x['challenge'] = True; x['challenge_detection'] = 'HTML title and anubis_challenge marker'; p.write_text(json.dumps(x,indent=2)+'\n')
(L/'review.json').write_text(json.dumps(r,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'recommendation':r['recommendation'],'gates':{k:v['verdict'] for k,v in r['gates'].items()},'manifest_sha256':r['input_hashes']['manifest_sha256']},indent=2))
