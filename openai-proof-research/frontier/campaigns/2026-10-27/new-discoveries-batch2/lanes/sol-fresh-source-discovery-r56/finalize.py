import pathlib,json,datetime,hashlib
P=pathlib.Path(__file__).resolve().parent
heads={}
for n in ['omega','omega-main','openai','aim','count']:
 d=json.loads((P/'sources'/f'{n}-head.json').read_text());heads[n]={'sha':d['sha'],'commit_utc':d['commit']['committer']['date'],'api_url':d['url']}
files={}
for f in sorted(P.rglob('*')):
 if not f.is_file() or '__pycache__' in f.parts:continue
 rel=str(f.relative_to(P))
 if rel in ['provenance.json','verify.log','verify-guard.json']:continue
 b=f.read_bytes();files[rel]={'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
d={'lane':str(P),'final_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'unresolved','candidate_count':1,'credit':0,'counts_unchanged':{'additional':6,'total':36},'nomination':False,'PROOF_md':False,'source':'TheoremDB P2806, original CC0 prospecting question; not an expert conjecture in cited process paper','source_qualification':'HOLD','source_statement_fingerprint_advertised':'c6d9e2373db08e9d7dafe73158015888ee04f0d96c9254b4b1952569ca4e89a2','heads':heads,'http_events':'http.jsonl','access_failures':[],'coverage_limits':['No whole Omega dev coverage','Complete D5 and Problems reused from refreshed r54 snapshots with verified 3commit/1documentationfile delta','Other cached scopes verified by unchanged heads','Lexical tree and bounded search checks do not imply exhaustive semantic clearance','Registry original question lacks established named expert/journal provenance'],'searches':[{'utc_date':'2026-10-29','query':q} for q in ['"bootstrap" "spanning" "log-concavity"','"bootstrap percolation" "matroid"','"bootstrap-grid-spanning-count-log-concavity"']],'resource_policy':{'AS_bytes':512*1024*1024,'CPU_seconds':210,'wall_seconds':230,'process_group_sampled_RSS_bytes':512*1024*1024,'BLAS_threads':1},'remaining_gap':'Uniform balanced proper-coloring inequality for every fort-projected intersection/union slice, or a different full-grid proof/certified source counterexample. Strip transfer alone does not suffice.','files':files}
(P/'provenance.json').write_text(json.dumps(d,indent=2)+'\n')
print(d['final_utc'],len(files),'hashed artifacts')
