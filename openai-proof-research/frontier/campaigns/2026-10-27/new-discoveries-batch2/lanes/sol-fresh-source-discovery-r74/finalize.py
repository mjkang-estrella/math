import pathlib,json,hashlib,datetime,platform
import numpy,scipy,sympy
L=pathlib.Path(__file__).resolve().parent
http=[]
for name in ['http.json','http-more.json','http-final.json']:http.extend(json.loads((L/name).read_text()))
files=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name!='provenance.json':
  b=p.read_bytes();files.append({'path':str(p.relative_to(L)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
for name in ['replay-exact-guard.json','replay-airy-guard.json','collect-guard.json','fetch-more-guard.json','final-sources-guard.json']:
 j=json.loads((L/name).read_text());assert j['guard_exit']==0 and j['reason'] is None
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'lane':L.name,'status':'unresolved; not nominated','credit':0,'counts_untouched':{'additional':7,'total':37},'target':'Balabdaoui-Wellner Bernoulli20(1)(2014) Conjecture3.1 pp239-240, full sharp constant w(x)>=w(0) all real x','expert_attribution':'Actual published paper by Fadoua Balabdaoui and Jon A. Wellner','public_counterpart':{'arxiv':'2607.18619v1','submitted_utc':'2026-07-21T01:39:27Z','actual_scope':'v>0,v>=4x,w>4|x|,inf w>0; no sharp-center inequality proved in inspected body','body_versions':'PDF22Jul2026; HTML24Aug2026 under same v1; both saved'},'registry':{'freshness':'HOLD','api_calls':0,'inherited_hold':'sharedGitHubAPI403/429; no retry or bypass','latest_observed_omega':'6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3','observation_utc':'2026-10-29T15:49:00Z (inherited minute precision)','current_HEAD':'unknown','blueprint_snapshot':'3b4135a35caa0ae817cf5eca51d605b098027fd2','actual_matched_lean':'sources/registry-chernoff.lean','scope_limit':'Dated named trees plus live readmes and bounded primary searches do not establish current full registry absence'},'versions':{'python':platform.python_version(),'numpy':numpy.__version__,'scipy':scipy.__version__,'sympy':sympy.__version__},'guard':{'AS_bytes':512*1024**2,'groupRSS_bytes':512*1024**2,'CPU_seconds':210,'wall_seconds':230,'sample_ms':40,'BLAS_threads':1,'source':'copied r72 capped_run.py'},'http_reads':http,'web_reads':'sources/web-reading-receipt.md','context':'context-reading.json','exact_checks':'exact-checks.json','floating_only':'airy-diagnostics.json','remaining_gap':'Full compact inequality N(x)>=0 for0<=x<=w(0)/4, or an admissible certified negative Airy witness; no complete proof. Eligibility and priority alsoHOLD.','manifest':files}
(L/'provenance.json').write_text(json.dumps(out,indent=2))
print(json.dumps({'files':len(files),'status':out['status'],'credit':0}))
