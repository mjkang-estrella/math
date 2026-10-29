from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).parent;R=L.parents[5];B=L.parent.parent
def digest(p):
 h=hashlib.sha256();n=0
 with p.open('rb') as f:
  while b:=f.read(1048576):h.update(b);n+=len(b)
 return {'bytes':n,'sha256':h.hexdigest()}
contexts=[R/'AGENTS.md',B/'AGENTS.md',B/'NEXT.md',B/'ledger.json',B/'prior-campaign-context.json',R/'sources/upstream.json',R/'sources/CONTENTS.md',B/'lanes/root-edge-irregulator-final-freeze-r1/CURRENT-REGISTRIES.json',B/'lanes/sol-fresh-source-discovery-r108/refresh-http.json',B/'lanes/root-packing-uniform-exclusion-r1/EXCLUSION.json',B/'lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']
http=[json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()]
prov={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'UNRESOLVED_NO_FULL_RESULT','selected_source':{'author':'Peter V. Danchev','title':'A note on nil-clean rings','year':2020,'doi':'10.2478/ausm-2020-0020','label':'Problem 3, printed p292','quantifiers':'For every associative unital nil-clean R whose every nilpotent is a difference of two arbitrary idempotents: for every a exists k>=1,b with a^k=a^k*b*a^k; additional J(R)=0 clause asks every a exists b with a=a*b*a. Neither clause established.'},'screened_questions':['same source p292 Problem 1: bounded unit group','same source p292 Problem 2: characteristic2 p-group or 2p-group unit group','same source p292 Problem 3: arbitrary idempotent differences and regularity'],'retained_http_sources':http,'context_hashes':[{'path':str(p.relative_to(R)),**digest(p)} for p in contexts],'registry':{'freshness':'HOLD','baseline_complete_utc':'2026-10-29T18:13:38.748036+00:00','last_reported_omega_head':'89cda9c274d1122b7676173296af3047c3b64cd1','last_reported_omega_utc':'2026-10-29T20:10:57Z','last_reported_openai_head':'7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a','new_registry_HTTP_attempts':0,'reason':'No current semantic clearance; previously blocked recursive-tree/HEAD endpoints not retried; no inferred reset.'},'access_limits':['Ster2018 ScienceDirect HTTP403, no retry/alternate endpoint used','No worldwide literature-absence claim','Search snippets not treated as theorem bodies','Generated content inventories hashed but their recursive copied contents omitted','Excluded binary files and .git/node_modules/.lake/__pycache__ directories','Concurrent working tree is not an atomic filesystem snapshot','No formal proof audit; no Lean/paper investment'],'resource_guard':{'unchanged':str((B/'lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py').relative_to(R)),'AS_and_group_RSS_MiB':512,'CPU_seconds':210,'wall_seconds':230,'nominal_sample_ms':40,'BLAS_threads':1,'first_scan_failure':'SIGKILL at CPU ceiling; guard reason null; preserved without overwrite','RSS_limit':'Sampled RSS cannot exclude transient spikes'},'search_queries':['"nil-clean" "bounded" "π-regular" Danchev','"nilpotents" "differences of two idempotents" regular','"nil-clean" "p-group" "2p"','"Danchev" "nil-clean" "differences of two" "regular"','"A note on nil-clean rings" "Problem"','"nil-clean" "idempotents" site:github.com/trureturing'],'mathematical_gap':'No universal pi-regularity derivation, no global ring counterexample; symmetric-witness and bounded-index routes fail.','strongest_objection':'Positive cases routine; route obstructions are not source counterexamples.','external_actions':False,'children':False}
for name in ['screen-guard.json','screen-part2-guard.json','screen-part3-guard.json','checks-guard.json','supplement-guard.json']:
 try:prov[name]=json.loads((L/name).read_text())
 except ValueError:prov[name]={'incomplete':True}
for name in ['screen-receipt.json','screen-part2-receipt.jsonl','screen-part3-receipt.jsonl','supplement-receipt.json']:
 prov[name]=[json.loads(s) for s in (L/name).read_text().splitlines() if s.strip()]
prov['all_date_audit_summary']=json.loads((L/'audit-summary.json').read_text())
(L/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
with (L/'manifest.jsonl').open('x') as out:
 for p in sorted(L.rglob('*')):
  if not p.is_file() or p.name in ['manifest.jsonl','manifest-verification.json','finalize.log','finalize-guard.json']:continue
  out.write(json.dumps({'path':str(p.relative_to(L)),**digest(p)})+'\n')
n=0
with (L/'manifest.jsonl').open() as f:
 for s in f:
  row=json.loads(s);assert digest(L/row['path'])=={k:row[k] for k in ['bytes','sha256']};n+=1
(L/'manifest-verification.json').write_text(json.dumps({'status':'PASS','files':n,'manifest':digest(L/'manifest.jsonl'),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exclusions':['manifest itself','verification receipt itself','active finalize log and guard receipt']},indent=2)+'\n')
print(json.dumps({'status':'PASS','verified_files':n}))
