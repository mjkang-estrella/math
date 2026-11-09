import pathlib,json,hashlib,re,datetime,resource,os
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(120,120));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
L=pathlib.Path(__file__).resolve().parent;B=L.parent.parent;H=lambda p:hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
d=json.loads((L/'results.json').read_text());rs=json.loads((L/'source-receipts.json').read_text())+json.loads((L/'additional-receipts.json').read_text())
for id,names,outcome,sections,gap in [
 ('386794',['roots','mccord','cycle'],'KNOWN_COMPARISON_AND_CLASSIFICATION_BRIDGE_ORIGINAL_SCOPE_HOLD','roots sections 2.2,2.7,5 selected proofs,6; mccord Example1, Definition20, Theorems21/24 full concluding proofs; cycle section6 Propositions6.1/6.2, Corollary6.5 proofs','Original AIM convention and published/preprint correspondence remain uncleared; under restored related-primary conventions comparison plus all-parameter classification is public, not discovery.'),
 ('386886',['fs','fs-compute'],'KNOWN_INDICATOR_ROUTES_NO_NEW_GENERAL_METHOD_ORIGINAL_SCOPE_HOLD','fs section2, Definition5.1, Remark5.2, Proposition5.3 and Theorem5.5 proofs, Example5.4; fs-compute section4 equations4.1-4.8, Theorem4.1 proof','Restore original categorical hypotheses and input model; supply a genuinely new general computational theorem beyond indicator enumeration and public group-inclusion formulas.')]:
 d[id].update(new_outcome=outcome,new_primary_body_review=True,new_proof_body_review=True,new_review_scope='selected_related_primary_bodies_not_workshop_original',new_sections_read=sections,proof_dependency_audit='partial; dependencies listed in ATTEMPTS.md, not complete',remaining_lemma_or_gap=gap,attempt_report='ATTEMPTS.md',source_receipts=[x for x in rs if pathlib.Path(x['file']).stem in names])
(L/'results.json').write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
head=json.loads((L/'sources/registry-head.json').read_text());assert head['sha']=='4eaee87548250b2682affda7d05d947c05554bae'
tree=L.parent/'fresh-corpus-r10/sources/registry-preprints.json';tr=L.parent/'fresh-corpus-r10/sources/registry-preprints-receipt.json';t=json.loads(tree.read_text());rec=json.loads(tr.read_text());assert H(tree)==rec['sha256'];assert not t['truncated'];assert t['sha']=='3f56f68a176b4494c346091ea0a319651bc217ec'
terms=['Frobenius-Schur','closure-space','closure_space','roots-of-unity','clique','cyclic-graph','McCord','fusion-categor']
(L/'registry-review.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'live_head':head['sha'],'head_receipt':'source-receipts.json','reuse':{'path':str(tree),'sha256':H(tree),'receipt_path':str(tr),'receipt_sha256':H(tr),'git_tree_sha':t['sha'],'truncated':False,'entries':len(t['tree'])},'path_screen':{q:[x['path'] for x in t['tree'] if q.lower() in x['path'].lower()] for q in terms},'limits':'Bounded path screen only; repository proof bodies not searched/read. No novelty clearance. MathDB/Palomar inherited access holds respected; no requests.'},indent=2)+'\n')
refs=[B/'ledger.json',L.parent/'ledger.json',B/'prior-campaign-context.json',B/'lanes/root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',B/'lanes/root-mathdb-accepted-exclusions-r304/historical-dispositions.json',B/'lanes/root-mathdb-cayley-review-intake-r363/disposition.json',L.parent/'historical-depth-r29/environment.json']
for n in [402,404]:
 for name in ['SUMMARY.md','SOURCE-READING.md','source-reading.md','FAILURES.md','failures.json','bindings.json']:
  p=B/f'lanes/sol-mathdb-primary-qualified-breadth-r{n}'/name
  if p.exists():refs.append(p)
ctx=[]
for p in refs:
 raw=p.read_bytes();ctx.append({'path':str(p),'sha256':H(p),'bytes':len(raw),'mutable_administrative':p.name=='ledger.json'})
# Exact-ID bounded history extraction, without duplicating the history tree.
p=B/'lanes/root-mathdb-accepted-exclusions-r304/historical-dispositions.json';hist=json.loads(p.read_text());matches=[]
def walk(x):
 if isinstance(x,dict):
  if str(x.get('mathdb_id',x.get('id',''))) in d:matches.append(x)
  else:
   for v in x.values():walk(v)
 elif isinstance(x,list):
  for v in x:walk(v)
walk(hist)
(L/'context-bindings.json').write_text(json.dumps({'refs':ctx,'exact_id_history_matches':matches,'exclusion_rule':'All inherited families and protected IDs retained; no self-acceptance; administrative bindings do not certify literature clearance.'},indent=2)+'\n')
old=json.loads((L.parent/'historical-depth-r29/environment.json').read_text());binary=pathlib.Path(old['lean_binary']);assert H(binary)==old['lean_binary_sha256']
formal=B.parents[1]/'2026-10-14/formal'
# Locate the explicitly assigned read-only environment without invoking Lean.
formal=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal')
m=json.loads((formal/'lake-manifest.json').read_text());rev=next(x['rev'] for x in m['packages'] if x['name']=='mathlib');assert rev==old['mathlib_revision_user_pin']
(L/'environment.json').write_text(json.dumps(old|{'lean_binary_sha256_actual':H(binary),'unchanged_version_receipt':str(L.parent/'historical-depth-r29/environment.json'),'receipt_sha256':H(L.parent/'historical-depth-r29/environment.json'),'lean_toolchain':(formal/'lean-toolchain').read_text(),'toolchain_sha256':H(formal/'lean-toolchain'),'lake_manifest_path':str(formal/'lake-manifest.json'),'lake_manifest_sha256':H(formal/'lake-manifest.json'),'actual_mathlib_revision':rev,'resource_policy':'Python/network helpers: affinity <=2 CPUs; AS 1GiB, CPU 100-120s, outer wall 120-170s; HTTP 25s, 20MiB per response, pdftotext 30s. No enumeration, compile, background jobs, or dependency mutation.'},indent=2)+'\n')
print('Finalized exactly',len(d),'rows; related primary/proof reads',sum(x['new_primary_body_review'] for x in d.values()),'; zero credit.')
