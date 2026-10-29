import pathlib,hashlib,json,datetime
P=pathlib.Path(__file__).resolve().parent
B=P.parents[1]; R=B.parents[3]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
inputs=[B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B/'NEXT.md',R/'AGENTS.md',R/'sources/upstream.json',R/'sources/CONTENTS.md',B/'lanes/root-polyomino57-acceptance-r1/ACCEPTANCE-PRIOR-LIMITS.json']
inputs += [B/('lanes/sol-fresh-source-discovery-r'+str(n)+'/SUMMARY.md') for n in range(60,67)]
assert all(p.exists() for p in inputs),[(str(p),p.exists()) for p in inputs]
context=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in inputs]
registry=[]
for rel in ['lanes/sol-polyomino57-source-prior-refresh-r3/live/omega-Problems.json','lanes/sol-jacobi-full-final-review-r1/evidence/omega-D5-tree.json']:
 p=B/rel;v=json.loads(p.read_text()); paths=[e['path'] for e in v.get('tree',[]) if any(t in e['path'].lower() for t in ['heim','neuhauser','plane','partition','arcais','sun'])]
 registry.append(dict(path=rel,sha256=sha(p),tree_sha=v.get('sha'),truncated=v.get('truncated'),kind='actual Lean D5' if 'D5-tree' in rel else 'Problems dossiers',matched_paths=paths))
r=json.loads((P/'routes.json').read_text());i=json.loads((P/'independent.json').read_text());a=json.loads((P/'abel.json').read_text());k=json.loads((P/'kernel.json').read_text())
assert all(not t['negative_shift1'] for t in r['derivative'])
assert all(not t['neg'] for t in r['base_delta'])
assert all(not t['negative_suffix_indices'] for t in a['rows'])
assert len(r['derivative'])==100 and i['exact_source_inequalities']==970 and k['identity_checks']==80
for p in P.glob('logs/*-guard.json'):
 if p.name=='finalize-guard.json' or not p.stat().st_size:continue
 assert json.loads(p.read_text())['guard_exit']==0,p
obj=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),lane=P.name,status='UNRESOLVED',discovery_credit=0,campaign_counts=dict(additional=7,total=37),source_target=dict(authors=['Bernhard Heim','Markus Neuhauser'],arxiv='2601.11226v1',latest_history_seen='v1 only, January16 2026',published='Ramanujan Journal70(2026)58, July15 2026',doi='10.1007/s11139-026-01435-0',label='Conjecture1, printedp5',scope='Both n>=1,x>5 and n>=6,x>=1, literal Delta_n>0 for sigma2 recurrence'),inputs=context,registry=dict(freshness='HOLD',latest_observed_omega_head='6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3',latest_observed_time_utc='2026-10-29T15:49Z',current_HEAD_verified=False,api_retry=False,reset='No usable reset evidence located in inspected inherited r64-r66 provenance; no current API call',saved_tree_screen=registry,actual_body_read=['Problems/dawsey-russell-urban-partition-polynomial-derivative-question-refutation.md','D5/S0/Certificates/DawseyPartitionPolynomialDerivativeQuestionRefutation.lean'],limits=['Saved trees are historical, not current-head full delta clearance','r57 omega-D5.json is Blueprint markdown, not actualLean','Current raw README has no head SHA','No exhaustive worldwide prior-art clearance']),http=[json.loads(t) for t in (P/'http.jsonl').read_text().splitlines()],sources=[dict(path=str(p.relative_to(P)),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted((P/'sources').iterdir()) if p.is_file()],checks=dict(derivative_rows=100,base_delta_rows=12,euler_product_rows=17,scalar_comparisons=1000,source_inequalities=970,independent_shift_rows=19,abel_identity_checks=300,kernel_identity_checks=80,below_threshold_probes=300,finite_checks_are_proof=False),resource_limits=dict(address_space_bytes=536870912,sampled_group_rss_bytes=536870912,cpu_seconds=210,wall_seconds=230,sample_ms=40,blas_threads=1),failures=[],extraction_warnings=['pdftotext ICC/Lab profile warnings on predecessor publisher PDF; readable text retained'],strongest_objection='No all-index proof of the sufficient cone or source result. Public x1 result and standard bridges earn no credit.',falsifier='Exact in-domain Delta_n<=0; negative derivative or suffix alone is only a route obstruction',precise_gap='All n>=6,j>=1 suffix domination, or alternative uniform all-x>=1 direct inequality',runnable='bash run.sh',new_lean=False,proof_file=False,children=False,external_mutations=False)
obj['artifacts']=[dict(path=str(p.relative_to(P)),sha256=sha(p)) for pattern in ['*.py','*.md','run.sh'] for p in sorted(P.glob(pattern))]
(P/'provenance.json').write_text(json.dumps(obj,indent=2))
print(json.dumps({'status':obj['status'],'credit':0,'sources':len(obj['sources']),'context_files':len(inputs),'checks':'PASS'}))
