import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).parent
receipts=[json.loads(s) for s in (L/'source-receipts.jsonl').read_text().splitlines()]
for r in receipts:
 if 'sha256' in r:
  assert hashlib.sha256((L/'sources'/r['name']).read_bytes()).hexdigest()==r['sha256']
  assert hashlib.sha256((L/'frozen'/r['name']).read_bytes()).hexdigest()==r['sha256']
for r in json.loads((L/'bindings.json').read_text()):
 assert hashlib.sha256(pathlib.Path(r['copy']).read_bytes()).hexdigest()==r['sha256']
 if r['kind']=='frozen':assert hashlib.sha256(pathlib.Path(r['original']).read_bytes()).hexdigest()==r['sha256']
failures=[r for r in receipts if 'error' in r]
(L/'failures.json').write_text(json.dumps({'access':failures,'missing_optional_modules':['networkx','pysat','z3'],'mathematical':['spectral exact target publicly resolved July2026','weak acyclic matching exact target publicly resolved by2025','one/two Kempe-change repair insufficient on K33 witness','112-vertex adaptation achieved19 abnormal edges; required at most2'],'unperformed':['current denied proof-registry heads','external DRAT archive replay','full worldwide novelty review']},indent=2)+'\n')
prov={'lane':str(L),'time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'eligibility':'HOLD','credit':0,'counts':{'additional':9,'total':39,'next':40},'retired_target':{'question':'Elphick–Linz–Wocjan Conjecture1','source':'https://arxiv.org/pdf/2101.05229v3','full_prior_proof':'https://arxiv.org/pdf/2607.18044v1','labels':['Theorem1.2','Lemma2.2','Theorem2.3','Lemma1.4'],'proof_pages_read':[5,6,7,8,9]},'replacement':{'source':'https://arxiv.org/pdf/2104.09241v1','label':'Section3 Question1','status':'unresolved locally; current public status not certified','closest_current_body':'https://arxiv.org/pdf/2608.10012v1','external_certificate_replay':False},'breadth':{'completed_distinct_families':10,'ranked_survivors':1,'history_scan_files':len(json.loads((L/'history-bindings.json').read_text())),'novelty_certified':False},'limits':{'AS_bytes':536870912,'process_group_RSS_bytes':536870912,'CPU_seconds':210,'wall_seconds':230,'guard':'/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py','environment':{'OPENBLAS_NUM_THREADS':'1','OMP_NUM_THREADS':'1','PYTHONDONTWRITEBYTECODE':'1'},'cap_raises':False},'administrative_bindings':'bindings.json','source_receipts':'source-receipts.jsonl','historical_references':'history-bindings.json','checks':['check_repair.py','check_construction.py','verify_checks.py'],'failures':'failures.json','no_complete_resolution':True,'no_PROOF_md':True,'no_Lean_manuscript':True,'no_children':True,'public_registry_status':'UNCLEARED; prohibited routes parked; no retry','external_mutations':False}
(L/'provenance.json').write_text(json.dumps(prov,indent=2,ensure_ascii=False)+'\n')
excluded={'final-manifest.json','final-verification.json'}
entries={str(p.relative_to(L)):{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in excluded}
(L/'final-manifest.json').write_text(json.dumps({'excludes':sorted(excluded),'files':entries},indent=2)+'\n');print('manifest entries',len(entries))
