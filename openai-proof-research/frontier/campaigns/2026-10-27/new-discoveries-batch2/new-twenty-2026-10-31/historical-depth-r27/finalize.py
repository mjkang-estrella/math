from pathlib import Path
import json,hashlib,datetime,platform,subprocess,os
P=Path(__file__).resolve().parent;B=P.parent.parent;sha=lambda b:hashlib.sha256(b).hexdigest();R=json.loads((P/'reservation.json').read_text());old=json.loads((P/'inherited-dispositions.json').read_text());records=json.loads((P/'records.json').read_text())
# Independent equality checks against corpus decoded statement, not only inherited hashes.
for i,x in records.items():
 assert x['record']['statement']==x['literal_statement'],i
 raw=(P/'raw'/f'{i}.jsonl').read_bytes();assert raw.endswith(b'\n') and sha(raw)==x['raw_line_sha256'];assert json.loads(raw)==x['record']
 assert (Path(x['path']).read_bytes().splitlines(keepends=True)[x['line_one_based']-1])==raw
 assert sha(Path(x['path']).read_bytes())==x['chunk_sha256']
primary={384918:('projection_bounds_incomplete','equiangular-subspaces.pdf; dimension-count.pdf','ATTEMPTS.md:384918'),384921:('two_cycle_construction_gap','mcquillan2010.pdf; workshop-web-extraction.json','ATTEMPTS.md:384921'),384964:('zero_free_regions_unresolved','sokal.pdf; bencs-regts.pdf','ATTEMPTS.md:384964')}
context={384923:'radio definitions and product necessary-condition bridge; known Petersen product comparison',384930:'distance magic definition; no all-regular-graphs classification',384931:'open-neighborhood two-color balance definition; no full classification',384938:'proportional weighted rule recovered, but initial-weight/update conventions remain incomplete',384945:'d/k subset inclusion graph restored; no induced-subgraph classification',384946:'tree homomorphism minimization context restored; no full minimizer characterization'}
results={}
for n in R['ids']:
 i=str(n);o=old[i];x=records[i]
 d=dict(mathdb_id=n,title=x['record']['title'],canonical_url=x['record']['canonical_url'],literal_statement=x['literal_statement'],source_url=x['record']['source_url'],raw=dict(path=f'raw/{i}.jsonl',sha256=x['raw_line_sha256'],ancestor_path=x['path'],line_one_based=x['line_one_based'],ancestor_chunk_sha256=x['chunk_sha256'],newline_preserved=True),literal_sha256=x['literal_sha256'],old_disposition=o['disposition'],old_objection=o.get('individual_reason',o.get('reason')),old_report=R['prior_coverage'][i]['report'],inherited_review=R['prior_coverage'][i],new_unique_review_credit=0,accepted_credit=0,proposal=False,exact_aimpl_body_read_this_pass=False,complete_proof_dependency_audit=False,full_literal_lean_endpoint=False,source_scope_cleared=False,novelty_cleared=False)
 if n in primary:
  outcome,sources,attempt=primary[n];d.update(new_outcome=outcome,new_depth='selected_relevant_primary_definition_theorem_and_proof_bodies_read',new_primary_body_review=True,new_proof_body_review=True,source_files=sources,mathematical_attempts=attempt,remaining_gap='See corresponding route in ATTEMPTS.md; no full-scope proof or exact counterexample obtained.')
 elif n in context:d.update(new_outcome='primary_context_restored_full_problem_still_held',new_depth='workshop_report_definition_and_context_only',new_primary_body_review=True,new_proof_body_review=False,source_files='workshop-web-extraction.json'+('; radio-product.pdf' if n==384923 else ''),new_findings=context[n],remaining_gap=o.get('individual_reason',o.get('reason'))+' Restored definitions/context do not supply the full solution.')
 else:d.update(new_outcome='inherited_hold_retained_no_new_primary_body',new_depth='old_disposition_and_literal_record_reconciled_only',new_primary_body_review=False,new_proof_body_review=False,source_files=None,remaining_gap=o.get('individual_reason',o.get('reason')))
 results[i]=d
assert len(results)==40 and set(results)==set(map(str,R['ids']))
(P/'results.json').write_text(json.dumps(results,indent=2)+'\n')
# Bound registry reuse: actual content identity and external receipt remain flat references.
regdir=P.parent/'fresh-corpus-r10/sources';tree=regdir/'registry-preprints.json';t=json.loads(tree.read_text());assert t['sha']=='3f56f68a176b4494c346091ea0a319651bc217ec' and t['truncated'] is False
assert json.loads((P/'sources/registry-head.json').read_text())['sha']=='4eaee87548250b2682affda7d05d947c05554bae'
files=[tree,regdir/'registry-preprints-receipt.json',P.parent/'fresh-corpus-r8/sources/registry-current.json',P.parent/'fresh-corpus-r8/sources/registry-path-screen.json',B/'lanes/root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',B/'lanes/root-mathdb-accepted-exclusions-r304/historical-dispositions.json']
reuse=[dict(path=str(p),sha256=sha(p.read_bytes()),bytes=p.stat().st_size) for p in files]
(P/'registry-reuse.json').write_text(json.dumps(dict(head='4eaee87548250b2682affda7d05d947c05554bae',complete_preprint_tree=t['sha'],root_tree_complete=False,bounded_path_screen=[v['path'] for v in t['tree'] if '/' not in v['path'] and any(w in v['path'].lower() for w in ['chromatic','isoclin','magic','forcing','ehrhart','labeling'])],files=reuse,limit='Path screen only. Relevant-looking chromatic titles not read in full. No complete public-registry proof-body clearance; no exhaustive registry coverage.'),indent=2)+'\n')
lean=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean');formal=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal');mf=formal/'lake-manifest.json'
m=json.loads(mf.read_text());mathlib=next(x for x in m['packages'] if x['name']=='mathlib');assert mathlib['rev']=='d13f23b723b8a846827a245b89c10fc7d3f11612'
(P/'environment.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),python=platform.python_version(),lean_binary=str(lean),lean_binary_sha256=sha(lean.read_bytes()),requested_lean_version='4.34.1',lean_invoked=False,lean_compilation_claimed=False,mathlib_manifest=str(mf),mathlib_manifest_sha256=sha(mf.read_bytes()),mathlib=mathlib,trust_limit='Dependency cache read-only. No Lean endpoint, extraction, axiom audit, source-to-olean attestation or full upstream rebuild claimed.',process_limits=dict(diagnostics='2 CPUs affinity0,1; 2GiB AS;25s CPU;35s wall;one BLAS thread',render='2 CPUs affinity0,1;2GiB AS;45s CPU;50s subprocess wall',http='25s per request;20MB response bound;one attempt;default verified TLS')),indent=2)+'\n')
# Fresh hashes for actual new bodies/extractions, never a claimed hash of unread/unfetched PDF bytes.
receipts=[]
for p in sorted((P/'sources').iterdir()):
 if p.is_file():receipts.append(dict(path=str(p.relative_to(P)),sha256=sha(p.read_bytes()),bytes=p.stat().st_size))
(P/'source-hashes.json').write_text(json.dumps(receipts,indent=2)+'\n')
print('PASS:40 exact ID keys;all40 raw newline/line/chunk/literal comparisons;3 primary-proof-depth routes;6 context restorations;31 retained holds;zero credit;cache pins recorded')

canonical=[]
for i,d in old.items():
 if 'canonical_record_sha256' in d:
  actual=sha(json.dumps(records[i]['record'],ensure_ascii=False,sort_keys=True,separators=(',',':')).encode());assert actual==d['canonical_record_sha256']
  canonical.append(dict(mathdb_id=i,expected=d['canonical_record_sha256'],actual=actual,match=True))
(P/'historical-canonical-check.json').write_text(json.dumps(canonical,indent=2)+'\n')
print('PASS: all inherited canonical record hashes present in r396 matched')
