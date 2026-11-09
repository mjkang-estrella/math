import pathlib,json,hashlib,datetime,resource
resource.setrlimit(resource.RLIMIT_AS,(768*1024**2,768*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(30,30))
D=pathlib.Path(__file__).resolve().parent;rows=json.loads((D/'results.json').read_text());H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
updates={
'385446':('exclude_literal_alternative_already_proved_in_current_registry',['registry-packing-main.tex','registry-packing-intro.tex','registry-packing-signs.tex','registry-packing-cert.tex'],'Sharp radial Schwartz auxiliary-function endpoint is an existing upstream theorem; A2 universal optimality not concluded. Original AIM context remains held.'),
'385502':('park_singular_insertion_route_uniform_contact_bound_unproved',['sticky','packing-periodic.pdf','hypostatic.pdf'],'Need admissible disk frame/gap and a uniform contact upper bound over all packings of its radii; local singular rigidity alone is insufficient and already known in examples.'),
'385513':('exclude_finite_simple_graph_classification_known_full_scope_bridge',['monks.html'],'Finite simple classification follows from existing degree-5 theorem, degree-4 theorem, degree<=3 insertion and degree>=6 count; original AIM graph conventions not restored.'),
'385582':('park_slab_global_phase_and_source_scope_gaps',['critical.html'],'Two finite diagnostics found no better direction; derived transverse instability only matters if it precedes the source-scoped global crossing. Need actual threshold/domain and global chamber argument.'),
'385892':('park_missing_primary_second_theorem_no_new_body_review',[],'Missing theorem and subgroup cannot be replaced by generic amenable-group sumset theorems.')}
for i,r in rows.items():
 r.update(new_original_problem_body_review=False,new_complete_dependency_audit=False,current_full_registry_clearance=False,discovery_credit=0,new_unique_record_coverage=0,old_objections_preserved=True)
 r['remaining_lemmas_or_objections']=r['old_disposition']['reason']
 if i in updates:
  outcome,sources,reason=updates[i];r.update(new_outcome=outcome,new_primary_body_review=bool(sources),new_proof_body_review=bool(sources),new_source_receipts=[f'sources/{s}.receipt.json' for s in sources],new_review_notes='ATTEMPTS.md',new_reason=reason,remaining_lemmas_or_objections=reason)
 r['source_scope_cleared']=False;r['literal_statement_sha256']=hashlib.sha256(r['literal_statement'].encode()).hexdigest()
(D/'results.json').write_text(json.dumps(rows,indent=2)+'\n')
context=[]
for p in [D.parent/'ledger.json',D.parent.parent/'ledger.json',D.parent.parent/'prior-campaign-context.json',D.parent/'AGENTS.md',D.parent.parent/'AGENTS.md',D.parents[4]/'AGENTS.md']:
 if p.exists():context.append(dict(path=str(p),sha256=H(p),mutable=p.name=='ledger.json'))
env={'lean_binary':'/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean','lean_version_user_pin':'4.34.1','mathlib_revision_user_pin':'d13f23b723b8a846827a245b89c10fc7d3f11612','lean_executed':False,'local_formal_endpoint':None,'trust_limits':'No Lean packet, no local kernel endpoint, no strict rebuild or axiom audit claimed. External cached dependencies read-only; no upstream rebuild.'}
p=pathlib.Path(env['lean_binary']);env['lean_binary_sha256']=H(p)
(D/'environment.json').write_text(json.dumps(env,indent=2)+'\n');(D/'context-bindings.json').write_text(json.dumps(context,indent=2)+'\n')
source=[]
for p in sorted((D/'sources').glob('*.receipt.json')):
 r=json.loads(p.read_text());source.append(dict(receipt=str(p.relative_to(D)),**r))
(D/'source-index.json').write_text(json.dumps(source,indent=2)+'\n')
print(json.dumps({'ids':len(rows),'new_related_primary_reviews':sum(r['new_primary_body_review'] for r in rows.values()),'new_selected_proof_section_reviews':sum(r['new_proof_body_review'] for r in rows.values()),'original_problem_body_reviews':0,'complete_dependency_audits':0,'lean_endpoints':0,'credit':0},indent=2))
