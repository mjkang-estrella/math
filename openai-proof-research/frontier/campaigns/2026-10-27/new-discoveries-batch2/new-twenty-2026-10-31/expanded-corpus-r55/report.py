import pathlib,json,hashlib,datetime,subprocess
p=pathlib.Path(__file__).resolve().parent;d=json.loads((p/'extracted.json').read_text());h=lambda x:hashlib.sha256(x).hexdigest()
notes={
360848:('excluded_source_paraphrase_already_refuted','Conjecture6.5 is four named families; Example6.6 already refutes broad wording.','ml'),
360853:('parked_exact_lower_bound_missing','Need explicit crown-free representation-number>3 component or complete counting/semantic bridge. Recent fixed-order theorem is related, not exact subsumer.','crown'),
360865:('unresolved_statement_only','General equitable Brooks scope; no full-scope mechanism selected. Odd/even complete-bipartite traps may involve source exceptions; no endpoint correction attempted.',None),
360894:('unresolved_statement_only','Distribution-fixed metric minimization requires recovering contact-analytic compactness and existence definitions. Primary body unread.',None),
360899:('parked_logarithmic_exponent_gap','Need exponent1 rather than source positive Favard exponent. Small-n log-domain correction ineligible.','trapezoid'),
360900:('parked_consecutive_monotonicity_gap','Exact rational diagnostic through7; subdivision only proves divisibility-index inequality, not consecutive monotonicity.','trapezoid'),
360945:('unresolved_statement_only','Wide-partition matching/Latin filling equivalence suggests substantial structural theorem; width definition not recovered from primary.',None),
360967:('unresolved_statement_only','Need a fixed forbidden graph with genuinely intermediate unbounded sublinear bootstrap time or a full dichotomy proof.',None),
360986:('unresolved_statement_only','Infinite edge-coloring and induced class2 obstruction quantifiers require source definitions. No takeover of held326640 majority candidate; no family identity asserted.',None),
360992:('unresolved_statement_only','Literal statement is classical convex-polygon conjecture. Small-n malformed-domain corrections ineligible; primary body unread.',None),
360993:('unresolved_statement_only','Fixed-terminal global Steiner optimization needs full geometric lower bound; no finite shortcut selected.',None),
360994:('unresolved_statement_only','Characteristic-edge-vector embedding and Steiner cost require source bridge; source body unread.',None),
361004:('unresolved_statement_only','Maximum covering constant definition and exact optimization domain missing from literal; primary body unread.',None),
361012:('unresolved_statement_only','Stable representation expectation asymptotic and primitivity rank need source scope; identity/proper-power edge cases are not eligible corrections.',None),
361036:('unresolved_statement_only','Could search cubic planar graphs, but no source-fidelity or novelty gate completed; no diagnostics started.',None),
361062:('unresolved_statement_only','Depends on omitted combinatorial criteria and tangent-space dimension definitions; primary body unread.',None),
361070:('parked_topological_bridge_gap','Source n+2 upper bound uses alternating subspace; n+1 case requires a new zero-supremum/argmax compactness argument.','lineability'),
361076:('unresolved_statement_only','Need uniform tight distance-regular diameter argument in b; no finite instance could prove general bound.',None),
361086:('ordinary_refutation_source_version_HOLD_no_Lean','n7,k2,m11,t6: ambient maximum degree4, every compressed family degree>=5. Full ordinary proof retained; published body403; Lean and qualification outstanding.','kneser'),
361089:('unresolved_statement_only','Shifted quadratic ideal relation graph and density dependence invariant absent from literal definitions; primary unread.',None),
361134:('unresolved_statement_only','Full bridgeless cubic normal5-edge-coloring conjecture; no shortcut selected.',None),
361158:('unresolved_statement_only','Requires mixed-characteristic monodromy realization for all conjugacy classes; primary body unread.',None),
361166:('parked_known_related_theorem_uniqueness_bridge_unread','Theorem4.6 proves all-optimal-code criterion, not an explicit uniqueness bridge. Source conclusion reports solved conjecture; no new result claim.','codes'),
361177:('unresolved_statement_only','Network nesting/balance and entropy prescription need primary definitions before construction.',None),
361186:('excluded_wording_sign_correction','Positive determinant and Fxx>0 make P a minimum in negative-discriminant case; maximum is a source sign error.','beloch'),
361258:('unresolved_statement_only','Exact vertex-separating tree-system semantics and complexity reduction missing; primary unread.',None),
361269:('parked_global_recoloring_invariant_missing','Source ceil(Delta/3) insertion proof does not extend to constant2; endpoint color saturation prevents naive induction.','impropriety'),
361283:('unresolved_statement_only','Need eigenvalue-to-cut-packing bridge in all irregular graphs; no small source-vetted counterexample search completed.',None),
361289:('unresolved_statement_only','Star would contradict displayed inequality for r2, so source likely has omitted restrictions. No wording correction investment without primary body.',None),
361304:('unresolved_statement_only','Connectedness absent in paraphrase; disjoint-union loophole ineligible. Need actual curvature and connected-source statement.',None),
361370:('unresolved_statement_only','Displayed RHS counts star in F rather than D, a likely paraphrase defect. No credit for elementary intersecting-triangle counterexample; source body unread.',None),
361452:('unresolved_statement_only','Restricted-root tangent-cone regularity needs geometric definitions and primary proofs.',None),
361456:('unresolved_statement_only','Full oriented-tree arc-density embedding scope; primary digraph/oriented-graph hypotheses not recovered.',None),
361470:('unresolved_statement_only','Dichromatic forcing of directed topological minor requires full extremal proof; primary unread.',None),
361503:('unresolved_statement_only','Tournament backedge-clique complexity requires exact decision reduction; no source body reviewed.',None),
361549:('unresolved_statement_only','Weighted bisection extension beyond known subcubic scope; no vetted exact counterexample route selected.',None),
361559:('unresolved_statement_only','Random4-regular global rigidity may have generic-versus-every-framework scope distinction; source definitions unread.',None),
361574:('excluded_routine_orthogonality_with_embedding_bridge','Polynomial sign-change product and Chebyshev orthogonality prove root bound; source Theorem3.9 supplies injective real curve parametrization.','chebyshev'),
361580:('unresolved_statement_only','Super-prolongation/downstream axioms missing; primary source required before route selection.',None),
361584:('unresolved_statement_only','Asymptotic extremal iterated-line-graph ratio; disconnected/vanishing-denominator issues are domain corrections, not candidates.',None)}
receipts=[json.loads(x) for x in (p/'sources/receipts.jsonl').read_text().splitlines()]
res={}
for i,x in d.items():
 n=int(i);outcome,attempt,source=notes[n];record=x['record']
 res[i]={'mathdb_id':n,'title':record['title'],'canonical_url':record['canonical_url'],'literal_statement':record['statement'],'provenance':{k:v for k,v in x.items() if k!='record'},'raw_preserved_file':f'raw/{i}.jsonl','source_name':record['source_name'],'source_url':record['source_url'],'review_depth':{'literal_read':True,'primary_definition_and_selected_body_read':source is not None,'whole_paper_reviewed':False,'inherited_technical_review_claimed':False},'source_receipts':[a for a in receipts if source and a['name']==source+'.pdf'],'inherited_matches':[],'history_check':'Exact IDs plus selected mechanism terms in history-search.txt; exact all40 titles in history-titles.txt (no matches). Administrative reservation and numerical coincidences distinguished from technical review. Bounded search, no global nonreview claim.','outcome':outcome,'mathematical_attempt_or_remaining_gap':attempt,'detail':'ATTEMPTS.md' if source else None,'formal_endpoint_complete':False,'credit':0,'acceptance':'root only; not submitted as accepted'}
assert len(res)==40 and set(map(int,res))==set(json.loads((p/'reservation.json').read_text())['ids'])
(p/'results.json').write_text(json.dumps(res,indent=2,ensure_ascii=False)+'\n')
inputs={}
for f in [p/'reservation.json',p.parent/'ledger.json',p.parent.parent/'ledger.json',p.parent.parent/'prior-campaign-context.json',pathlib.Path('openai-proof-research/sources/upstream.json')]:inputs[str(f.resolve())]=h(f.read_bytes())
manifest=pathlib.Path('openai-proof-research/frontier/campaigns/2026-10-14/formal/lake-manifest.json');env={'lean_version':subprocess.check_output(['/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean','--version'],text=True).strip(),'mathlib_pinned_revision':'d13f23b723b8a846827a245b89c10fc7d3f11612','lake_manifest_path':str(manifest.resolve()),'lake_manifest_sha256':h(manifest.read_bytes()),'formal_work':'No local Lean theorem compiled; no strict replay or axiom audit or packet claimed. Cached upstream dependencies were not rebuilt or modified.','resource_limits':'Investigation scripts affinity <=2 CPUs, CPU<=120s, AS<=6GiB, timeout<=140s; exact verification CPU30s/AS1GiB/wall40s; trapezoid self-wall100s. No background jobs remain. Small metadata reads not expensive processes.','input_hashes':inputs,'administrative_context':'Accepted count remains4/20 beyond39. Ledger is mutable context, not immutable mathematical source.'}
(p/'environment.json').write_text(json.dumps(env,indent=2)+'\n')
print('results',len(res),'primary',sum(x['review_depth']['primary_definition_and_selected_body_read'] for x in res.values()))
