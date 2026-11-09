import pathlib,json,hashlib,datetime,re
R=pathlib.Path(__file__).resolve().parent;records=json.loads((R/'records.json').read_text());receipts=json.loads((R/'source-receipts.json').read_text());out={}
reasons={
357907:'Transfer of a random continuum critical exponent to discrete uniform models; no deterministic finite obstruction or feasible full probabilistic Lean route recovered from statement alone.',
357926:'Full successive-minima lattice-point inequality; endpoint examples do not address all dimensions and arbitrary convex bodies. Primary body not reviewed; no exclusion as known asserted.',
357971:'Requires uniform boundary-pinning decay at q=Delta+1, not merely uniqueness or weak mixing; no full-scope contraction established.',
357972:'Requires polynomial mixing for all finite maximum-degree graphs; tree-case progress does not bridge to this endpoint.',
357981:'Exponential bound for all n; small n path packings cannot decide it. Need a structural encoding or reversing-permutation bound.',
358017:'Relevant extremal colouring property and both Hajós operations require primary reconstruction; no proxy based only on dichromatic number used.',
358021:'Asymptotic cap count over all prime powers; finite enumeration would not establish the exponent.',
358083:'Cycle bound requires precise source n qualifications; no small-order loophole pursued without primary hypotheses.',
358084:'Sufficiently-large quantifier prevents a finite small graph from refuting; no infinite extremal family constructed.',
358088:'Maximum criterion and linear-fragmentation law definitions remain unrecovered; moments alone do not certify the desired endpoint.',
358128:'Uniqueness over arithmetic limiting probability measures requires the actual admissibility conditions; convexity alone does not imply strict minimizer uniqueness.',
358137:'Need critical frustration under all edge deletions and exact equality quantifiers; arbitrary signed graph examples would not suffice.',
358143:'Need explicit g_k definitions and elementary-basis coefficients; ordinary chromatic e-positivity does not automatically imply this stronger claim.',
358172:'General transitive-group field-counting asymptotics; no tractable new full-scope mechanism. Trivial-group domain correction is ineligible.',
358238:'Need unbounded clique dynamics, not a finite nonrepeating prefix; primary locally-cyclic surface definitions not reviewed.',
358239:'Requires eventual clique-nullity of every disc triangulation in source scope; small graph dynamics would not prove it.',
358244:'Infimum over all finite-type hyperbolic surfaces; explicit corkscrew length proves only one inequality. Need matching universal lower bound.',
358303:'Connected graphon alone permits highly inhomogeneous degrees; need exact edge ordering and law before constructing a probabilistic obstruction.',
358326:'Need exact (1,1) removal process and expectation law; no generic random-DAG surrogate accepted.',
358340:'Density notion and strict/weak threshold must be sourced; no equality-threshold correction pursued.',
358350:'Equivariant twisted TMF and VOSA compatibility classes not reconstructed; no Lean route to full semantic endpoint identified.',
358356:'Hyperplanes, vertex convention and affine-hull restriction need primary text; no dimension/endpoint loophole used.',
358358:'Asymptotic (2+o(1))k quantifier requires uniform large-k immersion theorem; finite tournament witnesses do not decide it.',
358361:'Need full commutative algebra hypotheses including purity and generic complete intersection; a monomial ideal without all properties is not an answer.',
358496:'Five-way equivalence includes distinct norm/weak topologies and QTS; no implication assembled without source theorem bodies.',
358523:'B(M) is a decomposition object requiring primary definition; no replacement by maximum pointwise dimension justified.',
358540:'Uniform bounded tree-independence requires all graphs in class; no unbounded certified family supplied.',
358636:'Global Willmore minimization is stronger than strict local stability; no full-scope variational route.',
358637:'Requires two positive smallest elements compatible with same three larger integers; no numerical search or formal bridge attempted.',
358668:'Need distinguished weight-diagram/base conventions and all highest weights; no substitute statistic theorem.',
358684:'Uniform O(k) bound over connected matroids; fixed representable examples or graphical subclass cannot settle it.'}
primary={
357975:('primary_conjecture_and_context','Conjecture1.1; Theorem1.2 statement; normalized L=D^-1/2 L D^-1/2 definition. No proof of the conjectured bound.','hold_no_full_mechanism','Cheeger lower bound is only2/n^2. Transfer from combinatorial Laplacian spread fails because normalization depends on degree. Need sharp simultaneous complement Rayleigh bound.','2304.01979'),
357976:('primary_conjecture_and_context','Conjecture3.3 literally names G only, while surrounding paragraph explicitly describes graph pairs G or Gc.','excluded_wording_symmetry_route','Complementing the proposed extremizer preserves max(lambda2(G),lambda2(Gc)) but changes its isomorphism type; this is the source wording/symmetry omission, not a credited new mechanism. Bound remains unresolved here.','2304.01979'),
357977:('primary_conjecture_and_context','Conjecture5.1 and connected-complement qualification, Section5; earlier spectral conventions.','hold_no_full_mechanism','A universal-vertex join extremizer for the maximum bound has disconnected complement and is inadmissible here. Deleting a single universal incident edge gives a pendant attachment in the complement, not a sparse balanced cut; no low-low spectral witness. Need both graphs connected and two certified low Rayleigh quotients violating2/sqrt(n).','2304.01979'),
358166:('primary_definition_and_selected_proof_bodies','Theorem5, proof beginning, footnote4 principal smallest minimizer; Conjecture1 and Remark4; eigenvalue/Dirichlet formulas(14),(16),(18).','hold_specific_analytic_gap','After jbar, denominator sin(pi*j/N) increases, so later negative lobes are bounded below by -1/(2sin(pi*j/N)). Need a sampled first-lobe value below every later-lobe envelope. Continuous first minimum alone does not prove sampled comparison. Even N=2m+2 produces ties but footnote4 chooses jstar2; not a refutation.6241 double-precision pairs N<=160 found no violation; not a proof or novelty evidence.','2304.11602'),
358177:('primary_theorem_and_proof_body','Theorem1 statement and printed typical-case induction, Corollary2.1 statement and mu mod3=1 proof read. Other omitted/similar theorem cases not independently reconstructed.','excluded_known_source_resolution','Corollary2.1 explicitly states L(mu,3^n)=3^(n-2) for mu mod3=1; its proof bounds valuation>=2 and realizes equality at listed residue classes3 or6 mod27. No new endpoint credit; small n formula qualification not pursued.','2304.12193'),
358307:('primary_definition_theorem_and_proof_body','Section4.3 Conjecture4.8, Proposition4.9 proof and Corollary4.9.1 proof; absorbing number definitions.','hold_equivalent_old_open_problem','Proposition4.9 only gives omega(alpha*)<=omega(alpha[x]); Corollary4.9.1 proves equivalence to old C2 polynomial extension equality via beta=alpha[x]+(x-1). Strong n-absorption alone is not the missing extension theorem. Preserve source typo between generated homogeneous components and largest contained ideal; use largest homogeneous contained part.','2305.03878'),
358323:('primary_definition_theorem_and_selected_proof_bodies','Chung Definitions37-41, Theorem42, Conjecture47 and its failed BKW application; Sokal Theorem1.5 and proof beginning/Lemma3.8 proof read separately.','candidate_full_lean_pending_independent_reviews','a=b=c=1. Actual generated sequence P has P_(3k+2)(0)=0 for all k, hence0 in upper limiting zero set, while every denominator root has modulus1. No circle set limit as claimed. Complete Lean exact_mathdb_negation with generating bridge and minimal root; strict extracted replay and31-declaration transitive axiom audit. Significance/novelty/fidelity remain independent/root decisions;0 credit.','2305.05130'),
358411:('primary_definition_and_selected_proof_bodies','Total arc-connectivity definition; Section4 proof ending Claims13-14; Section5 tripled-path construction and Conjecture1.','hold_exchange_lemma_gap','The source nonstrong optimal tripled path is not a refutation of existence of a strong optimum: orient each triple uniformly2forward1backward. Every pair has directed connectivities2 and1, saturating undirected cut3, so this strong orientation ties3*binom(t,2). Alternating signs gives only the source2/3 ratio. Reversing SCC arcs can lose internal cut capacities; need a nondecreasing SCC-merging exchange, or a certified graph where every strong orientation loses. No sweep claimed.','2305.08688'),
358667:('primary_theorem_and_selected_proof_bodies','Conjecture1 and Theorem1.1 read; Lemma3.5 case proof and conclusion read; not all preceding lemma proofs audited.','excluded_known_source_refutation','The cited source explicitly disproves the exact conjecture. Theorem1.1 gives m^2-m-24 with unique B_m^4 at m>=10, while the proposed B_m and B_m^5 are not those maximizers. Do not reformalize for discovery credit.','2306.02761')}
for i,v in records.items():
 n=int(i);r=v['record'];p=v['provenance'];x={'mathdb_id':n,'title':r['title'],'canonical_url':r['canonical_url'],'literal_statement':r['statement'],'provenance':p,'raw_file':f'raw/{i}.jsonl','source_url':r['source_url'],'source_name':r['source_name'],'inherited_matches':[{'kind':'administrative_current_r52_assignment','file':'../ledger.json','technical_review':False}],'inherited_exclusion_found':False,'history_check':'history-delimited.txt; full-title/ID scoped report search. Initial broad substring matches in history-search.txt include numeric/hash noise; no global technical nonreview claim.','new_review_depth':'literal_statement_only','outcome':'hold_primary_body_unread','reason_and_remaining_lemma':reasons.get(n),'source_body_receipts':[],'accepted_credit':0,'primary_body_reviewed':False,'formal_status':'not_attempted'}
 if n in primary:
  depth,review,outcome,reason,src=primary[n];x.update(new_review_depth=depth,primary_body_reviewed=True,primary_review_scope=review,outcome=outcome,reason_and_remaining_lemma=reason,source_body_receipts=[q for q in receipts if q['url']=='https://arxiv.org/pdf/'+src])
 if n==358323:x.update(formal_status='fresh_strict_replay_pass',lean_endpoint='MathDB358323.exact_mathdb_negation',packet='proof-source.zip',local_declarations_audited=31,axioms=['propext','Classical.choice','Quot.sound'],prior_art_limits='Bounded title/path/primary-body comparison only. Sokal theorem excludes the persistent dominant unit-ratio case, so its circle theorem does not subsume this obstruction. No exhaustive citing-literature, journal-update, MathDB/Palomar or all-registry-body clearance.',remaining_qualification='Independent mathematical, fidelity, significance/prior-art review and root acceptance; no selfacceptance.')
 
 if n==358323:x['additional_source_receipts']=[json.loads((R/'sokal-receipt.json').read_text()),json.loads((R/'sokal-arxiv-receipt.json').read_text())]
 out[i]=x
assert len(out)==40; (R/'results.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
# Retain compact inherited family context rather than copying historical evidence trees.
ctx=[]
for p in [R.parent.parent/'prior-campaign-context.json',R.parent.parent/'ledger.json',R.parent/'ledger.json']:
 d=json.loads(p.read_text());item={'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'families':{}}
 for key in ['accepted','excluded','held_candidates','candidates']:
  if key in d:item['families'][key]=d[key]
 ctx.append(item)
(R/'inherited-family-context.json').write_text(json.dumps(ctx,indent=2,ensure_ascii=False)+'\n')
print('exactly40;primary reviewed9;candidate1;known2;wording exclusion1;remaining36 holds including candidate qualification')
