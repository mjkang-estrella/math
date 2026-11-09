import pathlib,json,hashlib,resource,os
resource.setrlimit(resource.RLIMIT_CPU,(30,30));resource.setrlimit(resource.RLIMIT_AS,(1536*1024**2,)*2);os.sched_setaffinity(0,{0,1})
L=pathlib.Path(__file__).resolve().parent.parent;D=json.loads((L/'extracted.json').read_text());H=json.loads((L/'history-id-title-matches.json').read_text());receipts=sum([json.loads(p.read_text()) for p in [L/'sources/receipts.json',L/'sources/more-receipts.json',L/'sources/final-receipts.json']],[])
notes={
344815:'Need a universal embedding under simultaneous minimum and maximum degree; no embedding lemma or witness found. Connectedness/domain shortcuts would not resolve source scope.',
344874:'Need exact Ramsey upper bound for every eligible tree and even wheel; a finite tree instance alone cannot prove universal assertion.',
344892:'Need source definition of free 2n diagrams, minimality and extremal unknot-count normalization before a comparison is meaningful. Primary body unread.',
344932:'Asymptotic exponent requires an all-large-n acyclic chromatic construction, not a finite counterexample to an informal o(1). Primary body unread.',
344948:'Inherited partial exclusion: degree-five table entry is already proved by Battistoni2211.16842 Theorem1, per older notes. Stop that route. Other table entries remain unreviewed; do not exclude whole table.',
344962:'Classification of every maximum t-intersecting permutation family requires exact parameter conventions and a global extremal argument. No source-body review or maximum-family certificate.',
344972:'Need the fixed-t clique bound for all bounded-degree m-edge graphs; total-clique theorem alone is not the needed bridge. Primary body unread.',
344976:'The literal itself flags uncertain theorem/conjecture status. Need surrounding source body and parity/range conventions; no endpoint or novelty assertion.',
345013:'Need exact dependence of alpha on diameter and excluded graph families from primary body; title suggests a resolution but is not theorem evidence.',
345032:'Literal says implication to Connes embedding. Need actual free-group definition and source implication body, then full-scope bridge to any refutation; none read here. No novelty route from label.',
345063:'Sufficient regularity is unspecified in record; must recover primary model and assumptions. No corrected-source result claimed.',
345068:'Need exact modified-diagonal normalization and cycle dimension indexing. No Chow relation established; body unread.',
345082:'Need characteristic/base-field and mld conventions before a divisor construction or unboundedness argument. Body unread.',
345091:'Need a graph with certified cop strategy lower bound or universal t-4 strategy. Finite domination or treewidth bounds alone do not settle literal game.',
345127:'Need all-range k-uniform minimum-vertex-degree matching theorem. Greedy matching only supplies stronger degree thresholds, no full bridge.',
345195:'Need a universal Omega(n^(2/3)) twins construction; finite pattern search cannot prove the asymptotic. Source body unread.',
345227:'Need recover relevant analytic eigenbranch and potential assumptions; ground-state variational bound does not automatically govern arbitrary branches. Body unread.',
345273:'Need asymptotic Alice strategy for all fixed nonreciprocal p; no finite random-graph diagnostic can certify high probability.',
345311:'Need a universal power-saving chromatic bound for Hasse diagrams, including asymptotic constants; source body unread.',
345358:'Need recover conditional cut definition and whether k is regular degree rather than a lower bound; no domain-paraphrase refutation pursued.',
345384:'Need primary bondage definition/domain and a certified planar example or full universal bound. No computational witness or primary proof reviewed.',
345388:'Need polytopal realization and generic linear orientation, not merely an abstract acyclic cubic graph; source body unread.',
345404:'Need full Andrasfai/Vega family definitions and all ratios n/3<s<=n/2. Local critical-ratio theorem does not settle full interval.',
345413:'Need exact Yokota normalization, admissibility and uniform error quantifier from source; no asymptotic endpoint proved.',
345500:'Need actual reflection/Hurwitz definitions and current full-group classification body; G6 theorem alone does not cover all well-generated groups.',
345509:'Need minor-free all-t tree decomposition whose bags admit t-colorings; t=5 source result is an uncredited parameter instance.',
345589:'Need universal tight-path extremal bound in ordinary uniform hypergraphs; convex geometric source setting alone cannot justify it.',
345652:'Need transience under only supercritical mean for almost every infinite tree; bounded support/minimum offspring argument leaves genuine scope gap.',
345677:'Need exact torsion and trace-fiber conventions for all hyperbolic torus-boundary manifolds; twist-knot theorem is partial and uncredited.'}
primary={
344827:('excluded_public_counterexample',['1912.04477'],'Section5.2, Conjecture5.1 and Example5.3: w=145723689(10), predicted7 versus actual5. Read explicit formula evaluation and surrounding bridge to patch ideal; not an independent commutative-algebra reproof.'),
345029:('held_hard_mathematical_gap',['1912.12253'],'Conjecture3, Proposition5, Theorems1-2, Definitions7/Lemmas8-11 and recurrence proof sketch read. Sustained rational-proxy/root-count analysis plus12 completed exact diagnostics. Universal root bifurcation/prime monotonicity remains unproved.'),
345041:('excluded_source_public_counterexample',['1912.12605'],'Source In(G) consists of vertex subsets with independence number<n, not independent sets of size<=n. Read definition, collapsibility setup, Conjecture1.4 and Section7.2 Proposition7.2 Alexander-dual/nerve proof: dodecahedron C(I8)>=16>14. Full source assertion already refuted.'),
345042:('held_hard_mathematical_gap',['1912.12605'],'Read source complex definition, Conjecture8.1 and surrounding implication. Need universal link collapsibility bound; truncated-independence-complex interpretation in record must not replace source object. No proof attempt on corrected surrogate.'),
345222:('excluded_public_full_scope_proof',['2001.07082'],'Read Conjecture1.2, Theorem5.1 and Corollary5.2 with final induction/proof bodies. Corollary proves exact d<=q upper bound and tangent-plane/common-secant equality classification. Supporting geometry not independently rederived.'),
345289:('excluded_public_source_resolution_and_paraphrase_defect',['2001.09123','2002.08535'],'Even case in actual source is n(n-2)!, not (n-2)!. Read source Conjecture1.2/examples and Pawlowski Theorem1.1, antichain/Bruhat setup, Lemma2.9 and final coefficient-bound proof. Public theorem resolves source; defective factor is not a discovery.'),
345398:('excluded_routine_explicit_bridge',['2002.01347','roman2019','roman2020'],'Read TRD/supercritical definitions, Conjecture1 and source Theorem9.3 proof. Earlier Lampman-Mynhardt-Ogden Proposition2.3 proof explicitly repairs an edge-added optimum with both endpoints positive, cost<=2. Equality at a supercritical edge proves support; universal vertex handled separately. Routine bridge, no Lean investment.'),
345435:('held_hard_mathematical_gap',['2002.03065'],'Read Conjecture1.5, normalization, Proposition6.1 and proof. Derived exact4D determinant-one box permanent and analytic bound for a continuous anisotropic family, not global convex bodies. Missing global mixed-volume inequality beyond AF and all semantic Lean bridges.'),
345538:('held_public_full_scope_claim_not_fully_audited',['2608.18392','2608.22816'],'Read Ling Theorem1.1/Remark1.2 and Han cap-move Lemma2.1 proof plus final telescoping argument. These publicly claim full scope. Safe-move existence/variational/discretization bodies not fully audited here; do not call independently verified theorem. Park discovery investment, retain prior claim.'),
345543:('excluded_paraphrase_only_route',['2002.07144'],'Read Definition1.1 and Section2.7 Theorem2.10 proof/Conjecture2.11. B is Bulgarian solitaire and degree is average preimage multiplicity at f(x), not maximum fiber. Unbounded maximum-fiber observation would only attack defective paraphrase. Actual mean-degree limit not solved.'),
345616:('excluded_public_full_scope_counterexample',['2002.10151','2608.14517'],'Read original parameter definition/conjecture and complete Lauri Theorem2 construction, Lemmas4-8 proof. Six-block G(d,k), d>=2,k>=4d-1, has L=k and equitable number k+d; first d2,k7 has32 vertices. Source alpha_min is min_v max independent set containing v, not minimum maximal independent size. Public refutation, no credit.')}
out={}
for i,x in D.items():
 d=x['record'];n=int(i);status,src,review=primary.get(n,('held_literal_record_only',[],notes.get(n,'')))
 if n==344948:status='held_inherited_partial_exclusion_route_stopped'
 rr=[r for r in receipts if r['name'] in src];out[i]={**{k:v for k,v in x.items() if k!='record'},'mathdb_id':n,'title':d['title'],'literal_statement':d['statement'],'source_url':d['source_url'],'source_name':d['source_name'],'outcome':status,'accepted_credit':0,'new_review_depth':'primary_definitions_and_selected_theorem_or_proof_bodies' if n in primary else 'literal_cached_record_only','review':review,'new_primary_receipts':rr,'inherited_matches':([{'reason':notes[n],'evidence':'older-ledger-context.json; history-id-title-matches.json; older parent-fresh-discovery-r5/FINDINGS.md referenced there'}] if n==344948 else []),'history_search':{'matches':len(H[i]),'receipt':'history-id-title-matches.json','classification':'inherited partial exclusion' if n==344948 else 'current reservation or unrelated digit/hash/numerical matches; no target exclusion located in bounded search','scope':'ID and exact case-insensitive title in md/results/ledgers; not all synonyms/all historical bodies'},'mathematical_attempts':'ATTEMPTS.md' if n in [345029,345398,345435] else None,'remaining_lemma':review if status.startswith('held') else None,'lean_endpoint':None,'novelty_clearance':False}
assert len(out)==40
(L/'results.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n');print('40 records;',len(primary),'primary;',40-len(primary),'literal only')
