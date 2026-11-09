import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent
notes={
373201:'Non-differential-algebraicity requires excluding every algebraic differential equation, not merely finding a non-D-finite generating function; no full-scope obstruction is available.',
373234:'Primary Definition 1.1 and Conjecture 1.3 match the witness quantifiers. Theorem 1.4 only treats s<=d/2 and sufficiently large n; the record overstates its n range. The Ahlswede–Khachatrian counterexample in references is for variable witness sizes/VC dimension, not this conjecture. Star stability fails as a general route because Theorems 1.5–1.6 already construct non-stars.',
373359:'Inversion operation and orientation state space are not defined here; ordinary graph diameter is not the target. Need exact inversion definitions before any finite certificate.',
373405:'Both likelihood degrees require precise statistical varieties and genericity/field conventions; equality for suspensions is only a subfamily. No graph-uniform degree comparison route.',
373424:'Full target is existence of a threshold for every k>=4, not the title source k=4 instance; a fixed-k labeling algorithm would be insufficient.',
373621:'S_BBG is named but its summands and convergence convention are absent. Ei is defined, but computing it does not bound the unspecified series remainder.',
373646:'F is not defined by a recurrence or initial conditions. Choice among tied maxima and uniform O(1) bound need primary definitions; no honest recurrence calculation possible from this row.',
373957:'General linear position with respect to p and flat shadow boundary require geometric definitions; known n-source counterexample does not address n+1. No full convex-body mechanism.',
374181:'Equitable chromatic number concerns existence at a number of colors, not all larger color counts. Complete graphs and odd cycles excluded; cannot use ordinary Brooks coloring as an equitable proof.',
374215:'Existential C0 and d<C0 must be uniform for all sufficiently large x. A few CRT intervals do not establish this polylogarithmic short-interval property.',
374234:'Directed general-position and allowed paths/orientations are undefined; full outcome requires a polynomial reduction with a biconditional, not small graph examples.',
374370:'Tetrahedral X-operators and representation space are absent. N=3,j=0,1 checks are given cases, not the all-rank spectral-parameter identity.',
374620:'Primary Theorem 3 states the exact reflection identity for all n. Its proof decomposes LEGO classes into connected red-black graphs, uses Ehrhart reciprocity for black graphs and inclusion-exclusion for red constraints. Already source-proved; no discovery hypothesis.',
374630:'Residue field, identity-pattern constraints and tangent equations are absent. A rank-3 finite model cannot be searched faithfully from this statement; sufficiently-large-q requirement is also unbounded.',
374699:'Universal induced-forest half bound for planar graphs; a greedy low-degree deletion alone does not maintain the required half budget. No full-scope route; no finite sweep warranted.',
374779:'The counting function is unspecified and the row itself reports one clause already refuted. Need separate exact primary clauses and counterexample before any substantive claim.',
374957:'Primary Conjecture 4.2 is genuine; preorder dual and polytope are source-defined. Matrix transpose is an all-k,l bijection requirement; size<=5 checks are existing evidence, not a new theorem.',
374965:'Primary Conjecture 7.2 asks full bivariate reciprocity. The source proves the diagonal specialization using ordinary reflexive Ehrhart reciprocity and gives a draconian-sequence formula; diagonal equality does not imply a two-variable polynomial identity. No new proof from that specialization.',
375368:'Row explicitly reports a published counterexample. Do not reproduce it as discovery or treat the open metadata as evidence; primary counterexample body remains unread here.',
375385:'Upho self-similarity and finitary definitions are not supplied. The nonlattice Petersen example is expressly outside the target; transferring it without a lattice-preserving construction fails.',
375386:'Upho and precise homogeneity are source-defined. Equal rank counts for all ranks is weaker than poset realization; the Petersen realization is already known and not a universal monoid construction.',
375488:'n must range over positive integers; n=1 makes clause 2 tautologically follow from clause 1 but does not give clause 3. Classical power identities might yield only a routine Waring adaptation; no full ring-uniform bridge verified.',
375573:'Literal formal q-series has an explicit positive quadratic exponent and products, so coefficient certificates are conceivable. Matching finitely many coefficients cannot prove the infinite identity; primary relation to the proved identity must be cleared before any investment.',
375684:'Literal bound fails at Delta=1 (K2 needs two list colors whereas log1=0), and Delta=0 is undefined. This is a domain/wording correction only; intended large-Delta logarithmic bound is not addressed.',
375864:'Quantifiers require a single g(k) for every digraph and a half-integral packing or bounded cycle-length residual. Vertex-disjoint counterexamples are not half-integral counterexamples; no bounded certificate route survives.',
376015:'Ceiling and singularity-envelope operators are not defined. Positive-mass theorem does not pass automatically to mass zero; analytic envelope stability would require a substantial dependency chain.',
376019:'Omega, collision/pocket dynamics, initial coordinates and measure are missing. A numerical shot is not a rigorous interval witness, and continuity at a regular witness must be established. No certification attempted.',
376020:'Full target is linear runtime including construction, not existence. Literal n=3 edgeless graph already conflicts with strict <n/2 for each color, a scope defect only; must consult exact primary exceptions, not claim a new counterexample.',
376139:'Row already describes its 36-vertex tournament refutation. Rebuilding the reported construction yields no discovery; matching orientation and second-neighborhood conventions also need source qualification.',
376245:'Sharp Euler sum normalization, barred-index sign convention and summation domain for double zeta (including convergence/regularization) are missing. Numerical depth checks would not settle all d.',
376287:'Row explicitly reports a Del Pezzo counterexample with group (C7 semidirect C3) times C2. Known refutation route, not a fresh full-scope target; versality definitions/body not cleared.',
376336:'Row explicitly states Hall–Paige was proved using finite simple group classification. Reproving it or its instances is ineligible; no investment.',
376400:'ell_(r,p) is merely named and the star is not defined. All r,t,k and real p>=2 matter; the known r=k-1 or t=1 cases and p<2 examples do not settle the stated scope.',
376554:'Observable a_j, Hamiltonian, state, and normalization are absent. Formula fit cannot be tested faithfully without them; all odd system sizes, not a finite fit, are required.',
377120:'The delta-set and asymptotic comparison definitions are absent. This is a uniform scale-saving analytic estimate, not a finite incidence count. No short full-scope route.',
377302:'Skein coefficient ring and specialization/genericity are not specified; central generation at p=0 does not extend by formal substitution. Full two-boundary-parameter problem would need substantial skein machinery.',
377466:'Primary Definition 3.16, Theorem 3.17 with rescaling proof and Conjecture 3.18 read. Forward classification depends on counts, but it does not force converse injectivity. Recovering real-class counts from abstract rings needs an intrinsic invariant, not just comparing chosen structure constants.',
377807:'Initial word w and recursive quasi-Engel words are not defined. Finite quotient solvability alone does not bound derived length for a finitely generated residually finite group; no full mechanism.',
378830:'Allowed shapes and K/fermionic formulas are unspecified. This large-rank identity cannot be screened as a literal computable equality without these definitions; prior large-rank X=M bodies uncleared.',
378968:'Yang–Baxter algebra, RSM-elements and rational power convention are absent. A scalar eigenvalue argument cannot substitute for nilpotent algebra identities at all ranks and rational alpha.',
379179:'Order polynomial and existential/selected linear t_W are undefined; wording assumes a linear map but does not specify it or its normalization. Type A/B constructions are given prior cases, not all finite Coxeter types.',
379218:'Primary Conjecture 5.3 and surrounding equivalence read. Source explicitly knows k=0 and k=n-1 and checked n<=15. Symmetry follows by reciprocal factors, but unimodality does not follow from arbitrary unimodal-product closure since factors 1+q^j have gaps. No full-scope route.',
379336:'All odd prime powers and line arrangements are required. Tangency/conic extremizers give upper examples, not the universal lower bound. Potential known finite-field Kakeya resolution must be body-checked; no novelty clearance.',
379486:'Weak relative hyperbolicity depends on coned-off Cayley graph convention, not strong relative hyperbolicity. Arbitrary Artin groups are the scope; two-dimensional source result alone cannot be generalized routinely.',
379783:'Primary Conjecture 0.3 and completeness/orientability conventions read. Minimum-volume theorem is a strong known-resolution lead requiring later Gabai–Meyerhoff–Milley body; no new mechanism and no successor body clearance here. Uniqueness must respect orientation conventions.',
379846:'Polytopal category, five operations and meaning of normal forms need definitions. Proving a restricted join/product case is already source territory; no all-homomorphism route.',
379872:'All torsion groups and fields are quantified. Hartley conjecture is a known-resolution lead, not cleared by memory; group-law to algebra-PI transfer requires primary prior theorem body. HOLD without it.',
380050:'Graph class must mean isomorphism classes: on labeled graphs an isomorphic-relabeling permutation trivially preserves hom counts, only a wording objection. For intended unlabeled graphs simultaneous permutation of source and target does not let one invoke fixed-test-graph cancellation directly.',
380104:'R(a,b,c) is not specified. Primary opening and Section 1 concern associated lower central quotients and cyclic differential forms, not this literal presentation. Cannot turn a missing-relation/generated-algebra mismatch into discovery; source qualification required.',
380271:'Displayed [200~ is a transcription artifact. With generic formal z,w the rational partition identity is meaningful; low-order coefficients are not a full proof. Macdonald/character-formula prior and source-body equivalence remain unread.'}
nonself={373359,373405,373621,373646,373957,374234,374370,374620,374630,374779,374957,374965,375385,375386,376015,376019,376245,376287,376400,376554,377120,377302,377466,377807,378830,378968,379179,379486,379846,380104}
scope={373234,373424,374779,375488,375684,376020,379783,380050,380271}
known={375368,376139,376287,376336}
rows=json.loads((P/'literal-records.json').read_text());out=[]
for r in rows:
 i=r['mathdb_id'];d={k:v for k,v in r.items() if k!='record'};d.update(title=r['record']['title'],source_url=r['record']['source_url'],disposition=('EXCLUDE_SOURCE_PROVED' if i==374620 else 'HOLD_REPORTED_PUBLIC_RESOLUTION' if i in known else 'HOLD_DEFINITION_OR_SOURCE_SCOPE' if i in nonself|scope else 'PARK_NO_FULL_SCOPE_ROUTE'),technical_judgment=notes[i],literal_record_read=True,complete_self_contained_statement=i not in nonself,scope_qualification_required=i in scope,ellipsized=False,accepted_credit=0,current_registry_cleared=False,whole_primary_body_read=False,full_dependency_audit=False,successor_body_clearance=False)
 out.append(d)
assert len(notes)==len(out)==50
(P/'dispositions.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n');(P/'proposals.json').write_text('[]\n')
print('50 dispositions; zero proposals; nonself',len(nonself))
