import pathlib,json,hashlib,datetime
O=pathlib.Path(__file__).resolve().parent;D=json.load(open(O/'extracted.json'));sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
notes={
351696:'General subdivisions of minimum-degree>=3 kernels remain outside the stated proved cases; no global edge-resolving-set construction obtained. Need a subdivision-stable bound with edge distances.',
351709:'Requires asymptotic orbit separation under SL(2,Z), not merely counting permutations/origamis. No feasible invariant separating super-exponentially many orbits obtained.',
351726:'Exclude from discovery: primary Theorem1.1 gives product-proper 3-labellings for every nice graph; equal incident multisets imply equal products, so the exact multiset claim follows. Source also cites Vuckovic2018 direct proof. Full-scope explicit bridge; no new Lean needed.',
351776:'Field-theory deformation classes and equivariant TMF anomaly twist require primary definitions and extensive missing formal infrastructure; statement-only hold.',
351819:'Need source satisfying-cycle equations and definition of exceptional (2,2,...) before any zero-coordinate test; not checked by treating arbitrary tuples as cycles.',
351874:'Adelic fibration density is not an elementary rational density assertion; need full class P and local split-fibre hypotheses. No feasible exact mechanism.',
351887:'Odd colour subgraphs allow isolated vertices outside their support; bounded ordinary edge-colouring tests would not establish the source odd-chromatic-index condition. Primary definitions pending.',
351949:'Displayed source graph and inductive strong-I class required. Minimum-order question needs both construction and exclusion below it; figure/body not reviewed.',
351953:'Generic trace fibres, norm-curve components and adjoint torsion all need literal algebraic/topological definitions; no feasible semantic Lean bridge identified.',
351989:'Measure-space cardinality/total-mass issues could give wording-only failures; not eligible absent source-scope verification. No discovery claimed.',
351994:'Meaning of V~|x|+1 and permitted maps is source-dependent; an arbitrary f can encode volume tautologically. Primary definitions required; no wording correction credited.',
351995:'The unspecified Diophantine equation and generated tree must be recovered before a uniqueness search; analogous Markov uniqueness not assumed solved.',
352000:'Metric-distortion equality needs an optimal Euclidean embedding and lower bound, beyond finite cosine calculations. Primary graph class and antipodal proviso not checked.',
352001:'Need spectral cosine normalizations and full distance-regular graph class. No bounded eigenvalue sample treated as resolution.',
352031:'Exclude known resolution: source Conjecture14, Theorem15 proof, Corollaries16-17 give connectivity/degree diameter bound; source explicitly concludes the conjecture for all k, with cycles/small k handled separately. Proof-body excerpts read, not whole paper audited.',
352038:'Candidate full exact refutation: delta=(55+sqrt3049)/2, root x^2-55x-6, actual periodic CF stream of period85. Distinct coefficient set has exactly six values above8; seventh-largest8 violates 55/7. Full literal Lean source_refutation, strict fresh replay and 31-declaration audit pass. Zero credit pending independent fidelity/significance/prior review and root acceptance.',
352122:'Possible articulation-point product inequalities suggest routine block containment, but no primary definition of subgraph counting convention was recovered. No routine or novel theorem asserted.',
352134:'Exclude known counterexample: source Theorem7 and Lemmas2-6 construction/proof bodies disprove for every ell>=11 via dense-girth graph substitutions and non-Hamiltonian triangulation gadgets. No new discovery.',
352139:'Set-wise intersections differ from sharing edges. Need full all-k,t family bound and maximum classification; no full-scope mechanism identified.',
352181:'Quadratic tournament Ramsey bound requires uniform embedding of all subdivisions; finite small tournaments would be parameter cases only. Primary later-resolution screen pending.',
352233:'Asymptotic O(sqrt g) claim cannot be refuted by g=0 endpoint; excluded as a mechanism, not declared a known theorem. Need uniform genus orientation argument.',
352239:'Inherited adjacent Omega two-dimensional classification found; its dossier explicitly excludes Conjectures1.4/5.6/5.8. Do not relabel it as full resolution of this canonical-subspace claim. No new investment after inherited match.',
352240:'Same inherited pseudo-Paley two-dimensional-classification family; exact-two maximum cliques needs additional max-clique subspace theorem. No full-scope bridge established.',
352241:'Inherited adjacent Omega result settles source Conjecture5.9 only; dossier states full count Conjecture5.8 requires Conjectures1.4 and5.6 as well. No duplicate credit or exact full-count resolution asserted.',
352243:'Need exact blow-up construction and competing planar induced-cycle count for all sufficiently large n. No endpoint correction or bounded instance offered.',
352282:'Literal action needs primary recovery: point-agreement and action-on-lines lead to different EKR problems. A putative easy stabilizer bound is withheld as an unverified scope bridge.',
352283:'Uniform fitting-height bounds require full ordered-identity definition and all finite solvable groups; abelian examples cannot settle it. No exact mechanism.',
352359:'Class of diffeomorphisms and smooth root-system quantifiers not explicit enough in paraphrase; source needed. No flow uniqueness correction counted.',
352385:'Need literal Sylow branching character coefficient; small partitions require representation-semantic bridge. No finite arithmetic proxy used as theorem.',
352413:'Primary definitions/Theorem3.1 proof and Conjecture3.5 read. One/two-clique cases have elementary multidigraph realizations; first difficult three-cover case has arithmetic cycle-count constraints, but infeasibility for one maximal cover does not exclude all nonmaximal minimum covers (source Remark2). Park global contraction/three-cover gap; no counterexample.',
352443:'Primary definitions and Conjecture4.1 read. Exact tree state-DP checked by independent brute subsets n<=10; 1600 deterministic tree trials/4782 leaf pairs and separate double-star formula grid6400 yield maximum gap1. No proof; need all-tree coefficient comparison controlling largest modes after leaf deletion.',
352461:'Closed-convex embedding dimension requires geometric realization and dimension lower bound above n; generic code enumeration insufficient. No source-body or feasible Lean mechanism.',
352482:'Theta-series lattice semantics and formally-unimodular condition needed before testing secrecy-function derivatives. No endpoint or parameter variant credited.',
352591:'Geometric disjointness must include intersection conventions and straight-line embedding assumptions; no graph-only edge-disjointness surrogate accepted.',
352610:'Determinacy/inner-model conditional existence requires a precise metatheoretic model framework; no feasible Lean endpoint in this pass.',
352611:'LSA extender-model existence likewise requires full source fine structure; no reduction to a finite/model-theoretic toy claim.',
352647:'Exact added-edge sets F_G,F_H must be recovered; no domination-number search on ordinary Cartesian products substituted. General claim would imply Vizing; no endpoint.',
352659:'Morava K-theory dimension lower bound equality needs topology and spectral-sequence bridges absent from present infrastructure. No numerical binomial proxy theorem.',
352666:'Sidon-polynomial definition and permutation-equivalence scope needed before finite-field search. No conclusion from polynomial functions modulo x^p-x without source definitions.',
352698:'Morita-equivalence unit weak equivalence requires contextual-category generating cofibration semantics. No elementary strictification argument or feasible complete Lean bridge obtained.'}
primary={'351726':('351726.pdf','Definitions, introduction, Theorem1.1 and proof overview; direct multiset/product bridge, not full construction proof audit'), '352031':('352031.pdf','Conjecture14, Theorem15 proof and Corollaries16-17 bodies, earlier Theorem3 statement; its long proof not fully audited'), '352038':('352038.pdf','AppendixA LemmasA.1-A.3 proofs, Theorem4.4 proof, CorollaryA.4 proof and ConjectureA.5; page28 visually checked'), '352134':('352134.pdf','Theorem1/7 and Section2 Lemmas2-6 definitions and construction/proof bodies'), '352413':('352413.pdf','Section1.1 graph/cycle definitions, Section3 Theorem3.1 proof, Conjecture3.5 and Remark2'), '352443':('352443.pdf','Introduction dominating set/unimodality/largest-mode definitions, ConcludingRemarks Conjecture4.1; high-degree proof not fully audited')}
results={}
for i,x in D.items():
 d=x['record'];p=primary.get(i);status='candidate_formal_refutation_pending_independent_review' if i=='352038' else ('excluded_known_full_scope' if i in ['351726','352031','352134'] else 'held_no_solution')
 results[i]={'mathdb_id':int(i),'title':d['title'],'canonical_url':d['canonical_url'],'statement':d['statement'],'source_url':d['source_url'],'provenance':{k:v for k,v in x.items() if k!='record'},'raw_file':f'raw/{i}.jsonl','inherited_matches':[],'history_check':'ID search of prior campaign markdown/JSON plus title/author probes in history-filtered.txt and title-history.json; administrative inventory matches not technical reviews; bounded nonfinding only','new_review_depth':{'literal_statement_read':True,'primary_body_review':p[1] if p else 'none; primary definitions and proof bodies unread','source_sha256':sha(O/'sources'/p[0]) if p else None,'source_receipts':'receipts.jsonl' if p else None,'formal_endpoint':'MathDB352038.source_refutation' if i=='352038' else None},'outcome':status,'accepted_credit':0,'attempt_and_remaining_gap':notes[int(i)]}
 if i in ['352239','352240','352241']:results[i]['inherited_matches']=[{'kind':'adjacent_public_registry_theorem_not_full_scope_clearance','path':'2026-10-26/new-discoveries/lanes/pi-euler-turan-final-review/fresh/trureturing/Problems/asgarli-yip-2021-pseudo-paley-two-dimensional-cliques.md','scope':'Conjecture5.9 only; source Conjectures1.4/5.6/5.8 explicitly outside it','action':'retain scope limits; no duplicate route pursued'}]
assert set(results)==set(map(str,json.load(open(O/'reservation.json'))['ids'])) and len(results)==40
(O/'results.json').write_text(json.dumps(results,indent=2,ensure_ascii=False)+'\n')
ctx=[]
for p in [O.parents[1]/'ledger.json',O.parent/'ledger.json',O.parents[1]/'prior-campaign-context.json',O.parents[3]/'2026-10-26/new-discoveries/ledger.json']:
 if p.exists():
  d=json.load(open(p));ctx.append({'path':str(p),'sha256':sha(p),'accepted':d.get('accepted'),'note':'Read administrative context, unchanged; contains accepted families and exclusions/holds; user latest decisions additionally retained.'})
(O/'context-read.json').write_text(json.dumps(ctx,indent=2))
