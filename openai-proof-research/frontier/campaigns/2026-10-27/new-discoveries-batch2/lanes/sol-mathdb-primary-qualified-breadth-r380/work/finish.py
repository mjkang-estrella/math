from pathlib import Path
import json,hashlib,datetime,re,itertools
R=Path(__file__).resolve().parents[1];L=R.parent
H=lambda b:hashlib.sha256(b).hexdigest()
def write(n,x): (R/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
reasons={
405819:('deep','Requires a uniform cryptographic construction and reductions under polynomial-time assumptions, explicitly without subexponential loss; toy circuits or stronger assumptions miss the target.'),
405821:('famous_hard','Consistency of the full first-order ZFR theory with an elementary self-embedding of V is a large-cardinal foundational problem; finite model checks cannot establish the requested consistency.'),
405822:('famous_hard','Equality of NP and existential-real complexity classes is a class-wide simulation problem; membership of particular geometric problems supplies no route.'),
405842:('famous_hard','The target requires polynomial time and space in log N for the entire dihedral HSP; known-style subexponential mechanisms and fixed N instances do not meet it.'),
405847:('famous_hard','A fixed positive exponent improvement for exact weighted APSP is the full fine-grained problem; approximation and restricted weights do not qualify.'),
405855:('famous_hard','Requires one asymptotic binary code family with constant query count, polynomial blocklength and constant corruption tolerance; isolated codes or growing query count miss scope.'),
405858:('deep','Exact rational SDP feasibility in the Turing bit model includes weakly infeasible boundary cases. Numerical interior-point success is not a decision algorithm for this scope.'),
405871:('famous_hard','Uniform polynomial-time unknot recognition is requested; certificates or successful bounded diagram recognition do not give the required algorithm.'),
405882:('deep','Relative consistency of strongly compact and supercompact cardinals is a foundational comparison. Conditional consequences of an added Ultrapower Axiom do not settle this unqualified statement.'),
405897:('famous_hard','Exact square-lattice site threshold, not its numerical approximation or the bond threshold, is requested; no exact identity mechanism is available.'),
405900:('deep','Universal nonamenable II_1 factor subfactor statement needs operator-algebraic structure. Special factors containing L(F_2) do not settle every factor.'),
406239:('inaccessible','Plausible bounded graph inequality, but both cited WoTW hosts timed out. Original definitions, small-order conventions and internal examples remain unread. No sweep or novelty claim made.'),
406241:('inaccessible','Original WoTW body inaccessible by timeout. In particular singleton graphs, exponent-zero convention, induced path order and non-induced C4-free indicator require primary verification before a purported small counterexample.'),
318661:('deep','Primary cycle subsection distinguishes homogeneous Gamma_m from Gamma-prime_m; table supports the claimed homogeneous degrees through 11. Radical elimination with cancellation and irreducibility is not a short degree proof; no finite degree table is promoted.'),
319677:('deep','Full boundary n=2k-1 subcube extremal theorem for all k is required. The proposed central family supplies a lower bound, not an upper bound for every irredundant family.'),
320851:('known_source_resolution','Primary Theorem 1.2 explicitly gives f(m)=floor(sqrt(4m+1))-1 and says it verifies the conjecture. Contradictory database open note cannot justify rediscovery.'),
321668:('deep','Primary Conjecture 6 is verified there for d<=7 and Proposition 8 proves |Gamma|<=2. Larger finite minors or singleton optimization are already covered helpers; arbitrary subset determinant lower bounds remain substantial.'),
323613:('deep','Exact weighted Hajnal-Szemeredi threshold for every r and t needs a universal clique-factor theorem. Matching obstructions and approximate bounds do not establish equality.'),
324505:('famous_hard','General crown crossing-number formula needs a lower bound over all drawings, not the explicit upper construction or already treated n=5.'),
325282:('known_source_resolution','Primary Theorem 2.2 proves precisely the displayed characteristic polynomial by scaling the path distance matrix and applying Lemma 2.1. Proof section read; no independent dependency audit.'),
325330:('deep','Optimal complementary chi-bounding function is a hereditary graph-class extremal assertion. A single graph realizing floor(8x/5) cannot supply the universal upper bound; domain/heredity cannot be silently dropped.'),
326185:('park_no_short_route','Primary Definition 1.1 normalizes both vectors before polarization. Lemma 3.21 already supplies a supremum-norm failure; it does not refute the iff. Conjecture 3.22 needs phase covariance for every pair and phase to force additivity. Ordinary unnormalized Jordan-von Neumann polarization cannot be substituted.'),
326304:('famous_hard','All ell high-girth extremal growth is requested, a major general construction problem. The ell=2,3 or other special constructions give parameter instances only.'),
326508:('known_source_refutation','Primary Theorem 2.6 and its complete local proof construct a strict energy-lowering competitor for an Euler-Lagrange minimizer when ell/h>sqrt(2)-1/2. This already contradicts the conjunction; lower-ratio questions are not new variants here.'),
327330:('deep_status_correction','Primary Conjecture 5.2 remains posed and the following text says all counterexample attempts failed. The database refuted tag reverses that sentence. Normal realization and O_p-prime(H)=1 are essential; no small full-scope mechanism survives.'),
327375:('deep','Primary conjecture paragraph expressly explains why Tuza 1-critical families are not maximal intersecting and hence not counterexamples. Must enforce maximality, not merely pairwise intersection or criticality.'),
327422:('park_no_short_route','Primary Conjecture 8 has both h-plus and h-minus equalities for all a,b, not just coprime parameters. Section 4 supplies cyclic-shift reductions and Example 9. A known shuffle theorem or standard area enumerator cannot be cited without proving applicability to these exact frontier statistics.'),
328034:('deep','Need maximality among all p^k-central subspaces of the specified cyclic algebra, not just the already shown centrality or maximality among monomial spaces. Ground-field hypotheses need primary expansion before an attempt.'),
328554:('known_source_refutation','Primary Second Conjecture 1.4 is explicitly disproved in section 3 by a set of Hausdorff dimension >1 whose blowups lie in a closed cone containing no plane. Introductory body read; complete fractal proof/dependencies not audited.'),
329290:('wording_and_deep','Record incorrectly calls D the smallest dimension. Primary p17 defines the largest realizable dimension; Corollary 6 already gives all lower dimensions >=2. Examples 6 and 7 warn against easy cardinality shortcuts. Intersecting linear tightness equations does not preserve rank-one frame operators, so generic Gram interpolation supplies no proof of the actual conjecture.'),
331661:('deep','Exact topological Tverberg threshold across prime powers and all remaining r,d needs topology of multiple intersections. Known failures at some dimensions or finite simplex maps do not give the proposed exact formula.'),
332757:('vague_deep','Effective evaluation of all genera and insertion counts from localization relations needs a specified terminating reconstruction algorithm and dependency theory. The record delegates definitions to the paper and offers no bounded elimination route.'),
333447:('known_source_resolution','Primary p2 explicitly says Conjectures 1 and 3 are proved and section 6 proves exactly the two-row NPS sum via symbolic summation. Treating the displayed conjecture label as an unanswered question would rediscover the paper result.'),
333693:('deep','Both existential knot claims demand global width minimality, expressly unproved for the proposed embeddings. Computing width/trunk of those embeddings cannot prove no better embedding exists.'),
334049:('wording_exclusion','Primary Conjecture 3.11 explicitly requires r>=1/(1-alpha), equivalent to alpha<=1-1/r. The record omits it. The 1x1 identity at delta=1 would refute only that omission and yields no discovery credit. Actual restricted conjecture remains unqualified.'),
335229:('park_no_short_route','Strict D(G,2)<2 for each finite outerplanar G is stronger than a non-strict defect-two coloring; fan limits do not disprove a strict finite assertion. No source-qualified perturbation decreasing every saturated vertex has been obtained.'),
335279:('deep','All 2-connected graphs and the ceiling square-root bound are requested. Cycles or complete bipartite test families do not establish a symmetry-breaking construction for all graphs.'),
335472:('deep','Capacity equality for every closed symplectic M, stable nondisplaceable X, R>0 and winding ell requires both capacity bounds under full Floer-theoretic hypotheses. Torus equality is already prior scope.'),
335908:('deep','For every gamma>0 and sufficiently large divisible n, the codegree matching conclusion is asymptotic. A small 3-graph failure or threshold rounding cannot refute its quantifiers.'),
336275:('park_no_short_route','Must forbid butterfly copies in every (n-1)-trace for every n>=5. The distinct Tr(n,B) formula does not settle this. No short compression/injection or structural obstruction is source-qualified.'),
337037:('deep','Full subcubic star edge coloring with six colors forbids bichromatic length-four paths/cycles, not just proper coloring. Finite search successes below degree three do not prove the uniform assertion.'),
337098:('park_no_short_route','Primary paper states the positivity-plus-unimodality strengthening and proves only specified small-a cases using KOH decomposition. Need arbitrary positive a,b,c,d with a smallest and ad=bc; generic Gaussian unimodality does not survive subtraction automatically.'),
337514:('vague_deep','Record leaves s(H) undefined. Likely bipartition-size interpretation must be confirmed from primary before use. Even with it, a formula for every connected bipartite H is an extensive Ramsey theorem, not small-k checks.'),
339632:('deep','Minimum over every r>=2 for each p>=4 needs global Folkman structural bounds. Finding equality at a few p,r or a single color-critical construction supplies no general minimum.'),
339881:('deep','Exact modular Erdos-Burgess constant for all n couples nonunit valuation constraints to unit-group Davenport constants. CRT and known prime-power/squarefree cases are not a new general upper-bound proof.'),
340202:('deep','Every n-atom in every torsion-free group is required; unique-product assumptions and the known n=1 case cannot be silently added. No small exact nonunique-product construction with certified atom minimality supplied.'),
340501:('known_source_refutation','Primary Example 1.3 already prints a signed K7 Laplacian and a violating top-four eigenvalue sum; following examples add order-eight failures. Smaller or exact algebraic certification would be adaptation of a printed refutation.'),
341325:('deep','Primary Conjecture 1.19 is an iff: necessary bounds in Theorem 1.20 and small-p sufficient constructions are not full sufficiency. Pin(2) equivariant stable homotopy introduces a large dependency burden, with no short route.'),
341738:('source_internal_exclusion','Primary Remark 1.3 already states that the 3-prism has no required coloring. Disjoint union with an isolated vertex meets the literal >=7 condition and inherits impossibility. This is a routine source adaptation and possible missing-connectedness issue, not a discovery; no connected corrected conjecture proposed.'),
343315:('known_prior_resolution','Primary p3 says Lu proved this for all r,m, not merely sufficiently large m. Retained Lu arXiv:1803.08653 Theorem 1 gives exactly lambda(H)<=m s^(-r), equality iff integer s and complete r-graph up to isolates. It subsumes the full stated r>=3 scope.')}
records=json.loads((R/'records.json').read_text());assert len(records)==len(reasons)==50
prov=json.loads((R/'source-provenance.json').read_text());pmap={e['key']:e for e in prov if e.get('usable')}
# source excerpts are flat derivatives; no historical or corpus copies.
intervals={318661:(890,952),320851:(30,90),321668:(461,547),325282:(135,202),326185:(40,77),326508:(260,320),327330:(393,426),327375:(120,160),327422:(618,712),328554:(31,82),329290:(929,989),334049:(750,780),340501:(45,125),341325:(415,465),341738:(53,75),343315:(115,133),'lu':(140,182),333447:(54,96),337098:(20,90)}
ex=[];versions=[]
for n,(lo,hi) in intervals.items():
 p=R/'work'/(str(n)+'.txt');a=p.read_text().splitlines();ex.append('\nID '+str(n)+' lines '+str(lo)+'-'+str(hi)+'\n'+'\n'.join(f'{j+1}: {a[j]}' for j in range(lo-1,min(hi,len(a)))))
 versions.append({'key':n,'version_header':[l.strip() for l in a[:100] if 'arXiv:' in l],'pdf':pmap[str(n)]['path'],'body_read_scope':'selected definitions/conjecture/nearby results only; not entire paper'})
(R/'primary-excerpts.txt').write_text('\n'.join(ex)+'\n');write('source-versions.json',versions)
d=[]
for x in records:
 n=x['mathdb_id'];kind,why=reasons[n];primary=str(n) in pmap
 d.append({'mathdb_id':n,'title':x['title'],'canonical_url':x['canonical_url'],'statement':x['statement'],'statement_sha256':H(x['statement'].encode()),'record_sha256_canonical_json':H(json.dumps(x,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()),'source_url':x.get('source_url'),'source_name':x.get('source_name'),'disposition':kind,'reason':why,'evidence_level':'primary_body_selected' if primary else 'literal_record_review_only','primary_refs':[pmap[str(n)]['path']] if primary else [],'proof_section_read':n in [325282,326508], 'full_dependencies_audited':False,'bounded_novelty':'not cleared; exclusions are source/prior objections, all other rows parked','proposal':False,'credit':0})
write('dispositions.json',d);write('proposals.json',[])
# Two tiny rejection checks AFTER source-internal examples. Neither is a candidate search.
edges={(0,1),(1,2),(0,2),(3,4),(4,5),(3,5),(0,3),(1,4),(2,5)}
def good(bits):
 for v in range(6):
  same=sum(bits[v]==bits[w] for w in range(6) if tuple(sorted((v,w))) in edges)
  if (bits[v]==0 and same>1) or (bits[v]==1 and same<1):return False
 for path in itertools.permutations(range(6),4):
  if all(bits[v]==1 for v in path) and all(tuple(sorted((u,v))) in edges for u,v in zip(path,path[1:])):return False
 return True
valid=[bits for bits in itertools.product([0,1],repeat=6) if good(bits)];assert valid==[]
write('bounded-checks.json',{'status':'rejection checks only','primary_first':True,'guard':{'path':str(L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'),'AS_bytes':536870912,'group_RSS_bytes':536870912,'CPU_seconds':210,'wall_seconds':230,'raised':False},'checks':[{'id':341738,'graph':'triangular prism','vertices':6,'edges':sorted(edges),'assignments':64,'valid_colorings':0,'isolated_vertex_extension':'Adds one vertex, graph remains subcubic and has 7 vertices; restriction of any valid coloring would color prism. Already printed obstruction, zero credit.'},{'id':334049,'matrix':[[1]],'r':2,'delta':1,'polynomial':'nonzero scalar multiple of x-1','maxroot':1,'claimed_bound':'1/2','source_condition_satisfied':False,'credit':0}],'hard_sweeps':0,'candidate_searches':0,'accepted_results':0})
# Read all bounded history inputs without treating them as mathematical clearance.
history=[]
for name in ['accepted-exclusions.json','historical-dispositions.json']:
 p=L/'root-mathdb-accepted-exclusions-r304'/name;b=p.read_bytes();obj=json.loads(b);hits=[n for n in reasons if re.search(r'(?<!\d)'+str(n)+r'(?!\d)',b.decode())];history.append({'path':str(p),'sha256':H(b),'exact_id_mentions':hits,'limitation':'Cached index only; family-scope screening, not exhaustive or current prior clearance.'})
write('history-scope-screen.json',history)
write('provenance.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'role':'solo research worker; no children','coverage_baseline':983,'reviewed_literal_records':50,'primary_body_selected':sum(e['evidence_level']=='primary_body_selected' for e in d),'proof_sections_read':2,'full_dependency_audits':0,'novelty_clearances':0,'briefs':0,'mathdb_requests':0,'counts_unchanged':{'additional':9,'total':39,'next':40},'restrictions':'No GitHub/Google/ScienceDirect/browser/account/public mutation/messages/Lean/manuscript work. Search-service results may contain excluded-domain links; none opened or used as evidence.','input_policy':'flat immutable absolute references; corpus chunks verified in place'})
(R/'failures.md').write_text('''# Failures and limits

Both WoTW cited hosts timed out; no body, definitions or internal examples verified. The web fetch of the first host also returned a timeout; this was not a 403/429/challenge retry. No MathDB requests.

An operator-typed arXiv identifier for 327375 was wrong (1402.4356, quantum optics). It was excluded immediately on title inspection. Fetching the correct 1402.7158 initially overwrote the misnamed local PDF. The extraction precondition then failed nonzero on the old hash. The correct PDF was renamed; the identical wrong-source bytes were restored from its original URL and hash-checked. Both retained with explicit provenance; the unrelated paper supplies no mathematical evidence. The failure was not suppressed. Poppler emitted a recoverable xref reconstruction warning on one PDF; text layout alone is not a formal proof audit.

Initial web responses were delivered as extracted text before their local snapshot hash could be frozen. They are navigation leads only, never the basis of a proposal or a proof. All relied-on primary PDFs were retained and hash-bound before local extraction. Initial intake DECISION/administrative bindings and previous freeze-helper code were read to identify inputs before the freeze; no reserved scientific statement was read before the successful input freeze.

Successor searches were bounded and uneven; no absence of prior art is inferred. No current proof-registry clearance was attempted because no source-qualified substantive candidate survived. No full dependency audit or mathematical correctness certification of a published proof is claimed. There are no inaccessible-source novelty clearances and no manufactured briefs.
''')
(R/'SUMMARY.md').write_text('''# r380: fifty literal statement dispositions, no proposals

Exactly the r379 reserved fifty were reviewed against literal r301 records. Freeze verified the intake manifest, its actual originals, bound r301 inventory and twenty corpus chunks IN PLACE, r304 accepted/exclusion/history inputs, and r363 Cayley exclusion. Reservation/queue exact equality and disjointness from 983 reconciled IDs and 372627/372628/368940 passed. No other active breadth reservation is recorded. Flat references only; no corpus or recursive history copies.

Fifty individual statement texts and SHA256s appear in dispositions.json. Eighteen have selected primary-body review; two local proof sections were read (Sills-Wang and Anand), with no complete dependency audit. The retained Lu theorem is an additional primary dependency, not another covered record. Source body resolutions/refutations block 320851, 325282, 326508, 328554, 333447, 340501 and 343315. The last also has Lu's exact full-scope prior theorem retained/read. Open labels and contradictory parser status notes were not novelty evidence.

The mixed-root record omits the source's r>=1/(1-alpha) restriction. A 1x1 failure only corrects that omission. The subcubic paper already prints the uncolorable prism; adding an isolated vertex is a routine adaptation, excluded by the Cayley lesson. Factor-poset D is the largest realizable dimension in the primary, not the smallest as the record says. No discovery is credited to any wording repair. Phase covariance uses normalized polarization, and its printed supremum-norm failure does not refute the characterization. The maximal-intersecting-family source expressly rejects the tempting Tuza construction as outside scope.

Both WoTW hosts timed out. Their two records remain literal-record-only, with no computations used to manufacture survivors. Other famous, deep or inadequately specified targets are individually parked with quantifier/scope objections. Two tiny source-first rejection checks ran under the fixed guard; no hard sweeps. No substantial full ordinary proof or counterexample survived to preserve for separate review, so proposals.json is empty (zero of at most three briefs).

This reports fifty reviews for root reconciliation only; it does not modify coverage or any shared ledger. Counts stay 9 additional / 39 total / next 40. MathDB requests zero. No Lean, manuscript or public work. Failures and timing limits are explicit in failures.md. The separate final verifier must rehash actual originals, all corpus chunks, exact statement sets and the exact output inventory.
''')
