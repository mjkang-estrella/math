import pathlib,json,hashlib,re,datetime
D=pathlib.Path(__file__).resolve().parents[1];C=D.parent;B=C.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
# Fully ingest the required context without copying the historical trees.
ctx={}
for p in [B/'ledger.json',C/'ledger.json',B/'prior-campaign-context.json']:
 b=p.read_bytes();o=json.loads(b);ctx[str(p)]={'sha256':sha(b),'bytes':len(b),'top_level_keys':list(o) if isinstance(o,dict) else None}
(D/'outputs/context-read.json').write_text(json.dumps(ctx,indent=2)+'\n')
x=json.loads((D/'extracted.json').read_text())
# outcome, review depth, disposition, exact mathematical coverage, unresolved obligation, primary evidence
notes={
'330692':('parked','primary definitions and characterization; companion formulas and open conjecture read',
 'Source Conjecture 3.11 is retained as the right-hand inequality of Elizalde–Moore Conjecture 7.4. No counterexample found. Source only settles k = 2.',
 'All permutations of lengths 3 through 9, every k from 2 through n; exact source-derived minimal-alphabet counts. Definition 3.5 invalidity is checked directly from the minimal negative segmentation. 409110 permutations total. All cumulative inequalities hold.',
 'Prove positivity of the cumulative binomial transform of the difference between Lemma 6.7 and Theorem 6.9, or find a violation beyond this finite range. This is not a literal Lean proof of the infinite-word semantics.',
 ['330692.pdf','signed-later.pdf'],['outputs/signed3.json','outputs/signed4.json','outputs/signed5.json','outputs/signed6.json','outputs/signed7.json','outputs/signed8.json','outputs/signed9.json']),
'330859':('parked','primary Conjecture 5.1 and surrounding exact bounds read; sustained finite search',
 'No violation; a Walsh transform of a subset of size m_n is the exact finite quantity. Exhaustive affine reduction improves the diagnostic coverage to every n <= 5.',
 'Direct exhaustive subsets n = 1,2,3,4: 2,4,56,4368 cases. For n = 5, affine normalization of the 11-element complement covers affine dimensions 4 and 5 in 462 and 65780 cases; minima are 78 and 82. A set of 11 points has affine dimension >= 4, and every such set contains an affine basis, so those two dimensions cover all cases. Seeded swap/annealing searches n = 5,6,7 use 80 seconds each; exact counts and minima are in outputs/sylvester*.json. No claim of exhaustive n >= 6.',
 'Need a lower bound for all subsets at n >= 6; the affine-basis normalization leaves too many free columns. Parseval alone gives a substantially weaker bound. No source theorem supplies this universal minimization.',
 ['330859.pdf'],['outputs/sylvester1.json','outputs/sylvester2.json','outputs/sylvester3.json','outputs/sylvester4.json','outputs/sylvester5.json','outputs/sylvester6.json','outputs/sylvester7.json','outputs/sylvester5-affine.json']),
'330904':('excluded_source_proved','primary conjecture, Theorem 2.1 and explicit proof read',
 'Wang’s source explicitly proves Conjecture 1.1 at the end of Section 2 using A3(n) = sigma(3n+2)/3, multiplicativity and Euler’s theorem. The displayed k0 formula is part of that proof. This is already solved in the cited paper.',
 'No new numerical search justified for an explicitly source-proved statement.',None,['330904.pdf'],[]),
'331559':('parked','primary UPC definition, Conjecture 3.1 and verified-range theorem read',
 'UPC means exactly one cycle of each length 3 through order, not the misleading MathDB description as simultaneously r-pancyclic for every r. The source attributes the conjecture to Shi (1986), despite the reservation metadata year 2015. Its low-chord ranges and Markström’s search are already known.',
 'All 1252 nonempty atlas graphs of order <= 7; exact simple-cycle counts. Only the triangle and the five-vertex six-edge graph are UPC in this range. Neither has four extra edges. This is BELOW published searches, not an advance beyond them.',
 'A competitive new search needs canonical Hamiltonian chord configurations beyond the cited published order/chord bounds; no such exhaustive search completed here.',
 ['331559.pdf'],['outputs/atlas.json']),
'331859':('excluded_source_ingredient_bridge','primary terminal-path definition, Conjecture 11, Theorem 10 proof; companion Lemma 6 proof and Figure 4 read',
 'A genuine intended-scope refutation was found, but the decisive (5,5,5) spider and b = 4 are printed in Bonato–Lidbetter. Adding b(3 disjoint P2) = 4 is elementary; recommend zero credit under the source-ingredient rule. No Lean endpoint is nominated.',
 'Structured spiders with t = 3, cores (k,k,k) and (k-1,k+1,k+1), sorted terminal orders in 1..2k+3, forest capacity filter and explicit ball-cover search. Stopped after the first failure: k = 4 after 30 tested cases, k = 5 after 32. Separate verifier checks all 216 three-round forest sequences and all ambient vertices. See spider-proof.md for full ordinary proof.',
 'No mathematical gap in the ordinary refutation; novelty fails because the companion prints the decisive value and construction. Root decides eligibility.',
 ['331859.pdf','burning-spiders-arxiv.pdf'],['outputs/spider4.json','outputs/spider5.json','outputs/spider-verified.json','outputs/spider-proof.md']),
'334534':('excluded_published_refutation','primary Conjecture 10; later Theorem 1.5 and construction/proof body read',
 'Bonamy–Morrison–Scott, Partitioning the vertices of a torus into isomorphic subgraphs, Theorem 1.5 refutes even the stronger divisibility hypothesis |H| divides |G|. Set G = C_k^m in that theorem. It is vertex-transitive and (G)^n = C_k^(mn), so no power partitions. Thus this is not a new lead.',
 'No finite-power nonpacking check could disprove the existential quantifier over all powers; rely on the published obstruction.',None,['334534.pdf','torus.pdf'],[]),
'327233':('excluded_source_proved','primary Conjecture 2.1, Theorem 2.2 and inverse-map proof structure read',
 'The source’s main theorem is precisely the statistic-vector-preserving bijection between surjective pistols and irreducible k-shapes. Proposition 4.3 proves its two maps inverse. The conjecture is an explicit corollary of the source, not open.',
 'No independent search needed for the already-proved vector equality.',None,['327233.pdf'],[]),
'328307':('parked','primary Definition 6.1, Conjecture 6.2 and chordal special case read; exact finite witnesses',
 'No obstruction in the atlas range. We construct an acyclic orientation, which automatically has no directed odd cycles, then assign each outgoing arc a layer so outgoing layer labels form a prefix and incoming labels are distinct.',
 'All 1252 nonempty atlas graphs through order 7 have a recorded acyclic orientation and ordered path-layer decomposition. Exhaustive vertex orders tried until a witness is found, then exhaustive outgoing-layer permutations with incoming collision pruning. Witnesses are stored per graph; no negative certificate is claimed.',
 'Need a full-scope existence proof or graphs beyond order 7; arbitrary acyclic orientations can fail the layer assignment, so no greedy universal argument was obtained.',
 ['328307.pdf'],['outputs/sequential.json']),
'328610':('excluded_published_proof','primary conjecture and Méroueh Theorem 1.3 plus proof structure/end read',
 'Méroueh, Lubell mass and induced partially ordered sets, arXiv:1506.07056, Theorem 1.3 states the exact uniform bound for every induced-P-free family. It explicitly identifies Lu–Milans as the conjecture being confirmed.',
 'No finite-family sweep resolves or refutes a statement with an unspecified uniform constant for each poset; the published theorem settles it.',None,['328610.pdf','lubell-proof.pdf'],[]),
'328750':('excluded_published_proof','primary sign conjecture; Renteln eigenvalue recurrence and Corollary 12 proof read',
 'Renteln, On the spectrum of the perfect matching derangement graph, Theorem 11 gives the sign times a nonnegative sum; Corollary 12 explicitly proves Conjecture 5. The note added records an independent simultaneous proof by Ku and colleagues. No novelty.',
 'No spectrum search justified after the full published sign theorem was recovered.',None,['328750.pdf','matching-proof.pdf'],[]),
'328890':('parked_hard_scope','primary Conjecture 4.1 and conditional larger-sieve theorem read',
 'This is an inverse-sieve statement with epsilon-dependent implicit constants and polynomial complexity. It is analytic and asymptotic in N despite the finite-discrete metadata filter. No finite certificate mechanism survives the unrestricted constants.',
 'No numerical sweep: finitely many N cannot refute the uniform assertion with unknown constants.',
 'Need the full inverse-sieve structural theorem or an asymptotic counterexample family with quantified failure for every complexity constant.',
 ['328890.pdf'],[]),
'329072':('parked_hard_scope','primary Conjecture 1.1, approximate-decomposition thresholds and related theorem statements read',
 'This is the exact clique-decomposition minimum-degree threshold conjecture, with an eventual n0(r), not a single finite graph assertion. The source’s approximate threshold results do not settle the exact boundary.',
 'No bounded graph search could refute existence of n0. No asymptotic obstruction family below or at the exact degree boundary was found.',
 'Need a genuine infinite family violating the exact threshold or a new absorption/fractional-decomposition argument. Lean cost is high.',
 ['329072.pdf'],[]),
'325227':('excluded_source_proved','primary Conjecture 1.3, Theorem 1.4 and classification proof portions read',
 'Anthony–Picollelli Theorem 1.4 completely classifies D-unique complete multipartite graphs and explicitly settles this bipartite conjecture. The paraphrase’s final sentence understates the theorem; it proves uniqueness among arbitrary graphs.',
 'No search justified for source’s explicit main theorem. This is also mathematically different from credited PD-TAR uniqueness; exclusion is source proof, not a false family conflation.',None,['325227.pdf'],[]),
'325320':('excluded_published_proof','primary moment conjecture; Gunderson–Przykucki Theorem 2 and Lemmas 3/4 proof portions read',
 'Lower bounds for bootstrap percolation on Galton–Watson trees, arXiv:1402.4462, Theorem 2 proves the full alpha in (0,r-1] range. Lemma 3 covers the interior, Lemma 4 the endpoint. Infinite moments give a trivial right side; the small-offspring case is addressed before the theorem.',
 'No finite simulation could resolve an almost-sure infinite-tree critical-probability bound; published theorem already supplies the answer.',None,['325320.pdf','bootstrap.pdf'],[]),
'326292':('parked_hard_scope','primary MMS Conjecture 1.2 and source cubic-range theorem read; bounded integer test',
 'The literal intended conjecture is the classical real-weight MMS sets problem n >= 4k. The source’s hypergraph theorem only settles a much larger range. No full proof or counterexample was found.',
 'At n = 4k for k = 2,3,4, enumerated every sorted integer vector in [-2,2]^n with nonnegative sum: 264,953,2511 vectors. Every k-subset was checked exactly. This covers only those integer vectors, not the real-weight problem.',
 'Need an exact real-weight sign-pattern search beyond established ranges or a full structural proof. This flagship conjecture is a poor Lean-cost discovery target here.',
 ['326292.pdf'],['outputs/mms.json']),
'326437':('parked','primary inertia/signature definitions and source special-case theorem statements read; exact rational finite test',
 'General Ma–Yang–Li signature versus cycle-count bounds remain beyond the source’s line-graph and power-tree cases in this pass. The 2026 counterexample to a constant line-graph-signature bound is a different conjecture and does not refute these cycle bounds.',
 'All 1252 nonempty atlas graphs through order 7. All simple cycles counted exactly once by minimum vertex and orientation; inertia signature computed by exact rational symmetric elimination, using 1x1 pivots or 2x2 zero-diagonal hyperbolic pivots. No violation. Output key signature_float_diagnostic is a stale name; the FINAL atlas.py calculation is rational, with no floating arithmetic.',
 'Need a sparse odd-cycle family with disproportionate signature beyond known theorem classes; dense random graphs have enormous cycle counts and are unlikely to help.',
 ['326437.pdf'],['outputs/atlas.json']),
'333080':('excluded_published_refutation','primary Conjecture 2.6; Pokrovskiy–Sudakov Theorem 2 and construction/proof read',
 'Take m = n and every class of size n. The proposed matching would meet at least n-1 classes, hence give a partial rainbow matching of size n-1. Pokrovskiy–Sudakov arXiv:1711.00429 constructs equi-n-square arrays with no partial transversal larger than n - log(n)/42 for sufficiently large n, contradicting this. This is a direct published-construction bridge.',
 'No new array search justified; complete-bipartite edges correspond to array cells, and class intersections to symbol multiplicities.',None,['333080.pdf','stein.pdf'],[]),
'381197':('excluded_published_proof','primary planar recoloring conjecture; Bousquet–Heinrich Theorem 1 and proof reduction read',
 'A polynomial version of Cereceda’s conjecture, arXiv:1903.05619, Theorem 1 proves diameter (Cn)^(d+1) whenever k >= d+2. Planar graphs are 5-degenerate, giving O(n^6) for every k >= 7; the paper explicitly states this consequence. Quadratic Cereceda remains a different stronger question.',
 'No finite recoloring test is relevant after exact published full-scope result is recovered.',None,['381197.pdf','recoloring.pdf'],[]),
'322976':('parked','primary integer-label definition and abelian-group contrast read; exact atlas test',
 'The intended labels are from [k], not an arbitrary set of k real numbers or an abelian group. The source’s group-valued counterexamples do not refute the integer conjecture. A 2026 Delta+1 bound is only a partial bound, not eta <= chi.',
 'All 1252 nonempty atlas graphs through order 7. Chromatic number found by exact coloring enumeration; a [chi]-additive coloring is then found by exact label enumeration and stored. No counterexample.',
 'Need a larger graph with a proved additive-label obstruction at k = chi, or a full universal construction. Group-order obstructions alone do not transfer to integer sums.',
 ['322976.pdf'],['outputs/atlas.json']),
'323179':('excluded_published_refutation','primary F-Wythoff rules and Ho conjecture; Jiao Theorem 12 and preceding explicit failure read',
 'Jiao, Electronic Journal of Combinatorics 20(1), P14 (2013), explicitly states G(1,8) = G(3,10) = G(5,12) = 9 and removes uniqueness in Modified Conjecture 15 / Theorem 12. These three positions lie on the same difference-7 diagonal. Existence is proved there; the full MathDB uniqueness statement is already refuted.',
 'No fresh mex sweep justified after exact published counterexample and modified theorem were recovered.',None,['323179.pdf','wythoff-proof.pdf'],[])
}
assert set(notes)==set(x) and len(notes)==20
results={}
for i,o in x.items():
 outcome,depth,disposition,coverage,gap,sources,attempts=notes[i]
 receipts={}
 for name in [i+'.abs.html']+sources:
  p=D/'sources'/(name+'.receipt.json')
  if p.exists():receipts[name]=json.loads(p.read_text())
 versions=re.findall(r'\[v(\d+)\]',(D/'sources'/(i+'.abs.html')).read_text())
 results[i]={**o,'outcome':outcome,'review_depth':depth,'disposition':disposition,'mathematical_attempts_and_coverage':coverage,'remaining_obligation':gap,'primary_sources':sources,'source_receipts':receipts,'arxiv_versions_listed_on_current_abstract':versions,'current_version_policy':'PDF fetched from unversioned arXiv /pdf route on receipt date; earlier versions not exhaustively compared unless stated. No withdrawn-conjecture clearance is claimed.','attempt_artifacts':attempts,'history_check':'outputs/history-exact.txt: no prior substantive ID/title disposition found within searched campaign prose/results/ledgers; hash/byte-count false positives discarded. Not global novelty clearance.','family_check':'Credited/excluded families in TASK.txt and both campaign ledgers read; no credited-family variant nominated.','registry_check':'outputs/registry-screen.json: complete current HEAD D5, Problems and OpenAI preprints path screens; no universal proof-body clearance claimed.','lean_status':'No eligible endpoint survived; no Lean/leanchecker was run; all computations are diagnostics.','accepted':False,'root_decision_required':True}
(D/'results.json').write_text(json.dumps(results,ensure_ascii=False,indent=2)+'\n')
# Byte manifest preserves exact raw-line and source integrity, including failures as receipts.
manifest={str(p.relative_to(D)):{'bytes':p.stat().st_size,'sha256':sha(p.read_bytes())} for sub in ["raw","sources","outputs","scripts"] for p in (D/sub).rglob('*') if p.is_file() and p.name!='artifact-manifest.json'}
for name in ["TASK.txt","reservation.json","extracted.json","results.json","SUMMARY.md"]:
 p=D/name;manifest[name]={"bytes":p.stat().st_size,"sha256":sha(p.read_bytes())}
(D/'artifact-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('exactly',len(results),'ID-keyed results');print({k:sum(o['outcome']==k for o in results.values()) for k in sorted(set(o['outcome'] for o in results.values()))})
