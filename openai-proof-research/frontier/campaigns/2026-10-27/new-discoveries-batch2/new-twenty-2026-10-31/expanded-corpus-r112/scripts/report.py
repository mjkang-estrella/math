import json,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
X=json.loads((D/'extracted.json').read_text())
def src(url):
    a=url.rsplit('/',1)[-1]; rec=json.loads((D/f'sources/{a}.html.receipt.json').read_text())
    return {'local':f'sources/{a}.html','sha256':rec['sha256'],'receipt':f'sources/{a}.html.receipt.json','fetched_utc':rec['utc'],'status':rec['status'],'text':f'sources/{a}.txt'}
REG='outputs/registry-screen.json (OpenAI/math HEAD 4eaee87548250b2682affda7d05d947c05554bae; Omega HEAD e51c7d81cdffe6e70999db34b8a564a99074807b; complete untruncated preprints, D5 and Problems trees; path screen only unless stated)'
HIST='history-matches.txt (exact-ID/title search: only false numeric hits and the reservation list in ledger.json); outputs/history-source-aliases.txt (source arXiv-ID search: only sibling IDs 373550/373551 (r68), 374697 (r70), 374244 (r110), and different same-source conjectures in r19/r60)'
R={}
def put(i,outcome,depth,attempts,remaining,logs=(),lean=None,extra=None):
    o=dict(X[str(i)]); o.pop('statement',None)
    e={'mathdb_id':i,'title':X[str(i)]['title'],'statement_sha256':X[str(i)]['provenance']['statement_utf8_sha256'],
       'provenance':X[str(i)]['provenance'],'raw_local':f'raw/{i}.jsonl','source_url':X[str(i)]['source_url'],'source':src(X[str(i)]['source_url']),
       'outcome':outcome,'review_depth':depth,'mathematical_attempts_and_coverage':attempts,'remaining_lemmas_or_limits':remaining,
       'logs':list(logs),'history_check':HIST,'registry_check':REG,'accepted_credit':0,'lean_endpoint':lean,'novelty_cleared':False}
    if extra: e.update(extra)
    R[str(i)]=e
put(373552,'parked_analytic_numerical_target',
 'Source Conjectures 3.1-3.3 located (sources/2603.10981.txt lines ~253-276); statement is a manifold-dimension claim about a real-algebraic solution set motivated by numerical scans.',
 'No finite search applies: the claim concerns the dimension of a continuous real solution variety for every error weight t. Siblings 373550 (parked) and 373551 (excluded, basis convention) were handled in r68.',
 'Would need a uniform description of the real minimal PI-code variety and a transversality/rank argument for all t; no tractable mechanism identified.')
put(373739,'parked_analytic_numerical_target',
 'Source Conjecture 3 and its surrounding numerical discussion read (sources/2603.20039.txt lines ~137-196).',
 'Analytic PDE-spectral claim (polynomial coercivity of the Ginzburg-Landau Hessian in kappa); the source states it is intended to be verified numerically and no analytic kappa-dependence is known. No finite certificate route.',
 'Requires analytic lower bounds for the nonlinear Hessian at minimisers uniformly in kappa; out of scope for this lane.')
put(374156,'parked_heavy_geometric_computation',
 'Abstract, Sections 1.1-1.3 and the signature discussion (lines ~496-602) read; Q_tau is defined per combinatorial type of 4-colourings of 6,...,6,4,4,4,4,4,4 triangulations via Thurston coordinates.',
 'The source reports checking many cases and that cones can have dimension > 4 (Taha-Fu example), in which case signature (1,3) needs a reduction the source discusses. Implementing type enumeration, cone computation and the Hermitian-form pull-back was judged infeasible within the caps; no search run.',
 'Needs a complete enumeration of generic colouring types with exact cone and quadratic-form computation, or a conceptual proof via the Thurston Hermitian form restricted to the cone span.')
put(374228,'parked_famous_open_conjecture',
 'Source (Chen-Wang-Zhang, positive and negative 3-energies) Section 1 read: Conjecture 1.1 is the 2016 Elphick-Farber-Goldberg-Wocjan square-energy conjecture, best bound 3n/4 (Akbari-Kumar-Mohar 2025); the source itself proves p=3 analogues only.',
 'Famous long-standing open problem with extensive literature verification for many classes; no capped exhaustive graph generator is available in this lane (no nauty/geng), so no small-order sweep beyond the literature was attempted. Counterexamples at small order are considered unlikely given prior verification.',
 'Full conjecture open; any route would need a new structural inequality for E_2^+ and E_2^-.')
put(374236,'parked_cyclic_ramsey_upper_bound_gap',
 'Source Sections 1-4 read; Theorem 4.5 gives the lower bound 1+(a-1)(b-2); Table 3 transcribed (exact for small cells, lower bounds only for (3,14),(3,15),(4,11),(4,12),(5,9),(6,8),(7,7),(7,8),(8,8)). SAT encoding validated against Tables 3, 10, 11, 15, 16, 19.',
 'Two proof routes tested by SAT and refuted at small orders: (1) a single-cut Erdos-Szekeres lemma (exists a cut where linear blue paths have <= b-2 or red <= a-2 vertices) is FALSE, with witnesses at (a,b,n)=(3,5,4),(3,6,5),(4,5,6),(4,6,5),(4,6,7),(5,5,8) (logs/cutlemma-*.log); (2) transfer of the 374241 jump argument needs J(v)+K(v) <= a, which FAILS even at extremal n=(a-1)(b-2), e.g. (a,b,n)=(5,5,12) and (4,4,6) (logs/runs-*.log). Circulant colourings cannot reach the known lower bounds (e.g. P5 vs P5 at n=12 is UNSAT under circulant restriction) so a circulant counterexample search was abandoned. No counterexample found.',
 'Need a genuinely cyclic Erdos-Szekeres upper-bound argument for red paths (unbounded red degree); the star case 374241 is solved here and its method does not transfer.',
 logs=['logs/cutlemma-*.log','logs/runs-*.log'])
put(374240,'parked_cyclic_ramsey_upper_bound_gap',
 'Source Conjecture 4.14 and Table 10 transcribed; lower bound is source Theorem 4.6 (connected H vs monotone cycle, colours swapped).',
 'Encoding validated (Cmon4 vs Palt4: SAT at 9, UNSAT at 10, matching Table 10). No upper-bound mechanism found; the 374241 jump argument does not apply because red is constrained only by monotone-cycle avoidance. Note that 374244 (K_a vs alternating path, parked in r110) has the same value and its upper bound would follow from this one.',
 'Need an upper-bound argument for red convex-cycle-free colourings forcing a blue cyclic zigzag path.')
put(374241,'candidate_full_proof_with_lean_endpoint',
 'Source (Basic, Damnjanovic, Stevanovic, Stosic, arXiv:2604.16188v1) Sections 1-4 and 6 read; definitions of cyclic embedding, S_a^sc, P_b^mon and R_cyc taken literally; Theorem 4.5 (lower bound) proof read; Table 11 transcribed.',
 'Full proof for all a>=3, b>=4 (PROOF-374241.md). Lower bound: source Theorem 4.5 block colouring. Upper bound: new Theorem A (jump functions J,K with J,K<=t+1 and J+K<=t+2, forced equality of the greedy span, orbit wraps to u-1 contradicting K(u)=1). Exact extremal min-degree n-ceil(n/(b-2)) confirmed by SAT for b=4,5,6, n<=13 (logs/mindeg-b*.log) as a diagnostic. Lean endpoint CycRamsey.cycRamsey_startStar_monPath proves the literal equality including the definitions and the lower-bound construction.',
 'No mathematical gap known. Remaining: independent adversarial review, statement-fidelity review of the Lean definitions (Sym2 colouring, Fin-addition rotation, fromRel graphs, sInf via IsLeast), wider prior-art search for Dirac-type results on convex geometric graphs, significance judgment by root.',
 logs=['formal/fresh-replay/*.log','formal/fresh-replay/sources.sha256','logs/lean-replay.log','logs/mindeg-b4.log','logs/mindeg-b5.log','logs/mindeg-b6.log'],
 lean={'packet':'formal/','endpoint':'CycRamsey.cycRamsey_startStar_monPath : ∀ (a b : ℕ), 3 ≤ a → 4 ≤ b → cycRamsey (startStar a) (monPath b) = 1 + (a - 1) * (b - 2)','modules':['CycDefs','CycRot','CycLower','CycUpper','CycMain','Audit'],'replay':'formal/replay.sh -> formal/fresh-replay (fresh extracted copy, -DwarningAsError=true, all builds rc 0, leanchecker rc 0 on all five modules)','axioms':['propext','Classical.choice','Quot.sound'],'lean':'4.34.1','mathlib':'pinned prebuilt cache d13f23b723b8a846827a245b89c10fc7d3f11612 (read-only; not rebuilt)'})
put(374243,'parked_sat_beyond_range_no_counterexample',
 'Source Conjecture 4.22 and Table 15 read: the formula is fitted to 14 exact cells (a=3 row b<=8, a=4 b<=5, a=5 b<=4, b=3 column); no source lower- or upper-bound theorem.',
 'Validated encoding (K4 vs Palt4: SAT 10 / UNSAT 11). Beyond-range cells: witnesses found at n=f-1 for (a,b)=(3,9),(4,6),(6,4),(5,5),(7,4) (outputs/ramsey/witness-*.txt), confirming the lower side; at n=f CaDiCaL returned UNKNOWN after 10 s and again after 112 s per cell (outputs/ramsey/r374243.jsonl, c43*.jsonl). No counterexample. The b=3 column R=2a-1 has an easy proof (forest/cocktail-party argument), not pursued as it is a known-type parameter case.',
 'Upper bounds at n=f beyond the source range need much larger SAT effort (or a proof); a counterexample would need SAT at n=f.',
 logs=['logs/r374243a.log','logs/c43a.log','logs/c43b.log','logs/c43c.log','logs/c43d.log','logs/c43e.log'])
put(374246,'excluded_routine_source_consequence',
 'Source Theorems 1.3 and 4.1 (with proofs) and Table 19 read.',
 'Short full proof: upper bound M_a^nest is a spanning subgraph of K_a, so R_ord <= R_ord(K_a,P_b^mon) = 1+(a-1)(b-1) by source Theorem 1.3 (colours swapped). Lower bound: the source Theorem 4.1 block colouring (blocks of size a-1, colour 1 inside blocks) works verbatim: the outer edge {phi(0),phi(a-1)} of a colour-1 nested matching forces all a vertices into one block, and a colour-2 monotone path visits b distinct blocks. (Table 19 even lists weaker lower bounds such as >=39 for (6,9) and >=32 for (12,4).) This is a one-paragraph bridge from the source own theorems, so per campaign rules (369221/374488/371637) it is a zero-credit routine consequence.',
 'None mathematically; excluded on significance grounds.')
put(374411,'parked_heavy_algebraic_computation',
 'Abstract, Sections 1-2 and the statement of Conjecture 4.6 read; source verified 1<=k<=n<=8 for affine permutations of length <=15 (n=6 to 21, n<=5 to 27) and proves k=3.',
 'Implementing affine k-inversions, admissible orders, consistent sets and the congruence-graph G_R exactly was judged beyond the lane budget; no new computation.',
 'Needs a full implementation of C_w(n,k) and G_R or a structural acyclicity proof generalising the k=3 argument.')
put(374521,'parked_reduction_recorded_no_search',
 'Whole source read (two-place LMRIV proof via power-sum identities; multi-edge Conjecture 3.1 verified n<=9).',
 'Observed reduction: by edge interlacing for LM roots, any connected G and proper supergraph H=G+F both having all-integer LM roots gives a multi-edge LMRIV, so integral pairs are sufficient witnesses. No graph generator (geng) is available; no search beyond the source n<=9 was run.',
 'Need either a structured search for LM-integral pairs (trees with Laplacian-integral spectra plus edges) beyond n=9 or a multi-place power-sum argument.')
put(374618,'excluded_source_refuted',
 'Whole source read: Chen-Li, Counterexamples to a conjecture on graph inertia.',
 'The source Remark 2.1 explicitly disproves exactly this inequality 2n <= (n-n^+)(n-n^+ +3) using W_k (n=binom(k+1,2), n-n^+=k-1). Zero credit; no new work.',
 'None.')
put(374698,'parked_heavy_definition_search_gap',
 'Introduction, Section 2 definitions (normal sets, alternatingly oriented vertices, E_1..E_4) and conjecture context read; sibling 374697 was parked in r70 for the same definition/search gap.',
 'A finite check would need plane-embedded digraph generation, minimum feedback vertex sets and enumeration of normal cycle sets; not implemented within the caps.',
 'Needs a plane-digraph generator with rotation systems and exact normal-set optimisation, or a proof of a low-density uncrossing lemma.')
put(374792,'parked_automatic_sequence_target',
 'Source Section 5 (Conjecture 5.2, Remark 5.4) read; Fibonacci indexing F_0=1, F_1=2, F_{-1}=1 inferred from the displayed prefix.',
 'Not computed. A proof would naturally use Fibonacci-automatic/regular-sequence tools (Walnut), which require Java (disallowed here). A Lean certificate for a counterexample at length n would need Cl(w) for all n+1 factors, judged too heavy.',
 'Need a Fibonacci-regular description of M_n or a large-n computation of closed-factor counts.')
put(374848,'parked_infinite_group_target',
 'Source Section 6 Conjectures 16-17 and definitions of Hausdorff dimension and fixed-point density read.',
 'Concerns arbitrary closed level-transitive subgroups of Aut(T); no finite reduction. Conjecture 17 implies Conjecture 16 per the source.',
 'Needs a martingale/Markov-chain argument for fixed-point proportions under positive Hausdorff dimension.')
put(374960,'parked_exhaustive_check_beyond_source_no_counterexample',
 'Source Section 4.4 (Conjecture 4.9, Remarks 4.10-4.11) and definitions of Q_tau, P_tau and the q-zeta polynomial read.',
 'C program csrc/qzeta.c checks identity (21) for every preorder of size n given as a naturally labelled poset on K vertex classes with vertex sizes (covers every isomorphism class, with repetition), via multichain prefix sums on the down-closed set P_tau and interpolation in X=q^m, arithmetic mod 2^61-1 at one fixed q. Mutation tests (wrong sign, wrong cov exponent) fail as expected. Results: all preorders of size <= 6 (reproducing the source), size 7 (131,645 representatives) and size 8 (K=1..6 classes: 115,361; K=7: 674,996; K=8: 2,800,472) pass with consistent interpolation. Probabilistic modulo-p identity check, not an exact proof.',
 'Full conjecture open beyond size 8; Remark 4.10 reduces (22) to Conjecture 4.4.',
 logs=['logs/qz56.log','logs/qz7final.log','logs/qz8k1to6.log','logs/qz8k7s*of2.log','logs/qz8k8s*of8.log','logs/qz8-summary.txt'])
put(375112,'excluded_public_registry_partial_settlement_q_open',
 'Source Sections 2-3 and 6 read (Definitions 2.4-2.6, Fact 2.9, Conjecture 6.1). Omega Problems/bona-maga-richey-2026-half-frequency-balanced-borders.md and Lean modules BalancedBordersHalfFrequency.lean, BonaMagaRicheyHalfFrequency.lean fetched at Omega HEAD e51c7d81 and read: the rho clause is kernel-checked there; the q clause is open. Earlier lane r19 also recorded the Omega rho proof.',
 'Independent diagnostic: derived rho^w=1/2 iff sum_b (2|b|_1-|b|) lambda^|b| = 0 (validated against the source rho^{11}, rho^{1001}); exhaustive C screen of all binary words of length <= 28 (csrc/halffreq.c, logs/half2_22.log, logs/half23_28.log) found no non-balanced-border word with rho=1/2, corroborating Omega. The q clause was not attacked (requires the transcendental q integral).',
 'The q clause remains open; the rho clause is public prior art (Omega).',
 logs=['logs/half2_22.log','logs/half23_28.log'],
 extra={'prior_art_bodies':['sources/omega-problem-halffreq.md','sources/omega-BalancedBordersHalfFrequency.lean','sources/omega-BonaMagaRicheyHalfFrequency.lean']})
put(375347,'parked_contains_stanley_open_problem',
 'Abstract, Section 1 (Stanley Question 1.1, constructions known for m<=6), Theorem 2.1 (#SCD(L(2,n)) = floor((n+2)/2)!) read.',
 'For fixed m>=7 even the existence of one SCD of L(m,n) is open (Stanley), so the literal conjecture for all m>1 contains a famous open problem; m=2 is source-proved.',
 'Out of reach.')
put(375370,'parked_exhaustive_check_beyond_source_no_counterexample',
 'Source definitions (CRIM moves, Dyson rank |r-lambda_1|, P-position) and Conjecture 1 with Table 1 (sizes <= 30) read; Omega CRIM files refute different Conjectures 2 and 3 (sources/omega-problem-crim.md, omega-CrimGrundyRefutation.lean), not Conjecture 1.',
 'C solver csrc/crim.c computes normal-play P/N status for every partition of size <= 85 (all partitions of every size m<=85; 241,783,707 positions including the empty one) by ranking partitions; reproduces small known facts (S_2 losing, rows N). No P-position of odd rank found (logs/crim60.log, logs/crim85.log).',
 'A proof needs a characterisation or invariant of P-positions; none found.',
 logs=['logs/crim60.log','logs/crim85.log'])
put(375467,'parked_exhaustive_check_beyond_source_no_counterexample',
 'Section 4 read in full (Lemmas 4.1-4.3 deficiency criterion, Propositions 4.4-4.14, Theorems 4.9, 4.15, 4.16, Conjecture 4.17, Table 2). The if-direction contains Bebeacua et al. Conjecture 1.2 (binary xrays) as the case 1^n.',
 'C program csrc/xray.c enumerates S^2(lambda) (Landau prefix condition, shape lambda), tests deficiency and realisability by backtracking. Validated against the source: {2^3,5}:146, {2^4,5} deficient (source Table 1 sequence), {1^4,4}:228, {1^7,4}:14630, {2^5,4}:13910. Beyond the source: complete for {2^6,4} (110716), {2^7,4} (897234), {1^8,4} (57018), {1^10,4} (848335), {1^8,5} (112953), {1^9,5} (457866), {1^10,5} (1837457), {2^6,3} (39276), {2^7,3} (309414); {2^8,3} hit the CPU cap undecided.',
 'Families {1^a}, {2^a}, {1^a,2^b(,3)}, {1^a,b<=5}, {2^a,3/4} remain unproved for all a; the binary case is a 2005 open conjecture.',
 logs=['logs/xray1.log','logs/xray2.log','logs/x15.log','logs/x23.log'])
assert len(R)==20 and set(map(int,R))==set(json.loads((D/'reservation.json').read_text())['ids'])
(D/'results.json').write_text(json.dumps(R,indent=1,ensure_ascii=False)+'\n')
print('ok',len(R))
