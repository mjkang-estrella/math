import json, pathlib, hashlib
D = pathlib.Path(__file__).resolve().parents[1]
ex = json.loads((D / 'extracted.json').read_text())
ids = json.loads((D / 'reservation.json').read_text())['ids']

def rec(path):
    p = D / path
    if p.exists():
        r = json.loads(p.read_text())
        return {k: r.get(k) for k in ('url', 'utc', 'status', 'sha256', 'bytes', 'error')}
    return None

def src(key):
    return {'abs': rec(f'sources/{key}.abs.html.receipt.json')}

def pdf(*keys):
    return {k: rec(f'downloads/{k}/receipt.json') for k in keys}

DISP = {
 345545: dict(
  outcome='CANDIDATE_REFUTATION_SOURCE_SCOPE',
  review_depth='Primary v4 Definition 1.1, Section 2.3, Theorem 2.5 with full proof, Section 4 Conjecture 4.4 and its evidence read; all four arXiv versions listed; Defant Troupes v2 Theorem 7.29 and Remark 7.30 read; Defant 2003.05935v2 grepped; Zhang 2606.24110 and Fried 2204.07873 screened.',
  summary='Source deg = (1/n!) sum_y |s^-1(y)|^2 (average fiber multiplicity; the MathDB "maximum fiber size" paraphrase is a defect: the literal maximum gives limit 4). New exact formula: the closure of two postorder tree orders is a postorder forest, so by the hook-length formula d_n = sum over pairs of tree shapes of prod 1/h_j. A block recursion makes P_n = n! d_n polynomial-time. Exact P_50 with the doubling form of source inequality (1) gives lim d_n^(1/n) >= 1.7330 > 1.73. Independently, P_78 with the source sup formula gives > 1.7319. So Conjecture 4.4 is false. Extrapolated limit approx 1.9532.',
  mechanism='Exact integer certificate P_50 (also P_78) plus the source Fekete argument; the DP is proved in candidate-345545/CANDIDATE.md section 3.3.',
  verification='DP equals brute force for n<=10; an independent automaton DP equals it for n<=14; shape-pair closure equals brute force for n<=6; exact integer inequalities checked.',
  lean_status='UNCOMPILED draft candidate-345545/lean/StackSortDegree.lean (endpoint plus lemma chain with sorry placeholders). Lean cost medium-high: DP correctness (trees, closure, forest hook formula, blocks) dominates.',
  significance='Refutes a published conjecture (EJC 2020) that Defant restated as open in 2022 after reaching a 1.62924 lower bound. The new polynomial formula is the key; the conjecture fails by a wide margin.',
  prior_art='Web searches 2026-11-03 found no later bound or refutation; OEIS-style search for 1,4,26,224,2356,29064 found nothing; registry path screens clear (Omega c7f3e33e D5 and Problems; OpenAI preprints listing at 4eaee875).',
  sources=dict(**src('2002.07144'), **pdf('2002.07144v4', '2004.11367', '2003.05935v2', '2606.24110', '2204.07873'))),
 373432: dict(
  outcome='EXCLUDED_KNOWN_2026',
  review_depth='Primary v3 Lemma 5.6, Theorem 1.2 and Conjecture 5.7 read; Liu note abstract and Danus Theorem 4 read.',
  summary='Already proved: Jihao Liu, "Factorial asymptotics of the Matryoshka numbers" (note dated 2026-06-15), and Danus arXiv:2607.06447 Theorem 4 give 0.00542831750 <= S <= 0.00542831848. The lane independently found the exact polynomial solution p(n)=n^4+18n^3+107n^2+242n+168 of the linearized recurrence and the averaging proof, but credit is excluded.',
  sources=dict(**src('2603.03425'), **pdf('2603.03425v3', 'liu-matryoshka-note', '2607.06447'))),
 343305: dict(
  outcome='PARKED_HARD_ASYMPTOTIC_WITH_DATA',
  review_depth='Primary v2 Section 7 Conjecture 7.2 and footnote read; Archer-Graves arXiv:2604.25912 (2026) read in part; Nadler 2604.22135 screened.',
  summary='Exact counts for n<=14 by brute force over 132-avoiders: PAv_n = 1,2,5,12,22,44,79,140,260,492,850,1690,3122,5856; Omega_{1,2,3} = PAv up to n=8, then 262 vs 260 at n=9 and 5884 vs 5856 at n=14; elements fixing n contribute exactly PAv_{n-1}. Archer-Graves (2026) now give |SAv_n(132)| ~ K 2^n/sqrt(n), but the PAv and Omega asymptotics still need a full cycle-structure enumeration and singularity analysis (Lean-heavy). No counterexample mechanism (asymptotic statement).',
  sources=dict(**src('1907.09451'), **pdf('1907.09451v2', '2604.25912', '2604.22135'))),
 364593: dict(
  outcome='PARKED_BOUNDED_NONFINDING',
  review_depth='Primary v2 Theorem A, Remark 2, Proposition 2.2 with Lemmas 2.3-2.5 and Conjecture 2.6 read.',
  summary='Intransitive maximal subgroups are settled in the source for all n>=5 (Prop 2.2). Lane check: for imprimitive maximal (S_a wr S_b) cap A_n, n<=36, the fixed-point proportion stays below f(n,1); the minimum margin is 0.037 (n=9, 3x3). Primitive maximal subgroups need a group library (GAP not used). A full proof needs an effective Luczak-Pyber estimate; Lean is infeasible. Follow-up Kishnani-Kundu (2608.22428) addresses other Burness-Fusari conjectures.',
  sources=dict(**src('2409.01043'), **pdf('2409.01043v2'))),
 365487: dict(
  outcome='PARKED_BOUNDED_NONFINDING',
  review_depth='Primary v2 Section 3 Conjectures 3.1-3.2 read; JKK arXiv:2007.01005 Theorem 1 (4 pi bound) read.',
  summary='Diagnostic double/Decimal computation (Sylvester-inertia band edges; not validated) beyond the authors q<=95: q=97 all p gives max q|S| = 9.3296320 (p=33), 3.2e-4 below 32C/pi, and a middle-inequality margin of 0.063 (p=3). p in {1,2} for odd q 97..129: no violation; the p=2 margin shrinks like ~q^-2.4. JKK prove only q|S| < 4 pi. A certificate would need validated root isolation of degree-q discriminants (Lean-heavy). The last inequality sqrt(2/q) is implied by Last 2(sqrt5+1).',
  sources=dict(**src('2410.18536'), **pdf('2410.18536v2', '2007.01005'))),
 358865: dict(
  outcome='PARKED_PROOF_ROUTE_SKETCH',
  review_depth='Primary v3 Section 1 definitions, Lemma 3.1 with proof and Conjecture 3.2 read.',
  summary='Lower bound n^2/8 is the source Lemma 3.1. Under the source rules the firefighter moves at most 1 step per turn and protects its vertex, so walls are 4-connected walks racing an L1 fire. In the continuum family (inward leg meeting the front, then an outward monotone leg), area 2b(n/2-b) is maximised at b=n/4, giving exactly n^2/8. This supports the conjecture, but a proof must control arbitrary walk strategies; no finite certificate is possible for a limit statement.',
  sources=dict(**src('2306.12575'), **pdf('2306.12575v3'))),
 382036: dict(
  outcome='PARKED_NO_MECHANISM',
  review_depth='Primary v4 (2026-09-08) Section 4.2: Theorem 4.7 proof, Lemma 4.8, Theorem 4.9 and Conjecture 5 read; v3 downloaded; v4 update note read (it refutes two OTHER conjectures, not Conjecture 5).',
  summary='Constructions give 3n/2 - O(1) and the lower bound is n+1. Refuting needs a family with ratio < 3/2 (no composition beating Lemma 4.8 found); proving needs a new lower-bound method. Akman-Sissokho 2607.23411 concerns affine spreads, not this bound.',
  sources=dict(**src('2212.14685'), **pdf('2212.14685v4', '2212.14685v3'))),
 366896: dict(
  outcome='EXCLUDED_WORDING_VACUOUS',
  review_depth='Survey v5 Conjecture 4.2 and original arXiv:2012.10330 (v1-v4) Corollary 2.8 and Conjecture 2.9 read.',
  summary='Both the survey and the original literally state n/3 + O(n), which holds trivially since mp <= n. The intended sharper form (o(n) or O(1)) is unstated, so any refutation or proof would target an unstated statement. Corollary 2.8 gives mp <= 2(n-1)/3 for connected cubic graphs.',
  sources=dict(**src('2501.19385'), **pdf('2501.19385v5', '2012.10330'))),
 348108: dict(
  outcome='EXCLUDED_LITERAL_SOURCE_TYPO_SUBSTANTIVE_PARKED',
  review_depth='Primary v1 Conjecture 5.1 read.',
  summary='Source item (5) itself reads "g -> 0 as alpha -> infinity and g -> 1.273 as alpha -> infinity", which is self-contradictory as printed, so a literal refutation is a typo correction (zero credit). The substantive almost-sure energy limit for BA trees is a hard probabilistic problem with no tractable mechanism; a 2025 paper (2502.01065) bounds limsup by 0.96 w.h.p.',
  sources=dict(**src('2009.13784'), **pdf('2009.13784'))),
 373769: dict(
  outcome='PARKED_PARTIAL_SOURCE_PROGRESS',
  review_depth='Source arXiv:2603.21625v2 Section 6 Conjecture 6.1 read.',
  summary='The source author (Waite) reports results supporting six of the seven classes (4321 via 2506.05712; 4123, 3412, 4231, 4213, 3142); 4312 is open and has no tractable mechanism here. Asymptotic, so no finite certificate.',
  sources=dict(**src('2603.21625'), **pdf('2603.21625v2'))),
 352805: dict(
  outcome='PARKED_LOW_SIGNIFICANCE_NUMERIC_CONSTANT',
  review_depth='Primary v1 Section 4 Conjecture 4.1 and the preceding discussion read.',
  summary='The authors explicitly say 229024 is a tentative explicit choice ("some level of uncertainty"); C is a 5-dimensional semialgebraic volume (Cayley-Menger positivity) up to the S4 symmetry. Refuting the chosen denominator would be a numerical correction; an exact C needs a semialgebraic volume evaluation (Lean infeasible).',
  sources=dict(**src('2112.00899'), **pdf('2112.00899'))),
 341220: dict(
  outcome='PARKED_CONSTANT_CONVENTION_AND_HARD',
  review_depth='Primary v4 Section 4 (n=3 exhaustive search, recurrence, Conjecture) read.',
  summary='"Asymptotic" is loose (for n=1 the count is binom(k,k/2) ~ sqrt(2/pi) 2^k/sqrt(k)), so a literal ~ refutation via constants would be a convention issue. The substantive Theta(2^k/k^{n/2}) needs a uniform lower bound over all splittable n-families (local-CLT/lattice argument); the upper bound comes from disjoint balanced blocks. Not pursued to completion.',
  sources=dict(**src('1811.12896'), **pdf('1811.12896v4'))),
 352307: dict(
  outcome='PARKED_HARD_ASYMPTOTIC',
  review_depth='Primary v1 Section 4 Conjecture 4.1 read.',
  summary='The central-moment expansion for all r in the regime n >> m; based on computational evidence. Asymptotic in m for every r; no finite certificate; no tractable full-scope route found. Published EJC 2023.',
  sources=dict(**src('2110.10315'), **pdf('2110.10315'))),
 372765: dict(
  outcome='PARKED_HARD_DIOPHANTINE',
  review_depth='Primary v1 Section 9 Conjecture 9.2 located and read.',
  summary='Asymptotic for near-perfect-power indices of overpartition numbers; heuristic and data-based; needs control of all n (Diophantine). No mechanism. Same-source items handled in r111/r366 lanes (different IDs).',
  sources=dict(**src('2601.18138'), **pdf('2601.18138'))),
 368881: dict(
  outcome='PARKED_HARD_ANALYTIC',
  review_depth='Rodgers-Sahay v2 Conjecture 3 read.',
  summary='Paley VC-dimension (1+o(1)) log2 N: the known lower bound is (1/2+o(1)) log2 N via Weil; the full conjecture needs character-sum control beyond square-root cancellation. Rodgers-Sahay prove the random Cayley analogue only.',
  sources=dict(**src('2506.14219'), **pdf('2506.14219v2'))),
 358020: dict(
  outcome='PARKED_HARD_EXTREMAL',
  review_depth='Primary v1 Conjecture 6 read.',
  summary='Theta(e^{1/(2k-2)} q) for e > q^C; requires near-design constructions and matching upper bounds; no tractable route. Same-source 358021 handled by r52.',
  sources=dict(**src('2304.04855'), **pdf('2304.04855'))),
 373488: dict(
  outcome='PARKED_HARD_GEOMETRIC',
  review_depth='Primary v1 Conjecture 4 located; Erdos Problem 1045 status via search (odd n open; even n non-regular by 2512.14251).',
  summary='Maximizer structure for every n (regular for odd n, symmetry and diameter-graph shape for even n); global non-convex optimisation; no finite certificate covers all n.',
  sources=dict(**src('2603.07088'), **pdf('2603.07088'))),
 382109: dict(
  outcome='PARKED_HARD_ANALYTIC',
  review_depth='Primary v3 Conjecture 10.4 located.',
  summary='Asymptotic constants of two LP-derived systole bounds; requires asymptotic analysis of the LP optimum; no tractable route.',
  sources=dict(**src('2302.02540'), **pdf('2302.02540v3'))),
 347590: dict(
  outcome='PARKED_HARD_EXTREMAL',
  review_depth='Primary v2 Conjecture 1.11 located.',
  summary='Existence of xi_g(k_A) and the limit of log(xi_g)/k_A; a universal choosability statement for all bipartite graphs; consistent with r606 park of a same-source item.',
  sources=dict(**src('2008.06040'), **pdf('2008.06040v2'))),
 341979: dict(
  outcome='PARKED_HARD_ASYMPTOTIC',
  review_depth='Primary v1 Conjecture 1 read.',
  summary='Omega(n^{1+eps}) area lower bound for subtree-separated orthogonal drawings of complete ternary trees; needs a lower-bound argument over all drawings; no finite certificate.',
  sources=dict(**src('1902.11044'), **pdf('1902.11044'))),
}

out = {}
for i in ids:
    e = ex[str(i)]
    d = DISP[i]
    out[str(i)] = {
        'mathdb_id': i, 'title': e['title'], 'canonical_url': e['canonical_url'],
        'source_url': e['source_url'], 'source_name': e.get('source_name'),
        'provenance': e['provenance'], 'raw_file': f'raw/{i}.jsonl',
        'literal_statement_sha256': e['provenance']['statement_sha256'],
        'inherited_exclusion_found': False,
        'history_check': 'Grep of campaign 2026-10-27 md/results/dispositions/ledger files for the ID and arXiv number: no prior technical entry for this ID (only same-source different-ID entries and the r133 launch note).',
        'accepted_credit': 0, 'self_accepted': False, **d}
assert len(out) == 20
(D / 'results.json').write_text(json.dumps(out, indent=1, ensure_ascii=False) + '\n')
print('wrote', len(out), {k: v['outcome'] for k, v in out.items()})
