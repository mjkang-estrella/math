"""Assemble results.json (20 ID-keyed entries) and artifact-hashes.json. Usage: finalize.py LANE"""
import sys, json, pathlib, hashlib, datetime
D = pathlib.Path(sys.argv[1]).resolve()
X = json.loads((D / 'extracted.json').read_text())
V = json.loads((D / 'outputs' / 'versions.json').read_text())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

def rec(p):
    r = D / 'sources' / (p + '.receipt.json')
    return {'path': 'sources/' + p, 'receipt': json.loads(r.read_text())} if r.exists() else None

N = {
'364179': dict(outcome='excluded_published_resolution', review='Source abstract and main theorem read (Bolohan-Buchanan-Burgess-Sajna-Van Snick, J. Combin. Des. 27 (2019), arXiv:2407.21745 v1 only).',
  attempts='No computation. Follow-up "Solution to the outstanding case of the spouse-loving variant of the Oberwolfach problem with uniform cycle length" (ResearchGate listing 347578324) constructs OP+(4m;m) for every odd m >= 5 and states it settles the uniform case; the m = 3 nonexistence is classical. Journal body of the follow-up not retrieved here.',
  gap='None for campaign credit (published resolution). Confirm the follow-up journal body if ever needed.', receipts=['2407.21745-abs.html', '2407.21745.html']),
'364256': dict(outcome='parked_infinite_family_game_lean_cost', review='Current v2 (Discrete Appl. Math. 2025) read: definitions (Maker colours m edges per turn, Breaker one; Breaker wins if the mover cannot colour), Proposition 1.1, Theorems 4.2-4.3 (wheels; W4 gives the printed pair (3,2)), Proposition 5.1 (exceptional pairs, proof omitted), Conjecture 5.2.',
  attempts='Mechanism analysis only: the conjecture needs a witness graph for EVERY non-exceptional pair (m1,m2), i.e. whenever (m2+1) does not divide (m1+1). A tempo/zugzwang design (trap component plus isolated-edge padding, entry forced by move index mod m+1) is the natural route, but Maker may enter the trap with several consecutive moves, so a uniform strategy proof for all pairs would be needed; one pair from a small exhaustive game search would be a zero-credit partial instance. No citing work found (web search 2026-11-05). Lean cost of uniform game-strategy proofs is very high.',
  gap='A uniform family G(m1,m2) with a full two-sided strategy analysis for every non-exceptional pair.', receipts=['2408.02819-abs.html', '2408.02819.html']),
'364405': dict(outcome='parked_ill_posed_statement', review='Source Conjecture 5.1 read (arXiv:2408.09823 v1, only version).',
  attempts='The conjecture reads "contain no induced k-cycle (k >= 5), except C_n (n >= 5) and several graphs"; the exception set is unspecified, so the statement has no exact literal content to prove or refute. No computation.',
  gap='An exact exceptional list from the authors; otherwise no well-defined target.', receipts=['2408.09823-abs.html', '2408.09823.html']),
'364454': dict(outcome='parked_deep_dynamics', review='Abstract, v2 metadata and the sibling record 364453 (r159) disposition read; Bonk-Meyer background via web search.',
  attempts='For expanding Thurston maps an invariant graph exists for sufficiently high iterates (Bonk-Meyer; Cui-Gao-Zeng for pcf rational maps); the record asks for n = 1. No finite certificate route; no computation.',
  gap='A construction of an F-invariant graph containing Q for the map itself, or an explicit obstruction for n = 1.', receipts=['2408.12371-abs.html', '2408.12371.html']),
'364481': dict(outcome='excluded_published_resolution', review='Source v1 Conjectures 1-3, Proposition 1 (length <= 3) and Proposition 2 (binary partitions) read in full.',
  attempts='This lane independently found a short full proof: with phi(t) = sum of lambda_i^t, equal pre_2 gives phi_l(2t) - phi_m(2t) = (phi_l(t) - phi_m(t)) (phi_l(t) + phi_m(t)); equal size makes the difference vanish at t = 1, hence at every 2^j, and a dominant-term argument forces lambda = mu. Also: no length-4 pairwise-product collision with equal sums exists (the reciprocal involution then fixes the multiset; search to part 60 in logs/pre2_len4-60.log). BUT the conjecture is already proved: Stella Li, "A note on multiset reconstruction from sum and pairwise products", arXiv:2508.00971 (abstract and HTML retained), and a 2026 Integers note; a further 2026 paper (Garg, arXiv:2606.09321) cites the result. Zero credit.',
  gap='None (known).', receipts=['2408.13346-abs.html', '2408.13346.html', '2508.00971-abs.html', '2508.00971.html']),
'364512': dict(outcome='parked_deep_category_theory', review='Conjecture 5.5 read in current v4 and v1 (unchanged); neighbouring Conjecture 5.7 noted.',
  attempts='Literal existence of a contravariant functor S -> Lasso(Set^S) on Cat. Precomposition F* does not obviously transport lassos (it would need Lan_F or Ran_F and coherence); degenerate constant constructions fail on identities. No finite certificate route; no computation.',
  gap='A functorial transport of lassos along F*, with composition and identity laws.', receipts=['2408.15184-abs.html', '2408.15184.html', '2408.15184v1.html']),
'364624': dict(outcome='excluded_source_equivalence_and_withdrawn', review='v1 Conjectures 3.13-3.15 and Proposition 3.16 read; current v6 (DMTCS accepted) read: only Conjecture 1.1 (the graph formulation of union-closed) remains; Conjecture 3.14 was removed.',
  attempts='The source itself proves (Proposition 3.16, v1) that the one-pendant-vertex conjecture is equivalent to the union-closed sets conjecture; it was removed in v6. Family lane r216 (326319) parked the same equivalence after a 4+4 exhaustive check. No new computation.',
  gap='Equivalent to the union-closed sets conjecture (flagship).', receipts=['2409.02221-abs.html', '2409.02221.html', '2409.02221v1.html']),
'364715': dict(outcome='excluded_routine_bridge', review='Source Section 7 problem statement read: input (G, k >= 2, d >= 1, r).',
  attempts='k and d are part of the input; restricted to k = 3 the problem is the general d-position problem, NP-complete by Klavzar-Rall-Yero (arXiv:2005.08095, Theorem 2.2). Membership in NP: for a candidate set S, the maximum number of S-vertices on a u-v geodesic of length <= d is computable by a DP over the shortest-path DAG for every pair, so verification is polynomial. A full proof is a routine bridge. Zero credit.',
  gap='None for credit (routine). A fixed-k hardness classification would be a different question.', receipts=['2409.05644-abs.html', '2409.05644.html']),
'364748': dict(outcome='parked_deep_geometric', review='Conjecture 9.2 read in current v4 (Trans. AMS 2025).',
  attempts='Boundary extremality of the normalized spectral set for n > 3 (fails for n = 2, 3 per source). Continuous semialgebraic geometry; no finite certificate route; no computation.',
  gap='A proof that every boundary point is extremal, or an explicit non-extremal boundary point for some n > 3.', receipts=['2409.07682-abs.html', '2409.07682.html']),
'364839': dict(outcome='parked_searched_lean_cost', review='Full source read (Hamano-Sainose-Hibi, Australas. J. Combin. 90 (2024)): definition (Castelnuovo = equality in Hibi volume bound), Theorems 1.6 and 3.2, Corollary 2.2, Conjecture 3.3, Examples 3.4-3.5; Tsuchiya arXiv:2010.13617 Theorems 1.3-1.5 (h*-characterisation) read.',
  attempts='Equivalent h* form: Castelnuovo iff h* = (1,h,...,h,c), h = b + c - d - 1; conjecture is h <= (c+1)(d+1) for c >= 2. Hand computation: prisms R x [0,c+1] over a one-interior-point polygon are Castelnuovo only for the 3-boundary-point triangle (exactly the printed Q(c), attaining the bound). Exact random scouting in d = 3 with a checker validated on all printed examples (cube, Example 3.5, Q(c), P_{c,d}(n)): 4000 + 150000 samples of 6-7 points in [-2,2]^3, 60000 samples of 8 points in [-3,3]^3. Castelnuovo polytopes with c = 1 reached b = 34 (> 29 printed), but c >= 2 examples had b <= 11; no violation. Any counterexample would need a Lean proof of a Lebesgue volume and lattice-point counts: high Lean cost.',
  gap='A structural proof of the upper bound (e.g. via collinearity of interior points for c >= 2) or a c >= 2 polytope with b > cd + 2d + 2.', receipts=['2409.12212-abs.html', '2409.12212.html', '2010.13617-abs.html', '2010.13617.html', '2301.09972-abs.html']),
'364872': dict(outcome='parked_family_already_searched', review='Statement compared with r222 entry 369233 (same three-sevenths conjecture, later source arXiv:2507.08503); original source v1 abstract retrieved.',
  attempts='Identical conjecture to 369233, which r222 parked after exhaustive connected graphs through n = 7, all trees through n = 15 and seeded random sparse graphs to n = 19. Per task instruction, not repeated.',
  gap='As recorded by r222: a global 7/3 amortised strategy or a counterexample beyond those spaces.', receipts=['2409.14180-abs.html', '2409.14180.html']),
'364900': dict(outcome='parked_deep_extremal', review='Statement and its origin (Klimosova-Piguet-Rozhon, Europ. J. Combin. 2020, arXiv:1802.00679) checked via web search; source 2409.15191 lists it as related open problem.',
  attempts='Exact skew-LKS for all n, d, r; only asymptotic dense-case results known. Small counterexamples would have to beat LKS-type extremal configurations; no finite route identified. No computation.',
  gap='Exact skew-LKS proof or explicit extremal counterexample.', receipts=['2409.15191-abs.html', '2409.15191.html']),
'364925': dict(outcome='parked_deep_langlands', review='v3 abstract and statement context.', attempts='Relative Dolbeault geometric Langlands divisor matching; no finite route; no computation.',
  gap='Out of finite-certificate scope.', receipts=['2409.15691-abs.html', '2409.15691.html']),
'365072': dict(outcome='excluded_source_refuted', review='Source abstract and record read; sibling records 365074, 365076, 365077 dispositions (r59, r176) checked.',
  attempts='The source (arXiv:2410.01549) itself presents two classes of graphs that are Ramsey-full but not Gallai-Ramsey-full, disproving Su-Liu. Reproducing it earns nothing. No computation.',
  gap='None (source-refuted).', receipts=['2410.01549-abs.html', '2410.01549.html']),
'365080': dict(outcome='parked_asymptotic', review='Source v2 abstract (m^{3/5-o(1)} general, m^{3/4-o(1)} linear) and record read.',
  attempts='Omega_r(m^{2/3}) surplus lower bound is asymptotic; finite instances cannot settle it. No computation.', gap='Asymptotic proof.', receipts=['2410.01682-abs.html', '2410.01682.html']),
'365097': dict(outcome='parked_deep_contains_open_conjecture', review='Source abstract and Conjecture 4 context; earlier Claude scout r245 rejection of the same conjecture noted.',
  attempts='Regularity of additive complexity for all k-automatic sequences extends the long-open abelian-complexity regularity conjecture; a counterexample would be an infinite object with a non-regularity proof. No computation.',
  gap='General regularity proof or a proven non-regular example.', receipts=['2410.02409-abs.html', '2410.02409.html']),
'365116': dict(outcome='parked_deep_superseded_in_current_version', review='v1 Conjecture 1 and current v4 (SciPost 2025, v4 2026-09-30) read: v4 gives complete ring presentations for all 230 groups with verified E_infinity row-module generators (Theorem 17); the module-support conjecture text does not appear in v4.',
  attempts='No finite route usable in this lane (group cohomology of 230 space groups); likely superseded by v4 computations. No computation.', gap='Check intermediate versions v2/v3 if ever needed.', receipts=['2410.03607-abs.html', '2410.03607.html', '2410.03607v1.html']),
'365134': dict(outcome='parked_searched_beyond_source_theorem', review='Full read of definitions (Definition 3, Remark 3), Lemma 1, Theorem 4 (2-factor with <= 2 cycles), Proposition 5 (P10), Theorem 5 (infinite 2-edge-connected family), Conjectures 7-8, Problems 1-2 of arXiv:2410.04389 (Australas. J. Combin. 91(3) 2025); r89 sibling 365133 noted.',
  attempts=('Exact reformulation: a non-conflicting flow w.r.t. perfect matching F is a labelling of F-edges by a, b, g = a+b with every Fbar-cycle summing to 0 (#a+#g and #b+#g even per cycle) and no Fbar edge joining a and b; 3-edge-colourable graphs are trivial. Checker validated: P10 has no flow; source Theorem 5 graph (l = 1, 34 vertices, all 96 perfect matchings) has no flow; witnesses for 5 named snarks re-verified independently. '
            'Coverage: (i) all labelled cubic multigraphs on Hamilton path 0..n-1 for n = 10, 12, 14 (2205, 29295, 446985 completions; only failures are the two labelled Petersen copies at n = 10); simple n = 16 only 1/32 chunk (81722 completions, 249 non-colourable, all with flow). Probe shows every bridgeless Ham-path cubic (multi)graph with n <= 12 (multi) and n = 14 (simple) has a 2-factor with <= 2 cycles, so this range is already covered by the source Theorem 4. '
            '(ii) Beyond Theorem 4: the P10-e block analysis (block with both cut edges in F always conflicts; otherwise it acts as a "twisted" Fbar edge forbidding equal non-g labels) shows a Ham-path graph contains at most two Petersen blocks (P10-e or P10-v, neither traversable). All bridgeless base multigraphs with Hamilton path on m <= 10 vertices with two end edges replaced by P10-e (8008 graphs), both ends replaced by P10-v (2300) and mixed (4204): every one admits a flow; each of these has all 2-factors with >= 3 cycles. Also P10 with any triangle/digon insertions (308 graphs), Blanusa-type dot products, 2-sums, J5, J7: all have flows. No counterexample.'),
  gap='A proof for graphs whose 2-factors all have >= 3 cycles, or a counterexample needing a forcing mechanism with at most two rigid Petersen blocks.', receipts=['2410.04389-abs.html', '2410.04389.html']),
'365197': dict(outcome='excluded_source_resolved_current_version', review='v1 Conjecture 1.5 and current v2 Theorem 1.3 read.',
  attempts='v2 Theorem 1.3: for every a > 0 there is b > 0 such that g < an implies at least b(2g+n-2) small eigenvalues; taking a = 1 gives the v1 conjecture (n > a(g+1) implies g < n). Zero credit.', gap='None.', receipts=['2410.06093-abs.html', '2410.06093.html', '2410.06093v1.html']),
'365505': dict(outcome='parked_deep_infinite_matroids', review='Conjecture 4.1 read in current v2 (also v1 retrieved); digraph theorem 1.1 noted.',
  attempts='Finitary-matroid generalisation of the source wasteful-partial-linkage theorem; infinite structures, no finite certificate route. No computation.', gap='A matroidal hindrance construction.', receipts=['2410.19583-abs.html', '2410.19583.html', '2410.19583v1.html']),
}
logs = {'364481': ['logs/pre2_len4-60.log'],
        '364839': ['logs/castel3-test.log', 'logs/castel3-s1-4000-b2-k6.log', 'logs/castel3-s2-150000-b2-k7.log', 'logs/castel3-s3-60000-b3-k8.log'],
        '365134': ['logs/ncflow-named.log', 'logs/ncflow-controls.log', 'logs/ncflow-ops-triangles.log', 'logs/ncflow-ops-digons.log',
                   'logs/hampath-n10-multi.log', 'logs/hampath-n12-multi.log', 'logs/hampath-n12-multi-c0of2.log', 'logs/hampath-n12-multi-c1of2.log',
                   'logs/hampath-n14-multi.log', 'logs/hampath-n16-simple-c0of32.log', 'logs/twofactor-n12-multi.log', 'logs/twofactor-n14-simple.log',
                   'logs/two-blocks-m2-8-multi.log', 'logs/two-blocks-m10-multi.log', 'logs/end-blocks-vv-m4-10.log', 'logs/end-blocks-ve-m4-10.log']}
out = {}
for i, n in N.items():
    x = X[i]; aid = x['source_url'].rsplit('/', 1)[1]
    out[i] = {'mathdb_id': int(i), 'title': x['title'], 'source_url': x['source_url'],
              'source_current_version': V.get(aid, {}).get('versions'), 'journal_ref': V.get(aid, {}).get('journal_ref'),
              'provenance': x['provenance'], 'raw_record': f'raw/{i}.jsonl',
              'outcome': n['outcome'], 'campaign_credit': 0, 'review_depth': n['review'],
              'mathematical_attempts': n['attempts'], 'remaining_gap': n['gap'],
              'numerical_logs': logs.get(i, []), 'source_receipts': [r for r in (rec(p) for p in n['receipts']) if r],
              'lean_endpoint': None, 'novelty_clearance': False}
assert len(out) == 20 and set(out) == {str(k) for k in json.loads((D / 'reservation.json').read_text())['ids']}
(D / 'results.json').write_text(json.dumps(out, indent=1, ensure_ascii=False) + '\n')
H = {}
for p in sorted(D.rglob('*')):
    if p.is_file() and p.name not in ('artifact-hashes.json',):
        H[str(p.relative_to(D))] = sha(p)
(D / 'artifact-hashes.json').write_text(json.dumps({'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'sha256': H}, indent=1) + '\n')
print('results', len(out), 'hashed files', len(H))
for i, o in out.items(): print(i, o['outcome'], len(o['source_receipts']))
