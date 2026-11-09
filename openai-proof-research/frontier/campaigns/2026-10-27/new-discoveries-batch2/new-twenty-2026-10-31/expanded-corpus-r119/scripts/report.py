"""Write results.json: exactly 20 ID-keyed dispositions with provenance (extracted.json) and source receipts."""
import json, pathlib
D = pathlib.Path(__file__).resolve().parents[1]
ex = json.loads((D / 'extracted.json').read_text())
res = json.loads((D / 'reservation.json').read_text())
abs_r, ep_r = {}, {}
for line in (D / 'sources/receipts-abs.txt').read_text().splitlines():
    p = line.split()
    abs_r[p[2]] = {'utc': p[0], 'url': f'https://arxiv.org/abs/{p[2]}', 'http': p[3], 'sha256': p[4]}
for line in (D / 'sources/receipts-eprint.txt').read_text().splitlines():
    p = line.split()
    ep_r[p[1]] = {'utc': p[0], 'url': f'https://arxiv.org/e-print/{p[1]}', 'http': p[2], 'sha256': p[3]}
R = {}
def put(i, depth, outcome, summary, **kw):
    R[str(i)] = dict(review_depth=depth, outcome=outcome, summary=summary, **kw)
FAMOUS = 'statement-level screen + arXiv abstract page (no e-print body read)'
put(359900, FAMOUS + '; Chan-Pak arXiv:2309.05764', 'PARKED_HARD_COMPLEXITY',
    'C_=P-completeness of EqualityStanley_k for large k: a complexity-class conjecture; no finite mechanism or Lean route.',
    remaining='Would need a C_=P-hardness reduction for equality cases of Stanley inequalities; out of scope.')
put(360113, FAMOUS, 'PARKED_HARD_COMPLEXITY',
    'Average-case computational indistinguishability of planted vs unplanted number partitioning (any c>1). Unconditional proof would separate complexity classes; no finite mechanism.',
    remaining='Only restricted-algorithm (e.g. low-degree) evidence is conceivable; not a resolution.')
put(360324, FAMOUS + '; Miller-Scheinerman Monte Carlo source', 'PARKED_HARD_ANALYTIC',
    'Existence of limiting proportions of character-table zeros (types I, II, all) in S_n: asymptotic analytic statement; finite computation cannot decide a limit.',
    remaining='An asymptotic theory of zero proportions in S_n character tables; out of scope.')
put(360345, 'source e-print read (Def def-TverbergGraph, Thm generalconnected, conjecture after line 450; arXiv:2310.08563) + own exhaustive d=1 computation',
    'PARKED_VERIFIED_RANGE',
    'Existential k(d) for all d is not finitely checkable. The k(1)=1 clause was checked exhaustively on the line: for r<=6, n<=12, the r-partition graph is connected for every n>=2r and disconnected at n=2r-1 (isolated vertices). Source has no d=1 theorem.',
    coverage='scripts/tverberg1d.py; logs/tv1d.log (r=2..6, n=2r-1..min(2r+2,12)).',
    remaining='A proof of k(1)=1 alone is only one clause (parameter case) of the conjecture; general d needs order-type theory beyond reach.')
put(360565, FAMOUS, 'PARKED_HARD_COMPLEXITY',
    'PSPACE-completeness of Builder-Blocker general position B- and B\'-games: needs a hardness reduction; no finite mechanism.',
    remaining='PSPACE-hardness reduction (e.g. from avoidance/Geography); out of scope for this lane.')
put(360575, 'source e-print read (Prop prop: regard decomp, Conj conj: on indecomp, Def WBI action, interval description; arXiv:2310.20571) + own exact computation',
    'PARKED_VERIFIED_RANGE',
    'Computed End(M_P) for every disconnected skew shape with no disconnected ribbon via the weak-Bruhat-interval module on tau_0-reading words (cyclic on sigma; End = {v: Ann(sigma)v=0}; local iff dim End/rad = 1, trace-form radical mod p=2147483629). All conjecture shapes indecomposable for |P|=5..8 (|P|=7: 60 shapes, |P|=8: 229 shapes); |P|=9 partial (57 shapes, all indecomposable) before CPU caps. Controls: every shape with a disconnected ribbon decomposes (source Prop); |P|<=6 matches source; source example 21435 reproduced.',
    coverage='scripts/hecke.py; logs/hecke-ctl.log, hecke-conj6.log, hecke-conj6b.log, hecke-conj7.log, hecke-conj8.log, hecke9-0..5.log (partial).',
    remaining='No counterexample through |P|=8. A proof needs an idempotent-free argument for X^{(1)} box ... box X^{(k)} with no consecutive projective factors (Huang decomposition only splits consecutive ribbons). Radical computed mod a large prime: diagnostic, not a certificate.')
put(360623, FAMOUS + '; Soukup arXiv:2311.02203', 'PARKED_HARD_COMPLEXITY',
    'Sign Imbalance not in #P: an unconditional non-membership would imply complexity separations; no finite mechanism.',
    remaining='Out of scope.')
put(360681, 'source e-print read (Conj conj2, Props on transitive non-interval examples S_n wr C_k, Thm thrm:41 for products; arXiv:2311.04489)',
    'PARKED',
    'Interval property of minimal-base cardinalities for primitive groups. Source counterexamples for transitive groups use imprimitive coset actions of S_n wr C_k. No primitive-group library (GAP/Magma) available here; hand analysis of product actions S_n wr C_k on n^k points, PGL(2,q) on the line and S_n on 2-sets gives intervals.',
    remaining='A search of primitive groups beyond the source authors\' library range needs GAP-free Schreier-Sims plus a primitive-group catalogue; not built.')
put(361110, 'source abstract/title + e-print located (arXiv:2312.07716: bipartite POP classes have regular insertion encodings)',
    'PARKED',
    'The "if" direction (bipartite => rational) is the source theorem. The converse needs a non-bipartite POP class with rational GF (needs a rationality proof) or a non-rationality proof for all non-bipartite POP classes; every non-bipartite POP contains a 3-chain, so its class contains Av(sigma) for some sigma in S_3, which gives no contradiction.',
    remaining='No concrete counterexample mechanism; proofs of non-rationality for infinite families are out of scope.')
put(361189, 'source e-print read in full for the conjecture (Conj 050522f, Thm mainTheorem, Appendix A; arXiv:2312.10914 v3) + own exact exhaustive search beyond the authors\' range',
    'PARKED_VERIFIED_RANGE',
    'Conjecture verified for n=8 (first case beyond the source n<=7): with L_7=56 (source), all 87,956 deficient 8-path forests with l_1>=56 are impossibly burnable; the search closes at m=31 (no deficient forest for m>=31). Also computed L_8=68: no deficient 8-path forest with l_1>=68, exactly one with l_1=67, namely (67,67,67,67,102,102,102,102) at m=26 (impossibly burnable), so Question mainQuestion holds for n=8 and L_8=M_8+1, consistent with Conj 071222a (L_8<=96). Delta_8=54<L_7=56: the slack appears first at n=8 (deficient, not impossibly burnable: (53,53,53,53,53,53,82,84) at m=22; none with l_1>=54). n=9 with L_8=68: m=25..29 complete and m=30 extensions + first 10^6 balanced candidates, 37,861 deficient forests, all impossibly burnable; remainder stopped by CPU caps.',
    method='Reduction lemma: if T in D(m) (deficient, parts>=L, order m^2) has largest part > 2m-2+L, removing 2m-1 from it gives a member of D(m-1). Hence D(m) is contained in Ext(D(m-1)) together with Balanced(m) (all parts in [L, 2m-2+L]), and each candidate is decided exactly by DFS over {1,3,...,2m-1} with exact-key failure memo and parity/count pruning. Validated against source: n=4 (47 deficient), n=5 (608), n=6 (5185), n=7 full table (178,1588,5460,9536,9572,1294,79,4,0) and the unique (45,45,45,45,72,74,74).',
    coverage='scripts/burn.c, burn2.c, burn_driver.py; logs/burn-n*.log, logs/burn2-n*-L*-m*-s*.log; outputs/burn/*/state.json (intermediate D(m) binaries removed; reproducible).',
    remaining='No counterexample; Delta_n appears to grow slower than L_{n-1}. A proof for all n remains open (source remarks the induction on L_{n-1} is doubtful).')
put(361213, 'source e-print read (Thm sec4 thm2, Rmk sec4 rmk1, Conj, Thms sec3 thm4/thm5; arXiv:2312.11995) + prior-art e-print read (arXiv:2410.15070 Thm sec3 thm4, Thm sec3 thm6) + own proof and computation',
    'EXCLUDED_PUBLISHED_RESOLUTION',
    'The only open part (d_perp = q-p for even s) follows from arXiv:2410.15070 (same authors, Oct 2024; Finite Fields Appl.), Thm 3.4/3.6 with h=(p^i-1)/2, i=1, gcd(1,s)=1: C^perp has parameters [q+1,4,q-p] for all s>1. The LRC claims then follow from the source Thm sec3 thm5. Independently we found a short explicit proof: the Cayley transform t -> (t-w)/(t-w^q) maps PG(1,p) into U_{q+1}, giving the codeword (a,b)=(w-w^{pq}, w^{pq}-w^q) with exactly p+1 zeros; verified numerically for (p,s) in {(3,2),(5,2),(7,2),(3,3),(3,4),(5,3),(11,2),(13,2),(5,4),(7,3),(3,6)}, with brute-force d_perp=q-p for q=9,25. Zero credit.',
    coverage='scripts/bch.py; logs/bch.log',
    prior_art={'arXiv': '2410.15070', 'theorem': 'sec3 thm4 (h=(p^i-1)/2, p odd, 0<i<s, m=gcd(i,s)): C^perp four-weight [q+1,4,q-p^m]'})
put(361744, FAMOUS + '; Zhou-Wang-Yan arXiv:2402.03878 cites Kelly (3/2+o(1))n', 'PARKED_HARD_FAMOUS',
    'Exact Haggkvist threshold delta*(D)>(3n-3)/2 for oriented graphs: famous; only asymptotic version (Kelly) known. The MathDB paraphrase\'s "resolved" wording refers to the approximate result. No finite route.',
    remaining='Exact-threshold stability analysis; out of scope.')
put(382188, FAMOUS, 'PARKED_HARD_PROBABILISTIC',
    'Random NTRU-lattice GKP code distance conjecture ("likely to be good"): probabilistic/heuristic statement without a crisp finite form.',
    remaining='Not a well-posed finite claim; would need a probabilistic shortest-vector theorem for random NTRU lattices.')
put(382203, FAMOUS, 'PARKED_HARD_COMPLEXITY',
    'Polynomial-time branchwidth for H-minor-free graphs (H embeddable in torus and projective plane): algorithmic structure theory; no finite mechanism.',
    remaining='Out of scope.')
put(382215, FAMOUS, 'PARKED_HARD_COMPLEXITY',
    'Polynomial-time homotopy type of independence complexes of circle graphs: algorithmic conjecture; no finite mechanism.',
    remaining='Out of scope.')
put(353172, 'source abstract (arXiv:2201.00571); e-print located', 'PARKED_NO_TOOL',
    'Cone conjecture on characteristic dependence of Betti numbers of J^2: needs minimal free resolutions over several characteristics of squares of edge ideals of cones over known char-dependent graphs (>=10 vertices); no Macaulay2/Singular available.',
    remaining='Betti tables of J^2 in char 0 vs 2 for the smallest char-dependent graphs; infeasible without a CAS.')
put(353177, 'source e-print read (Def q, Gray-code section, Conj BKV; arXiv:2201.00782 v6) + own computations',
    'PARKED_VERIFIED_RANGE',
    'Source evidence: n<=5, q in {2,3,4,5}. The 1-flip graph on W_{q,n} is bipartite by weight parity; DP shows |#even-#odd|<=1 for all q<=12, n<=40 (periodic pattern), so no parity obstruction. Hamiltonian paths (= 1-Gray codes) found and checked for q=2,3,4 with n<=14 and q=5 with n<=13; no leaves or isolated vertices.',
    coverage='scripts/qdec.py (DP validated by brute force q<=5, n<=12), scripts/qdec_ham.py; logs/qdec.log, logs/qham.log (stopped by CPU cap during q=5,n=14).',
    remaining='A general recursive construction for all q (the q=1 case needed a sophisticated construction in Baril-Kirgizov-Vajnovszki); not attempted.')
put(353203, 'source e-print read (uniqueness definition, Cor K_{2,t}(e), Prop p:K33, Conj; arXiv:2201.01798) + survey e-print (arXiv:2406.05509: Thm t:main TAR-iso => same X-sets after relabelling; still lists the conjecture as open) + own SAT computation and partial proof',
    'PARKED_STRONG_LEAD',
    'By the published reduction (Bong-Carlson-Curtis-Haas-Hogben 2023, survey Thm t:main), uniqueness of PD-TAR(K_{s,t}) is equivalent to: K_{s,t} is the only graph without isolated vertices on A u B having exactly its power dominating sets. Encoded exactly as SAT (minimal PD sets via forcing chronologies; maximal non-PD sets via forts; E != E(K_{A,B})) and solved with cadical: UNSAT (uniqueness) for (s,t) in {(3,4),(3,5),(4,4),(4,5),(3,6),(4,6),(5,5),(3,7),(5,6),(3,8),(3,9),(4,7)}; new beyond the source are (3,6),(3,7),(3,8),(3,9),(4,6),(4,7),(5,5),(5,6). (3,3) is SAT only via relabelled K_{3,3} (all-pairs family is fully symmetric; source proves it). Controls (2,3),(2,4) SAT as the source predicts. Partial proof: blocker duality shows the minimal sets N[fort] are exactly B u {x,y} and A u {u,v}; if every minimal fort Psi_xy with N[Psi]=B u {x,y} is {x,y}, then H=K_{s,t} (proved).',
    coverage='scripts/pdsat.py, pdsat_ablate.py, pdcheck.py; logs/pdsat-*.log, logs/abl-*.log (ablation: every constraint group is needed). CNFs removed (regenerable).',
    remaining='Lemma needed: for s,t>=3, (s,t)!=(3,3), no minimal fort Psi with N[Psi]=B u {x,y} meets B (equivalently, no "poor" q in B with N_A(q) in {x,y} together with "poor" p in A with N_B(p) in {u,v}). With it the conjecture is proved; a literal Lean endpoint would also need the TAR-isomorphism reduction formalized.')
put(353321, 'source e-print read (definitions of n-good/good ordered graphs, monotone caterpillars; arXiv:2201.07637 v2)',
    'PARKED',
    'Goodness is a statement for all n (r_<(G,K_n)=(m-1)(n-1)+1); a counterexample needs a good non-caterpillar tree (proof for all n) and a proof needs a non-goodness construction for each forbidden pattern lifted to every supertree. No finite route.',
    remaining='Lifting lemma: if G contains a forbidden ordered pattern of Fig. 2 then G is not n-good for some n.')
put(353451, 'source e-print read (Def def:stressed, Thm thm:Ehrhart-relaxation-improved, Conj RelaxationPositive, eq. tildephi; arXiv:2201.12442 v3) + own exact computation',
    'PARKED_VERIFIED_RANGE',
    'By the source formula E_{Rel_H M}(t) = E_M(t) + (n-s)/(n-1)! * binom(t-1+n-s,n-s) * tildephi_{r,s,n}(t), the conjecture holds whenever tildephi_{r,s,n} has nonnegative coefficients. Exact sympy expansion: all coefficients positive for all 363 triples 1<=r<=s<=n-1, n<=13, so the conjecture holds for every matroid on at most 13 elements; no counterexample route.',
    coverage='scripts/phitilde.py; logs/phit.log',
    remaining='Positivity of tildephi_{r,s,n} for all (r,s,n) (source Conjecture big conjecture route); not proved here.')
assert len(R) == 20 and set(R) == {str(i) for i in res['ids']}
HIST = 'scripts/history-patterns.txt over frontier md/json (history-matches.txt): only numeric/hash-substring noise and the reservation ledger entry; no prior handling found'
for i, e in R.items():
    x = ex[i]; a = x['source_url'].split('/abs/')[-1]
    e.update(mathdb_id=int(i), title=x['title'], source_url=x['source_url'], provenance=x['provenance'],
             source_receipts={'abs': abs_r.get(a), 'eprint': ep_r.get(a)}, history_check=HIST)
out = {'lane': 'expanded-corpus-r119', 'utc': __import__('datetime').datetime.now(__import__('datetime').timezone.utc).isoformat(),
       'credit': 'none claimed; no candidate endpoint; zero credit unless root accepts', 'self_acceptance': False,
       'registries': {'omega_HEAD': '4a11a6467d4ba3682c7630cd22c551cd11074cc6 (2026-11-03T01:40:51Z; newer than root-known ddeafbc8)',
                      'openai_math_HEAD': '4eaee87548250b2682affda7d05d947c05554bae (unchanged)',
                      'scope': 'HEAD receipts + truncated Omega recursive tree path screen (no ID hits; keyword hits unrelated); no proof reading, no candidate needed it',
                      'receipts': 'sources/registries/receipts.txt'},
       'results': R}
(D / 'results.json').write_text(json.dumps(out, indent=1, ensure_ascii=False) + '\n')
print(len(R), sorted({e['outcome'] for e in R.values()}))
