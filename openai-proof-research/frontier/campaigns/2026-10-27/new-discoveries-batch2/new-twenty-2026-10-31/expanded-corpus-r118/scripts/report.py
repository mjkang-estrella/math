"""Write results.json: exactly 20 ID-keyed dispositions with provenance (from extracted.json) and source receipts."""
import json, pathlib, re
D = pathlib.Path(__file__).resolve().parents[1]
ex = json.loads((D / 'extracted.json').read_text())
res = json.loads((D / 'reservation.json').read_text())
abs_r, ep_r = {}, {}
for line in (D / 'sources/receipts-abs.txt').read_text().splitlines():
    t, i, a, c, h = line.split()[:5]; abs_r[a] = {'utc': t, 'url': f'https://arxiv.org/abs/{a}', 'http': c, 'sha256': h}
for line in (D / 'sources/receipts-eprint.txt').read_text().splitlines():
    t, a, c, h = line.split()[:4]; ep_r[a] = {'utc': t, 'url': f'https://arxiv.org/e-print/{a}', 'http': c, 'sha256': h}

R = {}
def put(i, depth, outcome, summary, **kw):
    R[str(i)] = dict(review_depth=depth, outcome=outcome, summary=summary, **kw)

put(358266, 'source body located (conj:ECH_spectrum_connected_sum, arXiv:2305.01646 v2); no proof attempt',
    'PARKED_HARD_ANALYTIC',
    'ECH spectral invariants under contact connected sum (limit R->0 equals max-convolution). Famous-type analytic conjecture; no finite mechanism; no Lean route.',
    remaining='A proof requires the holomorphic-curve neck-stretching analysis of the source plus spectral-invariant continuity; out of scope.')
put(358789, 'source body located (conj: matching fields algebraic matroids, arXiv:2306.09693, Macaulay2 package paper); no computation',
    'PARKED',
    'Bases of the algebraic matroid of Gr(k,n) vs union over coherent matching fields. Finite for each (k,n) but needs Groebner-fan/tropical computations (no Macaulay2 here); the source reports agreement in all small examples considered.',
    remaining='Enumerate coherent matching fields for Gr(3,7) or Gr(3,8) and compare basis sets; requires tropical-Grassmannian software.')
put(358810, 'source body read (Conj conj:stab2, arXiv:2306.10154) + own meander-spectrum computation',
    'PARKED_VERIFIED_RANGE',
    'Family 2k|...|2k|1 over 2kr+1: Frobenius, distinct eigenvalues [-2k+1,2k] (r odd) / [-k,k+1] (r even), unimodal: confirmed for all 272 cases with n<=130.',
    coverage='scripts/seaweed.py + seaweed_sweep.py stab2; logs/sw-stab2.log. Calculator validated on four spectra printed in the source.',
    remaining='Closed-form multiplicities in (k,r) not found; literal Lean would need Lie-theoretic spectrum semantics (principal element, Frobenius form).')
put(358812, 'source body read (Epilogue conjecture, arXiv:2306.10154) + own computation + 2026 prior-art abstract (arXiv:2609.27153)',
    'PARKED_PARTIAL_PRIOR',
    'Log-concavity for Frobenius maximal parabolic a|b/n (gcd(a,b)=1): confirmed for all 5228 cases n<=110 (both orientations). Coll (arXiv:2609.27153, 2026-09-22) proves strict unimodality for all, log-concavity for W(mb+-t,b), t<=3, and verifies it when the smaller block is <=128 (any larger block); unrestricted conjecture stated open there. A counterexample would need min(a,b)>=129.',
    coverage='logs/sw-mp60.log, logs/sw-mp61-110.log', remaining='Abstract only read for arXiv:2609.27153 (body unread).')
put(358821, 'source body read (Conj con3, arXiv:2306.10417 v2)',
    'PARKED_SOURCE_FIDELITY_DEFECT',
    'MathDB paraphrase ends "or ML = 1/5"; the source con3 reads "or ML >= 1/4". The literal MathDB text is false for trivial reasons (e.g. ML >= 1/4 tuples), a zero-credit paraphrase defect. Source-scope statement: authors searched all speeds <= 400 and found only k in {1,2}; exhaustive extension beyond 400 exceeds the lane budget.',
    remaining='A structured search (e.g. families (a,b,b+a,b+2a)) beyond speed 400; no mechanism identified.')
put(358922, 'source body read (closing Conjecture, arXiv:2306.15130) + own computation + prior-art theorem body read (Chern-Sellers arXiv:2308.04348, Acta Arith. 215 (2024))',
    'EXCLUDED_KNOWN_FULL_SCOPE',
    'PD_2(2^{k+2}n) == PD_2(2^k n) mod 2^{k+1}. Chern-Sellers Thm 1.1 gives odd k with modulus 2^{k+2}; their Corollary (n->2n) gives even k>=2 with modulus 2^{k+1}; k=0 is Sellers\' own internal congruence PDO(4n)==PDO(n) mod 4. Own check to N=2^20 (k<=18) consistent; modulus sharp at k=6.',
    coverage='scripts/pd2.c; logs/pd2-1M.log', prior_art={'arXiv:2308.04348': abs_r.get('2308.04348'), 'eprint': ep_r.get('2308.04348')})
put(358947, 'source body located (conjec "We strongly believe that if A has SEP, then A_e has SEP at least for semisimple Banach algebras", arXiv:2306.16136)',
    'PARKED_HARD_ANALYTIC',
    'Banach-algebra spectral extension property under unitization; the source gives equivalent conditions only. No finite mechanism.',
    remaining='Would need a construction of a semisimple non-unital Banach algebra with SEP whose unitization fails SEP, or a general proof; no route identified.')
put(358968, 'source body located (conj: rec, arXiv:2306.17719, COLT 2023)',
    'PARKED_COMPLEXITY_HYPOTHESIS',
    'Computational hardness of planted dense subgraph recovery (Chen-Xu threshold). Average-case hardness conjecture beyond current complexity theory (the source proves it conditionally on k-PC); not provable as an exact MathDB solution.',
    remaining='None tractable.')
put(359121, 'source body located (conjecture after thm:special_rate, arXiv:2307.06157 v2)',
    'PARKED',
    'Push-sum gossip rate bound for regular non-transitive graphs; supported by the source\'s numerical experiments. Requires a spectral/tensor-product almost-sure rate analysis; no finite certificate (the bound is an almost-sure Lyapunov exponent).',
    remaining='Would need an analytic argument replacing transitivity; not attempted.')
put(359261, 'source body located (conj:threesegm, arXiv:2307.12458 v4)',
    'PARKED',
    'Outcome segmentation for every 3-move 2-d subtraction ruleset: an infinite-board statement over infinitely many rulesets; "outcome segment" is defined only informally in the source (regular pattern regions). Not finitely checkable.',
    remaining='Needs a formal definition of segmentation; source-definition gap.')
put(359278, 'source body read (Conj conj:k^2+2k, arXiv:2307.13161) + own exhaustive computation',
    'PARKED_NO_COUNTEREXAMPLE_IN_REACH',
    'Set reconstruction M_k(T), n >= k^2+2k. Computed set-injectivity: k=3 fails at n=8,9,10 (69, 6, 2 colliding pairs; source-consistent, below the bound) and is injective at n=11,12,13,14; k=4 injective at n=13 (far below 24). The conjecture domain for k=3 starts at n=15 (10.3M tableaux), beyond the lane caps for the exact set check. No counterexample expected.',
    coverage='scripts/minors.c S mode (union-compatible min-hash with exact verification of all signature groups); logs/minS-n*.log',
    remaining='k=3, n=15 set check (needs ~4x the per-call budget); a general proof would likely follow the source\'s k=2 method.')
put(359279, 'source body read (Conj conj:k+4 and definitions, arXiv:2307.13161) + exhaustive computation + independent exact check + full Lean endpoint',
    'CANDIDATE_REFUTATION_LEAN_COMPLETE',
    'FALSE. k=8, n=12=k+4: hooks T1=[1,5,7,8,12]/2/3/4/6/9/10/11 and T2=[1,2,3,7,10,11]/4/5/6/8/9/12 are distinct SYT with equal multisets of all 19,958,400 8-minors. n=k+4 injective for k<=7 (authors verified k<=5), fails for k=8,9,10,11; n=k+5 fails at k=11 (hooks, n=16). Ordinary strengthening (not formalised): exact hook weight formula mM_k(H(w)) = k! sum_P min(P) [H(w|_P)] and pigeonhole show no bound n >= k+c works for any constant c.',
    lean={'packet': 'lean-packet/TabMinors.lean', 'sha256': '88bb95043b39fc679081ce62ba9101b1d2c8193c216c0db2517b2fb36af55af2',
          'endpoint': 'TabMinors.not_conjecture : ¬ TabMinors.Conjecture',
          'replay': 'outputs/lean-packet-replay.json (strict -DwarningAsError=true build, leanchecker rc 0, 137 local declarations audited, axioms propext/Classical.choice/Quot.sound)',
          'controls': 'outputs/lean-controls.json (source Figure T-8 reproduced; source n=7 equal-M_2 pair has distinct mM_2; two negative controls rejected)',
          'toolchain': 'Lean 4.34.1; mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 cache (read-only, not rebuilt)'},
    proof='outputs/359279-proof.md',
    prior_art='Web searches 2026-11-02 (no follow-up resolution); Herden 2025 slides, DIMACS 2025 abstract, Sepanski 2024 abstracts (sources/prior-359279, receipts-prior-359279.txt): only k=2 and cubic bound; Omega HEAD 0561ac6ffe933c7b218c19879b67fd17a952b5a1 complete D5/Problems path screen negative; OpenAI/math HEAD 4eaee87548250b2682affda7d05d947c05554bae unchanged, cached preprint listing path screen negative. Path screens, not body reads. No journal version located.',
    remaining='Independent statement-fidelity review; significance adjudication by root; journal version (if any) unread.')
put(359324, 'source body located (structural conjecture, arXiv:2307.15380 v3; Lemma Structural in source)',
    'PARKED_HARD',
    'Asymptotic (1-o(1)) structural stability for near-extremal joints configurations; no finite mechanism.',
    remaining='Would need a stability version of the Chao-Yu tight bound; not attempted.')
put(359380, 'source body read (final conjecture, arXiv:2308.01821; authors verified all complete digraphs up to 6 nodes in Macaulay2)',
    'PARKED',
    'Single-edge reversal between nodes p-1 and p preserves the Jacobian matroid of complete digraphs. A p=7 check needs ~3.8e5 generic-rank tests per pair, and a difference certificate needs an identically vanishing minor (hard to formalise). The source contains a commented-out proof of the special case where all edges from [p-2] point into {p-1,p}.',
    remaining='Randomised p=7 sweep with exact symbolic confirmation of any discrepancy.')
put(359425, 'source body read (con:interlacing, arXiv:2308.04015 v1; authors checked 1430 cases: g<=5, n<=5, |mu|<=15/12/10) + own exact cut-and-join computation',
    'PARKED_VERIFIED_RANGE',
    'Interlacing of deformed monotone Hurwitz polynomials. Own recursion (validated against the Narayana identity) with exact Sturm real-rootedness and 60-digit root comparison: no failure for g=0, n<=7, |mu|<=13 (n=6,7 beyond the source); g=0, n<=2, |mu|<=20 (beyond 15); g=1, n<=7, |mu|<=11. The only root ties are the common root t=0.',
    coverage='scripts/hurwitz.py; logs/hurwitz-g0.log, logs/hurwitz-g0-n7.log, logs/hurwitz-g1.log, logs/hurwitz-g0-big.log (n=3 part stopped by the CPU cap)',
    remaining='A proof would need a real-rootedness-preserving form of the cut-and-join operator; none identified.')
put(359582, 'source body located (conj:LE-height-two, arXiv:2308.10214 v2); prior-art search (Soukup arXiv:2311.02203 lists it as open)',
    'PARKED',
    'Almost-completeness of linear-extension counts of height-two posets: an infinite existence statement; no construction found.',
    remaining='Explicit families of height-two posets realising all large integers.')
put(359589, 'source body located (conj:finrem-trees, arXiv:2308.10214 v2)',
    'PARKED',
    'Conciseness of the number of trees in planar graphs (polylog-size realisation of every integer); no construction found.',
    remaining='Explicit planar gadgets with controlled tree counts.')
put(359636, 'source abstract/e-print fetched (arXiv:2308.11907 v2, girth >= 5 classification); prior-art search (no general triangle-free proof found)',
    'PARKED',
    'Triangle-free weighted oriented graphs: CM iff G CM and D unmixed. The bipartite case is known (Pitones-Reyes-Villarreal) and girth >= 5 is the source theorem; the open case is girth 4 non-bipartite. No Cohen-Macaulay test software in this environment.',
    remaining='Enumerate girth-4 non-bipartite CM graphs (small W_2-type) with weights and test CM by polarisation plus Reisner; needs homology code.')
put(359740, 'source body read (Conj conj:3, arXiv:2308.16553 = Discrete Math. 347 (2024) 114182) + own exhaustive search',
    'PARKED_VERIFIED_RANGE',
    'Perfect matchings of K_{2p} with prescribed length list: necessity is the source\'s parity proposition. Exhaustive sufficiency check: all lists for p=3,5,7,11,13 (orbit-reduced by units); all support-3 lists for p=17,19,23: every list with an even number of even entries is realisable. Control p=9 (nonprime) finds 4 non-realisable orbit representatives.',
    coverage='scripts/seating*.c; logs/seating-p13.log, logs/seat3-p17.log, logs/seat4-p19.log, logs/seat4-p23-c*.log',
    remaining='Full p=17 sweep (~3.5e7 orbit representatives, >8000 CPU s) or a Combinatorial Nullstellensatz proof extending Kohen-Sadofschi Costa.')
put(359753, 'source body located (jconjecture after Thm thm:difgamahadamard, arXiv:2309.00117 v2)',
    'PARKED',
    'Gamma-bound vs Hadamard-bound dominance for integer D-optimality: convex-relaxation optimum comparison supported only by numerical experiments; continuous optimisation, no finite mechanism, poor Lean fit.',
    remaining='An analytic comparison of the two relaxations; not attempted.')

assert sorted(R) == sorted(map(str, res['ids'])) and len(R) == 20
for i, e in R.items():
    o = ex[i]; a = o['source_url'].rsplit('/', 1)[-1]
    e.update(mathdb_id=int(i), title=o['title'], source_url=o['source_url'], provenance=o['provenance'],
             source_receipts={'abs': abs_r.get(a), 'eprint': ep_r.get(a)},
             history_check='scripts/history-patterns.txt over frontier md/json (history-matches.txt): only numeric-substring noise and the reservation ledger entry; no prior handling found')
out = {'lane': 'expanded-corpus-r118', 'utc': '2026-11-02', 'credit': 0, 'self_acceptance': False,
       'registries': (D / 'sources/registries/receipts.txt').read_text().splitlines(), 'results': R}
(D / 'results.json').write_text(json.dumps(out, indent=2, ensure_ascii=False) + '\n')
print(len(R), sorted({e['outcome'] for e in R.values()}))
