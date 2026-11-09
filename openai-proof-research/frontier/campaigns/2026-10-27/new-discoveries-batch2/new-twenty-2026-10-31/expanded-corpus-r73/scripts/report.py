# Assemble results.json (exactly 40 ID-keyed entries), outputs/search-coverage.json and outputs/web-searches.json.
import json,pathlib,hashlib
D=pathlib.Path(__file__).resolve().parents[1]
X=json.loads((D/'extracted.json').read_text())
R=json.loads((D/'reservation.json').read_text())
assert sorted(map(int,X))==sorted(R['ids'])==sorted(R['ids']) and len(X)==40
def src(a): 
  k='math_'+a.split('/')[-1]; p=D/'sources'/f'{k}.eprint.receipt.json'
  return json.loads(p.read_text()) if p.exists() else None
COMMON_HIST='Prior-campaign history: lane rg over campaign *.md/*review*.json/*results*.json/*ledger*.json found only this reservation list and hash-substring coincidences (history-matches.txt); keyword screens of ledger.json and prior-campaign-context.json found no family overlap.'
REG='Live registries 2026-11-01: Omega HEAD f9b5efa07de8323d8b34adbeb8b22da41c9263f7 (complete D5 tree 0a7a4cf..., Problems tree 38e4ba9..., untruncated) and OpenAI/math HEAD 4eaee87548250b2682affda7d05d947c05554bae (cached complete preprints listing, HEAD unchanged): no reserved-ID path hits; keyword hits unrelated (outputs/registry-screen.json). Path screen only.'
E={}
def put(i,outcome,depth,summary,prior=None,search=None,remaining=None,lean=None):
  E[str(i)]=dict(outcome=outcome,review_depth=depth,summary=summary,prior_art=prior,finite_search=search,remaining=remaining,lean=lean)
put(377968,'excluded_known_refuted','full source note read (Korkmaz math/0307146, Conjecture 2); prior-art body read (Kotschick math/0307362, Example ex:involutions and the mapping-class example)',
 'Conjecture 2 (||f||_tau=0 implies f torsion) is false: if f=st with s,t involutions then f^n is a product of at most two torsion elements, so ||f||_tau=0, and products of two involutions of infinite order exist in Mod_g (e.g. iota * t_b iota t_b^{-1} = t_{iota(b)} t_b^{-1}). Independently derived here, but already in Kotschick (2003/2004), who also cites McCarthy-Papadopoulos pseudo-Anosov products of involutions.',
 prior='D. Kotschick, Quasi-homomorphisms and stable lengths in mapping class groups, arXiv:math/0307362 (sources/prior_math_0307362.eprint): Example ex:involutions and the Dehn-twist example state vanishing stable torsion length for infinite-order products of involutions.',
 remaining='None; known. Lean infeasible anyway (mathlib has no mapping class groups).')
put(377973,'parked_hard','source title/statement located (Crawley-Boevey math/0307246); no finite mechanism',
 'Irreducible multiplicative Deligne-Simpson criterion (Kostov / Crawley-Boevey-Shaw form). Infinite family over conjugacy classes; partial later progress by Crawley-Boevey on the multiplicative preprojective approach (not re-read). No tractable finite counterexample mechanism; parked.',
 remaining='Status of the sufficiency direction in later literature not audited.')
put(378033,'excluded_known_refuted','source conjecture read (Borcea math/0309233, Conjecture send3); prior art at abstract/search-snippet level',
 'Local-maxima conjecture for Sendov: M. J. Miller, Unexpected local extrema for the Sendov conjecture (arXiv:math/0505424; J. Math. Anal. Appl. 2008) exhibits locally extremal polynomials not of the form z^n+e^{i theta} (degree 8 and further degrees per later versions).',
 prior='Miller arXiv:math/0505424 (abstract/snippet lead; body unread in this pass).',remaining='Body confirmation of Miller degree-8 example as local maximum of d on S_n in the exact sense of the source.')
put(378034,'parked_hard','source conjecture and surrounding results read (Borcea, Conjecture operator; Theorem converse)',
 'Operator reformulation of Sendov + Phelps-Rodriguez equality. Source: known for dim <= 8 [BX]. Analytic, infinite; equality clause interacts with Miller-type local extrema but no refutation of this exact statement identified. Parked.',
 remaining='Whether Tao (2020) large-n Sendov plus equality analysis settles the inequality part for large n; equality characterization not analysed.')
put(378069,'excluded_refuted_in_source','source abstract/introduction and counterexample section located (Hoffmann math/0310160)',
 'Source title and introduction: the Boden-Hu conjecture holds precisely up to rank eight (N <= 8); Proposition examples gives counterexamples in all other cases (Section Counterexamples).',prior='The cited source itself.')
put(378115,'parked_hard','source statement located (Hales, Good orbital integrals math/0311353)',
 'Motivic fundamental lemma as identity in a motivic coefficient ring. Related transfer-principle work (Cluckers-Hales-Loeser) not audited; no finite mechanism. Parked.')
put(378162,'parked_no_counterexample','source definitions read (Borcea math/0312321: C_n, A_n(Omega), A, A-prime; Conjecture conj1 and preceding Propositions counter1/counter2)',
 'For n=2 and T=(1-lam D)e^{lam D} (lam real) the conjecture holds outright: the root difference d of TP satisfies d^2 = Delta + 4 lam^2 with Re d * Im d fixed, so real spread increases and imaginary spread decreases. Numerical diagnostic: 80000 random tests (n=3..6, T1=(1-lam D)e^{lam D}, T2=e^{-aD^2}) found no failure (logs/borcea.log).',
 search='scripts/borcea_scan.py: 40000 random monic complex polynomials, degrees 3-6, two operator families, seed 20261101; floating point, diagnostic only.',
 remaining='General A-prime operators and n>=3 unproved; Lean of complex root majorization infeasible here.')
put(378285,'excluded_known','source introduction read (math/0403121, lines around Conjecture conj)',
 'Andrews A_{4,3,3}=B^0_{4,3,3}: source states Andrews et al. (1994) gave an analytic proof and a combinatorial proof was given later; the present source proves the A_{5,3,3} analogue.',prior='Andrews et al. 1994 (cited in source); body unread.')
put(378324,'parked_hard','source statement located (Pemantle-Steif, Robust phase transitions..., math/0404092)',
 'Phase-transition criterion for Heisenberg models on general trees; infinite probabilistic; source proves robust version and branching number 1 case. No finite mechanism; parked.')
put(378371,'parked_hard','source statement located (Solomon, On twisted zeta-functions at s=0, math/0404379)','Refined Rubin-Stark reciprocity; arithmetic, no finite mechanism; parked.')
put(378395,'candidate_counterexample_lean_verified','full Section 4 read (definitions of P_Delta^{p,q,r} as cone over columns, collapsing, Proposition 2pq, Table 1, Conjecture conj:col); exact certificate and literal Lean endpoint',
 'REFUTED at (p,q,r)=(4,4,5). Explicit functional l (a,b,c integer tables in lean-packet/PROOF.md) defines a facet F of P_Delta^{4,4,5} (valid on all 80 columns; tight columns span rank 43 = 44-1) whose five slices have pairwise distinct zero patterns; any collapsing to 4x4x4 merges two slices of the 5-state variable and pulled-back faces have identical patterns on merged slices, so F is not obtained by collapsing from P_Delta^{4,4,4}. Found via the correspondence facets <-> coarsest regular subdivisions of Delta_{p-1} x Delta_{q-1}: 54 height matrices give 5-cell and 6 give 7-cell coarsest subdivisions of Delta_3 x Delta_3, all certified exactly (outputs/collapsing-444r-certificates.json).',
 prior='Bounded searches (2026-11-01) found no refutation or 4x4xr (r>4) facet computation; source Table 1 stops at 4x4x4. Not a known result in checked sources; global novelty not claimed.',
 search='scripts/coarse.py: all height matrices with normalised entries 0..2 (2x3), 0..3 (3x3), 0..3 (3x4), 0..1 (3x5), 0..1 (4x4); scripts/facet_cert.py exact rational facet certification.',
 remaining='Independent fidelity/significance review and root acceptance.',
 lean='lean-packet/proof/MathDB378395.lean: MathDB378395.Main.collapsing_conjecture_false : not CollapsingConjecture; fresh extracted strict -j1 -DwarningAsError=true replay PASS, leanchecker PASS, 134 local declarations audited, axioms only propext/Classical.choice/Quot.sound (lean-packet/fresh-replay-receipts/result.json).')
put(378409,'parked_hard','source located (Martelli survey math/0405250)','Minimal volume among hyperbolic manifolds with fixed boundary type; geometric topology, no finite mechanism; parked.')
put(378465,'excluded_known','source abstract and Theorem t:main read (Czygrinow-Hurlbert-Kierstead-Trotter math/0406053)','The source itself proves the conjecture: every graph of diameter at most d and connectivity at least 2^{2d+3} is Class 0.',prior='The cited source, Theorem t:main.')
put(378478,'parked_vague','source located (Krauth-Loebl, Jamming and geometric representations of graphs, math/0406166)','Existence of a finite algorithm for stable representations: algorithmic existence statement with source-internal notions; no exact finite counterexample mechanism. Parked.')
put(378479,'parked_vague','source located (Krauth-Loebl math/0406166)','Uniqueness of nontrivial stable spherical representation up to symmetry and jammed implies stable: continuous geometric configurations; no finite mechanism identified. Parked.')
put(378528,'parked_hard','source located (math/0407291, Exterior differential algebras and flat connections on Weyl groups)','Majid conjecture Lambda_w = Lambda_quad for simply-laced Weyl groups: relates to Nichols/Fomin-Kirillov algebras whose finite-dimensionality is open from S_6; computation infeasible with available tools. Parked.')
put(378541,'parked_numerical','source located (math/0407432, Painleve I boundary value problem)','Uniqueness of the solution attaining Xi_min(x0): ODE/numerical; not a finite object; Lean infeasible. Parked.')
put(378542,'parked_numerical','source located (math/0407432)','[Delta]=0 approximate symmetry of slope differences for Painleve I: numerical observation over a continuum; not exact-finite; parked.')
put(378574,'parked_hard','source located (Banuelos-Kulczycki math/0408267)','Spectral-gap rectangle lower bound for symmetric stable processes; analysis; parked.')
put(378584,'excluded_known','full source read (Cooper-Solymosi math/0408396); prior-art body read (Cooper-Hyatt arXiv:2501.02331 Theorems thm:fractional and thm:lexleast)',
 'Confirmed by Cooper-Hyatt (Des. Codes Cryptogr. 2025): every permutation with (q-1)/2 collinear triples is an extended fractional linear map and g is the lexicographic least. Independent exhaustive lex-order search agrees for all primes 3 <= n <= 19.',
 prior='Cooper-Hyatt arXiv:2501.02331 (sources/prior_2501.02331.eprint).',search='bin/lexperm, bin/lexperm2: exhaustive pruned lexicographic DFS for n=3,5,7,11,13,17 (single runs) and n=19 split by sigma(3) in 3..11 (logs/lex19-*.log); first solution equals g in every case.')
put(378587,'excluded_known_likely','source statement located (Berger-Breuil survey math/0408404)','Mod-p compatibility for crystalline representations of G_Qp and Pi(V): established in the p-adic Langlands literature (Berger, Berger-Breuil, Colmez); bodies not re-read in this pass. No finite mechanism in any case.',remaining='Exact reference/body confirmation not performed.')
put(378637,'excluded_known','source statement read (Green, Finite field models math/0409420)','Cap-set exponent mu(3)<1 proved by Ellenberg-Gijswijt (Annals 2017) via the Croot-Lev-Pach polynomial method.',prior='Ellenberg-Gijswijt (standard; body not re-read).')
put(378663,'excluded_refuted_in_source','full source read (Kellner math/0410297, Conjecture conj-bern-num, Theorem theor-Ap-small and exception table)','The source disproves Bacher conjecture: 149 exceptions among irregular pairs p < 10^6, first (6449,4884) and smallest index (15823,482).',prior='The cited source itself.')
put(378665,'excluded_known','source abstract located (Matsuki math/0410302)','The record itself and source state the conjecture is completely solved affirmatively (closed/open orbits earlier, non-Hermitian type earlier, Hermitian type in this paper).')
put(378697,'excluded_known','source statement located (math/0411020); prior-art body read (Boij-Soderberg arXiv:0803.1645 Theorem thm:MultConj)','Huneke-Srinivasan multiplicity conjecture for Cohen-Macaulay R/J: proved by Eisenbud-Schreyer (2009) (CM case) and extended by Boij-Soderberg.',prior='Boij-Soderberg arXiv:0803.1645 (sources/prior_0803.1645.eprint) introduction and Theorem thm:MultConj.')
put(378740,'parked_no_counterexample','source Section with Notation def of Ctr, Lemma details Ctr, Theorem unique Zt, computed table and conjecture read (Geramita-Migliore-Sabourin math/0411445); later work read (arXiv:1109.3610 introduction, Proposition pro.atmostt)',
 'Known affirmative for s <= 9 points (all t=4 cases) and s=11 (t=5,r=1; arXiv:1109.3610). Open literal cases begin at t=5, r=2,3,4. Exhaustive screens found no configuration with h_{2X} below the Z_{t,r} reference (modular ranks are one-sided sound: rank mod p <= rank over Q).',
 prior='Geramita-Ha (et al.) arXiv:1109.3610.',
 search='bin/dbl: all N-subsets of affine grids 4x4 (t=4 r=1..3; t=5 r=1..4) and 5x5 (t=4 r=1); bin/dbl2 with scripts/dbl_driver.py: seeded line-arrangement pools (batches A-E: K=6..8 lines, coefficient boxes 2..3, optional extra points), all N-subsets per pool with C(pool,N)<=60000, cases (5,2),(5,3),(5,4),(6,1..5). Totals in outputs/dbl-*.json. Z_{5,r} references reproduce the source table; Z_{6,r} computed from two independent C_{6,r} realizations.',
 remaining='A proof for s=12,13,14 would need a case analysis of the Geramita-Ha type; Lean formalization of fat-point Hilbert functions is infeasible in this pass.')
put(378771,'parked_hard','source located (Examples of Shimura correspondence for level p^2, math/0412104)','Central-value formula; arithmetic of modular forms; status (theorem vs conjecture) unclear in record; no finite mechanism; parked.')
put(378797,'parked_hard','source located (Yezzi-Mennucci, Metrics in the space of curves, math/0412454)','Existence of minimizing homotopies for E^A; calculus of variations; parked.')
put(378803,'parked_hard','source conjecture read (Nill math/0412480)','Lattice-point maximality of the Sylvester reflexive simplex among lattice polytopes with one interior point, d>=4: verified d=4 by Kreuzer-Skarke classification per source; no feasible finite search for d>=5. Parked.')
put(378902,'excluded_known','full relevant source read (Gao-Panigrahi-Thangadurai math/0503095, Open problem and Conjecture 1); prior-art bodies read (Cao EJC 13 (2006) N9 full; DeVos-Goddyn-Mohar Adv. Math. 220 (2009) Conjecture 1.7, Corollary 1.8 and its proof)',
 'Resolved by DeVos-Goddyn-Mohar Corollary 1.8 (which implies Gao-Thangadurai-Zhuang Conjecture 1.7(1) = this statement); Cao 2006 for two prime divisors. Independent exhaustive search agrees.',
 prior='DGM 2009 (sources/prior_dgm_AM220.pdf; text/prior_dgm_AM220.txt), Cao 2006 (sources/prior_ejc_v13i1n9.pdf).',
 search='bin/zerosum (validated against brute force zerosum_brute.py, counts 2,4,2,26,84): all multisets for n in {4,6,8,9,10,12} and every 1<=k<=n-2; n=14 k=6, n=15 k=3 (finds the known sub-range counterexample) and k=4; no counterexample in the conjectured range.')
put(378912,'parked_hard','source located (Anderson, Topics in conformally compact Einstein metrics, math/0503243)','Cusp Poincare-Einstein deformation conjecture; geometric analysis; parked.')
put(378923,'parked_hard','source located (Deitmar, Invariant triple products, math/0503379)','Convergence of triple-product integrals for general semisimple G; harmonic analysis; parked.')
put(378981,'parked_hard','source located (German, Klein polyhedra..., math/0504483)','Oppenheim lattice conjecture (implies Littlewood in dimension 3); famous open problem; not pursued.')
put(379012,'excluded_formulation_defect','source conjecture conj2 and definitions read (Migliore-Nagel-Romer math/0505229, including Theorem modulecodim2 and the pure-resolution corollary); prior-art body read (Boij-Soderberg 0803.1645 Theorem thm:MultConj)',
 'The literal statement (no Betti factor) is false trivially: N=(R/(x_1))^2 is torsion with c=1, m_0=0, M_1=1, e(N)=2 > 1; the source codimension-one theorem fails on the same module. This exploits an obvious missing beta_0 factor (direct-sum padding), so it is not credited. The corrected inequality e(N) <= beta_0 prod M_i/c! with the equality clause is Boij-Soderberg Theorem thm:MultConj.',
 prior='Boij-Soderberg arXiv:0803.1645.',remaining='Published version of the source not checked for a corrected statement.')
put(379043,'excluded_known','source located (Deza-Huang-Stephen-Terlaky math/0506003); prior art at abstract/search level','Maximum colourful simplicial depth d^{d+1}+1 proved by Adiprasito-Brinkmann-Padrol-Patak-Patakova-Sanyal (arXiv:1607.00347).',prior='arXiv:1607.00347 (abstract lead; body unread).')
put(379064,'parked_heuristic','source located (Farmer, The maximum size of L-functions, math/0506218)','Random-matrix heuristic prediction for maxima over families; analytic, not exact-finite; parked.')
put(379065,'parked_heuristic','source located (Farmer math/0506218)','Truncated-zeta maximum prediction; analytic heuristic; parked.')
put(379106,'parked_hard','source located (Jerdonek dissertation math/0506558)','Girth conjecture for Heegaard splittings; 3-manifold topology; parked.')
put(379108,'parked_hard','source located (Jerdonek math/0506558)','Simple-curve minimum-girth conjecture; topology; parked.')
put(379120,'excluded_nonexact','source conjecture read (math/0507234 Conj: bounded by approx d^2/3 ...)','Statement asserts an approximate bound ("approx 1/3 d^2 ..."); no exact quantified claim to prove or refute. Not pursued.')
assert len(E)==40 and set(E)==set(X)
out={}
for i in sorted(X,key=int):
  x=X[i]; e=E[i]
  out[i]=dict(mathdb_id=int(i),title=x['title'],source_url=x['source_url'],statement=x['statement'],provenance=x['provenance'],
             source_receipt=src(x['source_url'].split('/abs/')[-1]),**e,history=COMMON_HIST,registries=REG,
             discovery_credit=0,root_acceptance='not accepted; zero credit unless root accepts')
(D/'results.json').write_text(json.dumps(out,indent=1,ensure_ascii=False)+'\n')
cov={i:dict(outcome=E[i]['outcome'],finite_search=E[i]['finite_search'],review_depth=E[i]['review_depth']) for i in E}
(D/'outputs/search-coverage.json').write_text(json.dumps(cov,indent=1)+'\n')
from collections import Counter
print(Counter(e['outcome'] for e in E.values()))
