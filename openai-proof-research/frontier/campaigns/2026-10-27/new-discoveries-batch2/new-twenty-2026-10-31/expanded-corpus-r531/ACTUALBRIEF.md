# ACTUALBRIEF — expanded-corpus-r531 (Pi DeepSeek V4.1 Flash, high thinking)

Lane: /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r531
Role: research sub-agent. Root orchestrates and adjudicates. No children, no model fallback, no Lean/formal execution, no self-credit.
Campaign state at handback: 57/80 accepted beyond 39 prior, 96 total (unchanged by this lane).
Reservation: exactly the twenty IDs in reservation.json, sha256 a183187bf8c640a3ff9c1e72c12af603c34ba7b9b0ef4f646664fbd8188b8dee; no reselection, no padding.
Result: ZERO qualified survivors. No FULLCANDIDATE.md and no DORMANT-SOL-FORMAL-PLAN.md are authored, because no full-literal survivor exists (see NO-SURVIVOR.md). No dispatch.

## 1. Fixed commands and frozen state
1. FIRST command exactly: `timeout 20 python3 -I -B .../expanded-corpus-r531/bootstrap.py` — exit 0, bootstrap receipt retained.
2. SECOND command exactly: `timeout 140 python3 -I -B .../expanded-corpus-r531/verify_frozen.py before` — {"count": 13, "mismatches": [], "self_only_caps": true}.
3. Every other substantive action ran under the immutable absolute run.py with a UNIQUE_LABEL, Python on stdin, outer `timeout 140`; authored files were written only through the immutable absolute write_lane.py. One exception is disclosed in §7 (a direct intermediate write inside a runner script).
4. No bootstrap rerun, no helper/cap/frozen/TASK modification, no protected-peer read (transitive-bunkbed-reach-formal-deepseek-r20, expanded-corpus-r530 untouched), no r395/r463/r466/r482 quarantined material read or reused.

## 2. Complete authoritative reads (personally read, chunked through the runner)
TASK.txt is 149539 characters. Read in ten contiguous chunks, each at most 15000 characters, in this order:
[0,15000) [15000,30000) [30000,45000) [45000,60000) [60000,75000) [75000,90000) [90000,105000) [105000,120000) [120000,135000) [135000,149539).
inherited-denials.json is 293077 characters. Read in twenty contiguous chunks, each at most 15000 characters:
[0,15000) [15000,30000) [30000,45000) [45000,60000) [60000,75000) [75000,90000) [90000,105000) [105000,120000) [120000,135000) [135000,150000) [150000,165000) [165000,180000) [180000,195000) [195000,210000) [210000,225000) [225000,240000) [240000,255000) [255000,270000) [270000,285000) [285000,293077).
Both reads completed before any network or mathematical investment. All inherited artifact-wide denials are treated as binding. The literal union includes, among others, 0808.1167/10.1016/j.laa.2009.06.023, 10.1137/0208037, 2407.20226/10.1002/rsa.70063, 1803.11032/10.1007/s00373-018-1991-8, 1205.4293 and 1504.06869 (all versions and finals), 1901.09258/10.1088/1742-5468/ab081e, 2105.10903/10.7153/OAM-2022-16-67, the four erdosproblems.com pages 642/809/881/1187, and the registry-root artifacts. None of these was requested.

## 3. Literal provenance for all twenty (read before prioritization)
All twenty literals were read from the immutable corpus `/home/mj-kang/.../lanes/pi-mathdb-full-corpus-inventory-r301/corpus/mathdb-normalized-chunk-*.jsonl`; per-ID chunk path, chunk sha256, one-based line, raw-line length/sha256, trailing-newline flag, raw statement-token sha256, decoded statement sha256, and the complete decoded statement are recorded in `literal-bindings.json` (authored through write_lane.py). Chunks and lines:
- 349943 chunk-0007 line 4282; 346153 chunk-0007 line 519; 347791 chunk-0007 line 2147; 349042 chunk-0007 line 3386.
- 350668 chunk-0008 line 3; 338937 chunk-0005 line 3349; 340221 chunk-0005 line 4623.
- 381331 chunk-0014 line 373; 332023 chunk-0004 line 1486; 326946 chunk-0003 line 1448; 324243 chunk-0002 line 3771.
- 380396 chunk-0013 line 4445; 380398 chunk-0013 line 4447; 378950 chunk-0013 line 3009; 380771 chunk-0013 line 4820.
- 334069 chunk-0004 line 3516; 361816 chunk-0010 line 1054; 368351 chunk-0011 line 2534; 371095 chunk-0012 line 243; 360178 chunk-0009 line 4430.
Metadata selection is not scientific clearance; an open MathDB label is not evidence that a problem is open.

## 4. Network, search, access
Native search: 0 of 3 calls, 0 of 9 query strings. GET: 0 of 48 hops, 0 of 12 per ID. No denials created, no guard/ledger rows written, no payloads fetched, no challenge pages opened. Consequently every prior-art/novelty judgement below is explicitly UNPAID, and no source body, abstract, figure or registry head was read in this lane. The inherited denials were read in full (above) but no request eligibility was exercised.

## 5. Twenty ID-keyed gates (literal / source / ordinary / prior / novelty / significance / formal / independent / acceptance)

### 349943 — Non-negativity of absolutely indecomposable representation polynomials
- literal: full; for a quiver with nilpotent relations over F_q, all coefficients of A(alpha,q) (isomorphism classes of absolutely indecomposable representations) are non-negative integers.
- source: arXiv:2103.00636 (Deng–Hua), unread body, unpaid.
- ordinary: literal review only; Kac-type positivity over finite fields with relations.
- prior: unpaid (0 search, 0 GET); no claim about known resolution.
- novelty: none claimed.
- significance: would be a structural positivity theorem for relation quivers; not addressed.
- formal: a universal endpoint needs quiver representation moduli and polynomial positivity; a counterexample would need an explicit quiver/relation and a negative coefficient; Lean would need finite-field linear algebra plus a certified coefficient computation — expensive but finite in principle; whole-library Mathlib excluded.
- independent: none.
- acceptance: PARK. Precise gap: no finite explicit obstruction identified; proving non-negativity for arbitrary nilpotent relations is out of reach in this lane.

### 346153 — Furstenberg-type restricted-digit counting
- literal: full; for k >= 2 odd primes and digit sets B_i = {0,...,(p_i-1)/2}, with s = sum log(#B_i)/log p_i: if s in (k-1,k), counting function is N^{s-(k-1)+/-epsilon}; if s < k-1 the set is finite.
- source: arXiv:2004.05924 (Han Yu), unread, unpaid.
- ordinary: literal review only; the upper bound is stated to need Schanuel, the lower bound and finiteness are the target.
- prior: unpaid.
- novelty: none claimed.
- significance: Furstenberg-type intersection problem.
- formal: endpoint would need real asymptotics of a digit-restricted set and Schanuel-type input; not a finite kernel-checkable statement as posed.
- independent: none.
- acceptance: PARK. Gap: no finite reformulation; the literal's truth depends on deep Diophantine input.

### 347791 — Colorful Barany–Katchalski–Pach diameter conjecture
- literal: the extracted "conjecture" sentence repeats the preceding conditional conclusion verbatim ("there is an index k ... diameter at least c d^{-1/2}"); the colorful fractional theorem is mentioned but not reproduced.
- source: arXiv:2008.13737 (Dillon–Soberon), unread, unpaid.
- ordinary: literal review only; as extracted the conjecture is not a distinct statement from the displayed hypothesis-conclusion sentence, so the literal is redundant/under-differentiated.
- prior: unpaid.
- novelty: none claimed.
- significance: none established.
- formal: an endpoint would need a finite family of convex sets, diameters and an absolute constant c; not finite-checkable without c.
- independent: none.
- acceptance: PARK. Precise gap: literal duplication/indeterminacy (the "conjecture" text equals the already-printed conditional assertion, and c is unspecified), so no exact target can be bound.

### 349042 — Rosen's lifting conjecture for multiple harmonic sums
- literal: full; if a rational-coefficient combination of weight-k MHS vanishes mod p for all p >= p_1, then for each n >= 2 there are p_n and rationals c^{(l)} (weights k+l, 1<=l<=n-1) so that the corrected combination vanishes mod p^n for all p >= p_n.
- source: arXiv:2012.07067 (Takeyama–Tasaka), unread, unpaid.
- ordinary: sustained p-adic investigation (details §6.2). For k=1 the hypothesis is automatic (H_{p-1}(1) = 0 mod p^2, Wolstenholme). Exact pairing expansions give H_1 = -sum_{m>=1} p^m S_{m+1}, H^{(2)} = 2S_2 + sum_{m>=1}(m+1)p^m S_{m+2}, H_2 = (H_1^2 - H^{(2)})/2 with h=(p-1)/2, S_m = sum_{j<=h} j^{-m}. This yields H_1 - p H_2 = (p^3/2)(S_4 - S_2^2) + p^4(S_5 - S_2S_3) mod p^5. Since S_m = 0 mod p for even m <= p-2 (from H^{(m)} = 0 mod p and pairing), the n=2,3,4 lifts are proved with c^{(1)} = -1 and c^{(2)} = c^{(3)} = 0, for all p >= 7. At n=5 the residual is a genuine p^4 combination of S_4/p, S_5 and the p^3/p^2 parts of H_3,H_4; hand checks at p=7 and p=11 show the c1=-1, c2=c3=0 choice leaves a nonzero p^4 term, so further coefficients are genuinely needed.
- prior: unpaid; no claim that the conjecture is known or unknown.
- novelty: none claimed.
- significance: a lifting principle for MHS congruences; if it were a known finite-MZV/Bernoulli congruence theorem, the target would be an instance of a general law (zero credit) — that bridge is NOT authenticated here.
- formal: a counterexample endpoint would be explicit rationals plus one prime p with a mod p^n non-congruence; Lean would need integer modular arithmetic, inverses and finite harmonic sums over ZMod (p^n) — feasible in principle with Finset/ZMod and decide, but no such witness exists in hand. A full proof would need p-adic/MZV algebra and Bernoulli congruences — not feasible in this lane.
- independent: none.
- acceptance: PARK. Precise gap: the all-k, all-n lifting; concretely, a proof that the mod-p kernel of MHS is generated by the p^l-weighted higher-weight corrections with p-independent rational coefficients, uniformly for all large p. n=2,3,4 at k=1 are paid; n>=5 and k>=2 are unpaid. No counterexample found.

### 350668 — The abcd-conjecture
- literal: full; for K a number field or one-dimensional characteristic-zero function field and n>=3, h(P) < (1+epsilon) rad(P) + C off a proper Zariski-closed subset of the hyperplane sum Z_i = 0.
- source: arXiv:2105.05240 (Looper), unread, unpaid.
- ordinary: literal review only; abc-type height inequality.
- prior: unpaid.
- novelty: none.
- significance: uniform boundedness/dynamical Lang input.
- formal: needs heights, radicals and Zariski-closed subsets over number fields; not finite-checkable.
- independent: none.
- acceptance: PARK. Gap: abc-type, far out of reach.

### 338937 — Makai Jr.'s reverse isodiametric conjecture
- literal: full; for every full-dimensional convex compact K in R^n there is A in GL_n(R) with idq(AK) >= sqrt(n+1)/(n! 2^{n/2}), equality iff a regular simplex; o-symmetric case >= 1/n! with crosspolytope equality.
- source: arXiv:1804.05009 (Gonzalez Merino–Schymura), unread, unpaid.
- ordinary: literal review only; source states the plane case solved, open n>=3.
- prior: unpaid.
- novelty: none.
- significance: reverse isodiametric problem.
- formal: needs convex bodies, volume, diameter, GL_n action and equality cases in R^n; not a finite kernel endpoint.
- independent: none.
- acceptance: PARK. Gap: no finite reduction; open for n>=3 per literal.

### 340221 — Equivalent Riemann hypothesis conjecture for the constrained random model
- literal: full but model-dependent; a realisation of RM outside the stated error bound must violate prod_{k=0}^{pi(sqrt n)} rho_k(n+a) <= n for some n.
- source: arXiv:1808.09447 (Tunstrom), unread, unpaid.
- ordinary: literal review only; the objects RM, rho_k and the constrained model are defined only in the source.
- prior: unpaid.
- novelty: none.
- significance: RH-equivalent formulation.
- formal: would require analytic number theory and the random model; no finite endpoint.
- independent: none.
- acceptance: PARK. Gap: RH-equivalence, definitions source-dependent, out of reach.

### 381331 — Folklore generic Newton polygon conjecture for triangular exponential sums
- literal: full; over an open dense subspace of polynomials with triangular Newton polytope, for every finite character chi, every k>=1 and every admissible i_k, the Newton polygon agrees with the infinite Hodge polygon at x = x_k + i_k.
- source: arXiv:1701.00254 (Ren), unread, unpaid.
- ordinary: literal review only; p-adic Newton/Hodge polygon coincidence.
- prior: unpaid.
- novelty: none.
- significance: genericity input to the paper's main theorem.
- formal: needs p-adic polygons, Newton polytopes and generic openness; not finite-checkable.
- independent: none.
- acceptance: PARK. Gap: generic p-adic geometry; no finite witness.

### 332023 — The SCV–FCV comparison conjecture
- literal: full; for every N>=3 and w>=1, the tilde-SCV space equals CMZV_{w,N} over Q(xi_N), and FCV_{w,N} is isomorphic to CMZV_{w,N}/2 pi i CMZV_{w-1,N} via the displayed map.
- source: arXiv:1512.03691 (Singer–Zhao), unread, unpaid.
- ordinary: literal review only; the level-1 analogue is stated proved by Yasuda, level N>=3 is the target.
- prior: unpaid.
- novelty: none.
- significance: comparison of colored MZV spaces.
- formal: needs cyclotomic fields, MZV/FCV spaces and algebra isomorphisms; heavy algebraic infrastructure, not a finite endpoint.
- independent: none.
- acceptance: PARK. Gap: deep algebraic comparison; no finite obstruction.

### 326946 — Effective boundedness for parametrized Thue inequalities
- literal: full; there is an effectively computable kappa_1 depending only on alpha with max{|x|,|y|,e^{h(alpha epsilon)}} <= m^{kappa_1} for all solutions of |F_epsilon(x,y)| <= m, m>=2, xy != 0, degree >= 3.
- source: arXiv:1312.7205 (Levesque–Waldschmidt), unread, unpaid.
- ordinary: literal review only; the paper proves restricted-unit bounds.
- prior: unpaid.
- novelty: none.
- significance: effective Diophantine bounds.
- formal: needs algebraic number theory, units, heights and effective bounds; not finite-checkable.
- independent: none.
- acceptance: PARK. Gap: effective uniformity over all units; out of reach.

### 324243 — Lang–Silverman conjecture for Drinfeld modules
- literal: full; for every finite extension L/K, every r>=1 there is epsilon>0 with hat h_phi(x) >= epsilon max{h(j_phi), deg D_{phi/L}} for every rank-r Drinfeld module and non-torsion x.
- source: arXiv:1210.2340 (Ingram), unread, unpaid.
- ordinary: literal review only.
- prior: unpaid.
- novelty: none.
- significance: canonical-height lower bound.
- formal: needs function fields, Drinfeld modules, canonical heights and discriminants; not finite-checkable.
- independent: none.
- acceptance: PARK. Gap: Lang–Silverman-type, far out of reach.

### 380396 — Algebra conjecture for parameterizing motivic local systems
- literal: full but source-dependent; existence of a commutative algebra A in C_{F_q} with semisimple numerical realizations and a Galois x Z/n-equivariant bijection onto motivic irreducible local systems with ramification divisor D.
- source: arXiv:math/0702206 (Kontsevich), unread, unpaid.
- ordinary: literal review only.
- prior: unpaid.
- novelty: none.
- significance: motivic local systems.
- formal: needs tensor categories, l-adic representations and Galois equivariance; not a finite endpoint.
- independent: none.
- acceptance: PARK. Gap: deep motivic structure; no finite reduction.

### 380398 — Tensor-functor realization conjecture for finite-field motives
- literal: full but source-dependent; for every prime p a tensor functor Phi_p to the Karoubi closure with tensor-functor isomorphisms to the numerical realizations and Frobenius preservation.
- source: arXiv:math/0702206 (Kontsevich), unread, unpaid.
- ordinary: literal review only.
- prior: unpaid.
- novelty: none.
- significance: Master Conjecture of the source.
- formal: needs tensor categories, realization functors and Frobenius; not finite-checkable.
- independent: none.
- acceptance: PARK. Gap: deep motivic/tensor-categorical, out of reach.

### 378950 — Segal Conjecture for infinite groups
- literal: full; for G with a finite model for underline E G and finite proper G-CW X, pi^s_n(EG x_G X) = pi_G^n(X) completed at I_G, with the BG and n=0 corollaries.
- source: arXiv:math/0504051 (Lueck), unread, unpaid.
- ordinary: literal review only.
- prior: unpaid.
- novelty: none.
- significance: completion theorem extension.
- formal: needs equivariant stable homotopy, Burnside rings and I-adic completion; not feasible.
- independent: none.
- acceptance: PARK. Gap: deep homotopy theory.

### 380771 — Polynomial bound on integer zeros of straight-line computable polynomials
- literal: full; there is a>0 with n(f) < tau(f)^a for every f in Z[x], where tau is minimal SLP length and n(f) the number of distinct integer zeros.
- source: arXiv:math/9904130 (Malajovich), unread, unpaid.
- ordinary: sustained generic-attempt (details §6.3). Degree doubling gives only n(f) <= deg f <= 2^{tau(f)}. Product-tree constructions give tau ~ r log r for r roots, so n ~ tau/log tau, consistent but not a proof. No short generic argument and no applicable source theorem was found without source reading; no counterexample family found.
- prior: unpaid.
- novelty: none.
- significance: arithmetic complexity vs root count.
- formal: a counterexample endpoint would be an explicit integer polynomial, an explicit SLP and a certified root count; Lean could encode Int polynomials, an SLP as a list of operations and a Finset of roots and decide — feasible for a finite witness. A universal proof needs a complexity-theoretic height/degree argument — not feasible here.
- independent: none.
- acceptance: PARK. Precise gap: a lemma bounding the number r of distinct integer roots by tau(f)^a; only r <= 2^tau is available. No counterexample.

### 334069 — Deligne's character-valued polynomiality conjecture for parabolic-bundle counts
- literal: full but notation-heavy; there is A^{b;m}_mu(t) in Ch(S_mu)[t] with coefficients in the positive cone, evaluating at q to the geometrically indecomposable parabolic-structure counts for every finite field, every lambda and every compatible reduced divisor.
- source: arXiv:1609.04875 (Letellier), unread, unpaid.
- ordinary: literal review only; the source proves n=2.
- prior: unpaid.
- novelty: none.
- significance: character-valued refinement of polynomiality.
- formal: needs parabolic bundles over P^1, Chen-homology/positive cone and finite-field counts; not a finite endpoint.
- independent: none.
- acceptance: PARK. Gap: deep geometric/representation-theoretic; n>=3 unpaid.

### 361816 — Arad–Herzog conjecture on products of non-trivial conjugacy classes
- literal: full; for a non-abelian finite simple group G and n>=2, the product of n non-trivial conjugacy classes is not a conjugacy class.
- source: arXiv:2402.06703 (Beltran–Camina–Felipe–Melchor), unread body, unpaid; the literal itself records confirmations for sporadic groups, for squares, and open general case.
- ordinary: sustained character-theoretic investigation (details §6.1). Derived the exact criterion, zero propagation, the n=2 inverse-class exclusion, and excluded n=3 and n=4 counterexamples in A5 and PSL(2,7) by full character-table case analysis.
- prior: unpaid (0 search, 0 GET).
- novelty: none claimed.
- significance: a general structural statement about class products; no new invariant claimed.
- formal: a counterexample endpoint is a concrete finite simple group with explicit classes and a set-product equality; Lean can encode a permutation group on Fin n, conjugation orbits, subset products and prove equality by decide (propext/Classical.choice/Quot.sound only) for tiny groups — feasible in principle. A universal proof would need CFSG-level classification of character zero sets and ratios — not feasible here.
- independent: none.
- acceptance: PARK. Precise gap: no general contradiction and no counterexample; the missing lemma is that the system chi(1)^{n-1} chi(d) = prod_i chi(c_i) (all irreducible chi) has no solution with d != 1 for non-trivial classes in a finite simple group. n=3,4 excluded only for A5 and PSL(2,7).

### 368351 — MC-circle distribution conjectures
- literal: INCOMPLETE. The statement reproduces several explicit claims (monotonicity of R_n, existence of largest n-enclosing lattice circles, pairwise distinct rho_n, arbitrarily long MC/non-MC runs, density >80% and <20%, infinite strong MC numbers with positive density, at least six circumference points for strong MC circles) and then asserts that "the stated majority, minority, and percentage claims about mirror symmetries and axes of symmetry in items (10)--(19) hold exactly as listed in the source" — items (10)-(19) are not reproduced in the corpus literal.
- source: arXiv:2505.06234 (Zhao), unread, unpaid.
- ordinary: literal review only; claims are extrapolated from computations for n<1100.
- prior: unpaid.
- novelty: none.
- significance: none established.
- formal: some claims are finite lattice-circle statements (explicit circle, interior count, circumference count) and could in principle be kernel-checked; the density/asymptotic and symmetry-majority claims are not finite endpoints. Items (10)-(19) are missing, so no literal endpoint exists.
- independent: none.
- acceptance: PARK. Precise gaps: (a) literal incompleteness for items (10)-(19); (b) every quantitative claim needs lattice-point counting and a maximality proof, and this lane forbids enumeration/numerical tests, so no certified counterexample is available.

### 371095 — Conjectured maximum purity of absolutely PPT qutrit-qudit states
- literal: the piecewise formula and the attaining eigenvalue vectors are printed, but "absolutely PPT" is not defined in the literal (definition only in the source).
- source: arXiv:2510.19508 (Dung–Khoi), unread, unpaid.
- ordinary: literal review only. For n=2 the formula gives purity 88/400 = 0.22 with eigenvalues (0.3,0.3,0.1,0.1,0.1,0.1); the maximally mixed 6-dimensional state has purity 1/6 < 0.22, so the claimed value is at least plausible; no independent verification of the absolute-PPT characterization or of the maximum.
- prior: unpaid.
- novelty: none.
- significance: quantum-information extremal purity.
- formal: an endpoint needs the absolute-PPT spectral characterization and a linear-algebra inequality; a counterexample would be an explicit 3 x n state, its eigenvalues, and a proof of absolute PPT with larger purity — feasible only with the source characterization; Lean would need complex matrices and spectral data, expensive.
- independent: none.
- acceptance: PARK. Precise gap: definition of absolute PPT absent from the literal; no state construction or upper-bound proof; no counterexample.

### 360178 — Classification conjecture for maximal subgroups containing the cyclic factor
- literal: INCOMPLETE/UNDER-SPECIFIED. G is given by a presentation with parameters n,r,t, and X = G<c> with o(c)=m>=2 and G cap <c> = 1, but the action of c on G is nowhere specified; "a subgroup of largest order" has no tie-breaking rule; the parameter restrictions under which the six-case table is claimed are absent; the literal also contains a stray ")" in "Let $G$)".
- source: arXiv:2310.00345 (Hao Yu), unread, unpaid.
- ordinary: literal review only. The six cases prescribe M = <a^i><c>, cores and quotients Z2, D8, A4, S4, (Z4 x Z2).Z4, S4; because the extension X is not determined by the literal, no quantified statement is available to test.
- prior: unpaid.
- novelty: none.
- significance: none established.
- formal: with a repaired literal (explicit action of c, explicit parameter ranges, explicit maximality tie-break) a counterexample would be a finite group, a subgroup and its core/quotient, kernel-checkable by decide; the literal as extracted cannot be formalized.
- independent: none.
- acceptance: PARK. Precise gap: literal under-specification (c-action, tie-break, parameter range), so neither proof nor counterexample is well-posed.

## 6. Sustained derivations (what was actually proved, and what was not)

### 6.1 Arad–Herzog (361816)
Setup: G finite, C_i non-trivial conjugacy classes, D a conjugacy class. In the centre Z(CG) of the group algebra, the class sums C^_i form a basis and the Fourier component at an irreducible character chi is omega_chi(C) = |C| chi(c)/chi(1). Hence C1...Cn = D as sets (all products, exactly D) is equivalent to C^_1 ... C^_n = lambda C^_D with lambda = prod|C_i|/|D|, and therefore to
  (E) chi(1)^{n-1} chi(d) = prod_{i=1}^n chi(c_i)   for every irreducible chi and every d in D.
Derived consequences:
(a) Zero propagation: if chi(c_i) = 0 for some i then chi(d) = 0 for every d in D, so D lies in the zero set of chi.
(b) For n=2, summing (E) over chi gives sum_chi chi(1)chi(d) = sum_chi chi(c1)chi(c2). The left side is 0 because d != 1 (column orthogonality with the trivial character). The right side equals |C_G(c1)| when C2 = C1^{-1} and 0 otherwise. Hence C2 = C1^{-1} is impossible; this is also immediate because 1 lies in C1 C1^{-1}.
(c) For general n, summing (E) over chi gives sum_chi prod_i chi(c_i) = 0.
Counterexample exclusion for n=3, n=4:
- A5 (classes 1A, 2A size 15, 3A size 20, 5A/5B size 12; degrees 1,3,3',4,5). For n=3, D in {2A,3A,5A,5B}: chi_5 (degree 5, values 5,1,-1,0,0) forces a zero factor for D=5A/5B, then chi_3 (values 3,-1,0,alpha,beta, alpha=(1+sqrt5)/2) forces two identity factors (9alpha cannot be a product of two non-identity values), contradiction; for D=3A, chi_5 forces -25, which needs two identity factors; for D=2A, chi_4 (degree 4, values 4,0,1,-1,-1) forces a 2A factor, and chi_3 forces -9, impossible from {-1,0,alpha,beta}. For n=4 the same magnitude/zero arguments exclude every D (chi_5 gives 125 or -125 or 0 against products bounded by 1; for 5A the chi_3 magnitude bound phi^4 < 27 excludes 27alpha).
- PSL(2,7) (classes 1A, 2A size 21, 3A size 56, 4A size 42, 7A/7B size 24; degrees 1,3,3,6,7,8). For n=3: D=2A needs chi_4 (degree 6, values 6,2,0,0,-1,-1) to give 72 from {2,0,-1}, impossible; D=3A needs chi_5 (degree 7, values 7,-1,1,-1,0,0) to give 49 from {-1,1,0}, impossible; D=4A needs chi_5 to give -49, impossible; D=7A needs chi_6 (degree 8, values 8,0,-1,0,1,1) to give 64 from {0,-1,1}, impossible. n=4 is excluded by the same magnitude bounds.
Not proved: (E) has no solution in general. The n=2 case is exactly the classical Arad–Herzog statement and is not proved here; a full proof needs a classification-level analysis of character zero sets and ratios. No counterexample was found in A5 or PSL(2,7) (n=3,4), nor by the inverse-class argument.

### 6.2 Rosen lifting (349042)
Let p be an odd prime, h=(p-1)/2, S_m = sum_{j=1}^{h} j^{-m} in Z_p. Pairing j with p-j gives, for every j <= h,
1/j + 1/(p-j) = -sum_{m>=1} p^m j^{-(m+1)}, and
j^{-2} + (p-j)^{-2} = 2j^{-2} + sum_{m>=1}(m+1) p^m j^{-(m+2)}.
Hence H_1 = -sum_{m>=1} p^m S_{m+1} and H^{(2)} := sum_{j=1}^{p-1} j^{-2} = 2S_2 + sum_{m>=1}(m+1) p^m S_{m+2}. With H_2 = (H_1^2 - H^{(2)})/2 one obtains exactly
  H_1 - p H_2 = (p^3/2)(S_4 - S_2^2) + p^4 (S_5 - S_2 S_3)  (mod p^5).
For even m <= p-2, H^{(m)} = sum_{j=1}^{p-1} j^{-m} = 0 mod p (classical), and pairing gives H^{(m)} = 2S_m mod p, so S_m = 0 mod p. Therefore S_2 = S_4 = 0 mod p for p >= 7, and the right side is 0 mod p^4 for every p >= 7. Thus for k=1 the lifting holds for n=2,3,4 with c^{(1)} = -1 and c^{(2)} = c^{(3)} = 0. At n=5 the surviving p^4 term is governed by S_4/p, S_5, the p^3-part of H_3 and the p^2-part of H_4; hand checks at p=7 (residual 3p^4 + ...) and p=11 (residual 7p^4/2 + 3p^4) show that the choice above is not enough, so the general n>=5 case genuinely needs further rational coefficients and an identity among these p-adic quantities. Not proved: the all-k, all-n statement. Not disproved: no p and no coefficient set was shown to be impossible uniformly; the n=5 obstruction is a missing identity, not a counterexample.

### 6.3 Integer zeros vs SLP length (380771)
Only the degree bound is elementary: each SLP operation at most doubles the degree, so deg f <= 2^{tau(f)}, hence n(f) <= 2^{tau(f)}. A product tree for r distinct integer roots costs O(r log r) operations, so r ~ tau/log tau is attainable, consistent with a polynomial bound but not a proof. No short generic argument was found: bounding integer roots by SLP length needs a height/degree or algebraic-complexity input that is not available in this lane, and no applicable primary theorem was authenticated (0 GET). No counterexample family: a refutation needs n(f) superpolynomial in tau(f), i.e., exponentially many distinct integer roots computed by a short SLP; the obvious falling-factorial family needs Omega(n log n) operations and no subexponential construction is known to me. Not proved, not disproved.

## 7. Process disclosures and retained failures (honest)
1. `task-read-c00000-c15000` (first attempt) failed with exit 1: a bash `printf` format string consumed `%` characters in the Python source, so the runner received a truncated/mangled script. Its zero-byte .output.txt and exit-1 receipt are retained; the read was redone under a new label `task-read-c00000-c15000-r2` with a heredoc, not an unchanged rerun.
2. `probe-interface-1` was a single run.py interface check (it printed CWD, ARGV and the lane listing). No `--help`, no `LABEL --` probe, no relative runner.
3. DEVIATION: the corpus location scan (`corpus-locate-20`) wrote `literal-scan-raw.json` directly from inside the runner instead of through write_lane.py. That file is retained as a non-canonical intermediate and is not used as the authoritative provenance record; the authoritative record `literal-bindings.json` is authored through write_lane.py. No other direct authored writes occurred.
4. `probe-write-1.txt` is a write_lane interface probe; retained.
5. TASK.txt and inherited-denials.json were read in exactly the chunk ranges listed in §2; no chunk exceeded 15000 characters. `task-read-c270000-c285000` returned 23155 characters because the file ends at 293077.
6. No outer `timeout 140` was omitted on any run.py invocation. No cap (affinity 2 CPUs, CPU 115 s, AS 6 GiB, group RSS 6 GiB, deadline 130 s, arena 2) was raised or bypassed. Sampled RSS peaks are in the receipts; native tool telemetry and separate writer peaks are unavailable, so no universal process-compliance claim is made.
7. No search call, no GET, no denial, no ledger mutation, no budget mutation. `search-budget.json` remains calls_used 0, queries_used 0.
8. The model-policy file `model-policy-sol-only.json` and every GPT-6.1 Sol / Sol-only mention in inherited text are historical and were not applied; this lane ran as instructed on Pi DeepSeek V4.1 Flash with no children and no fallback.

## 8. Resource and access inventories
- Runner invocations: see every `*.receipt.json` in this lane (interface probe, size/reservation probe, ten TASK chunk reads including the failed first attempt, twenty denial chunk reads, corpus location, two literal reads, lane tree inspection, and later the manifest computation). Each receipt records the exact `-c` source, caps, affinity, wall/CPU, sampled RSS and exit.
- Literal bindings: twenty raw/token/decoded bindings in `literal-bindings.json`, with chunk path, chunk sha256, one-based line, raw-line length and sha256, trailing-newline flag, statement-token sha256 and decoded-statement sha256.
- Source/read/figure/HTTP/access/search inventories: source bodies 0, abstracts 0, figures 0, HTTP hops 0, access-inventory rows 0, search calls 0, search strings 0.
- Frozen inputs: thirteen bindings, verified before with zero mismatches; standalone frozen-after run at the end (see `frozen-after.json`).

## 9. Formal (Lean) feasibility, per main route
- 361816: counterexample endpoint needs a concrete finite simple group, conjugacy classes as orbits, subset products and equality. Feasible in principle with `Equiv.Perm (Fin n)`, `Finset`, `MulAction.orbit` and kernel `decide` for tiny groups; imports outside a whole-library Mathlib are acceptable under the updated cap note. Universal proof: not feasible (CFSG-level).
- 349042: counterexample endpoint needs explicit rationals and one prime with a mod p^n non-congruence; Lean needs `ZMod (p^n)`, finite harmonic sums over `Finset.range p`, inverses and a certified inequality — moderate but feasible in principle. Full proof: not feasible (p-adic/MZV algebra).
- 380771: counterexample endpoint needs an integer polynomial, an explicit SLP and a certified root count; Lean can encode `Polynomial Int`, an SLP as a list of operations and the root `Finset`, with `decide` — feasible for a finite witness. Universal proof: not feasible (complexity lower bound).
- 360178: no endpoint can be stated until the literal is repaired (c-action, tie-break, parameter ranges); after repair a finite counterexample would be kernel-checkable by `decide`.
No Lean, compiler, checker or formal API was executed in this lane.

## 10. Disposition
Zero qualified survivors; twenty ID-keyed parks with the precise gaps above; no acceptance, no credit, no dispatch. Root alone adjudicates.
