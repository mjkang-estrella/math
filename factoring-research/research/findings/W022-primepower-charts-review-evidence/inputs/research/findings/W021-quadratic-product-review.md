**W021 independent review: quadratic-exponent product via shifted blocks and multivariate evaluation**

2026-10-08 local / 2026-10-09 UTC. **Accept the primitive in repaired form, as a supplied-product evaluator only.** The block identity, the degree/density count, the Õ(b³) balanced construction, the post-construction digit split and the composite-ring evaluation citation all hold. The repairs are: cite van der Hoeven–Lecerf Theorem 5.5 for the Turing-machine bound, because KU Corollary 4.3 is a RAM statement; charge the binary exponent widths **additively**; pay the exponent setup at every localization level; and restrict any claimed gain to A≠0, because known Õ(√L) methods cover the linear case. No counterexample was found. **Verified new complete factoring improvement: NONE.** No novelty is claimed. The L^{3/4+ε} bound appears to follow directly from known tools, but I did not find it stated in a primary source.

**Frozen scope.** The parent construction `research/hypotheses/W021.md` (135 lines) is frozen at SHA-256 `74eff37c1ce3e4272dbe7f0543b18437667bac196e2f68d4ae62cbbf54bf66d9`. The [verbatim brief](W021-quadratic-product-review-evidence/task-brief.md) and the [input manifest](W021-quadratic-product-review-evidence/input-manifest.json) record hashes and read scope. I read the five mandatory guidance and specification files in full. I audited the W021 header and §A in full. §B served only as a scope limit and was not re-derived. §C was read only so it could be excluded, since it has a separate validation. I read the completed W020 collision review in full as the authority for the consumer contract; I did not re-audit it. STATE, solver code, Lean code and other findings were not read. The parent remains principal researcher. Only this report and its evidence directory were written.

## 1. Exact algebra — accepted

Write f(i)=Ai²+Di+C and i=bk+j with 0≤j<b. Then

```
f(bk+j) = (Aj²+Dj) + j·(2Abk) + (Ab²k²+Dbk+C),
```

so alpha^f(bk+j) = c_j · X_k^j · Y_k with c_j=alpha^(Aj²+Dj), X_k=alpha^(2Abk) and Y_k=alpha^(Ab²k²+Dbk+C). Hence F(X_k,Y_k)=∏_j(1−alpha^f(bk+j)) holds exactly in Z/NZ, where F(X,Y)=∏_j(1−c_jX^jY). Evaluating a polynomial is a ring homomorphism, so the identity uses no inverse other than alpha^(−1). It needs no distinct points, no squarefreeness and no field. Repeated points, zero divisors and zero values are all harmless. The full product is ∏_{k<K}F(X_k,Y_k) times the L−bK tail leaves, where K=⌊L/b⌋. When L<b, only the tail remains.

**Prior form of the identity.** The same block decomposition of a quadratic exponent is the Nogneng–Schost evaluation of sums ∑p^n q^(an²+bn), which costs Õ(√N). The first sublinear bound for those sums is credited to Tao–Croot–Helfgott, Lemma 3.1, as reported by Bostan–Yurkevich §2.2. For a **sum**, the giant factor q^(as²k²+bsk) factors out, leaving a *univariate* P(y) evaluated on a geometric progression. For a **product** of 1−(·), the factor Y_k sits inside every term, so the block polynomial is genuinely bivariate. That difference is exactly why the dense size grows from O(b) to Θ(b³).

## 2. Density, degrees, construction — accepted

The coefficient of Y^h is (−1)^h e_h, an elementary symmetric sum over h-subsets S⊆{0..b−1} of ∏_{j∈S}c_j · X^(ΣS). Its X-support is the interval [h(h−1)/2, h(2b−h−1)/2], of width h(b−h). So deg_Y F=b and deg_X F=b(b−1)/2, and both the support and the dense box are Θ(b³). F is not sparse.

**Balanced product tree.** A node covering s factors has Y-degree s and X-degree below s·b, so it has O(bs²) slots. One level has b/s nodes, for O(b²s) slots. Multiply each pair by bivariate Kronecker substitution: with X-degree bound d_X, map Y↦Z^(2d_X+1). That reduces each product to a univariate product of degree O(bs²) over Z/NZ. Summing O(b²s) over dyadic s≤b gives O(b³) slots. Construction therefore costs Õ(b³) ring operations, or Õ(b³ log N) bit operations with polynomial multiplication over Z/NZ via integer Kronecker substitution. On a multitape Turing machine, the array layout changes add only a logarithmic factor (vdH–L §5 segmentation cost). The certificate (§6) found deg_X F=b(b−1)/2 and deg_Y F=b in every case with b≥2.

**Digit split.** Map X^e Y^h ↦ X0^(e mod b) X1^(⌊e/b⌋) Y^h. Since e≤b(b−1)/2, we get e mod b≤b−1 and ⌊e/b⌋≤⌊(b−1)/2⌋. This is KU Definition 2.3, ψ_(b,2), applied to the X variable only. It is injective on degrees ≤b²−1 and satisfies G(X,X^b,Y)=F(X,Y). The map is linear but **not** multiplicative on the degree box, so it must be applied after the full product is built. The certificate's negative control confirms this. For b≥3, multiplying the relabelled factors gives X0-degree up to b(b−1)/2>b−1 and a different coefficient array, although it evaluates to the same values at (X,X^b,Y). For b=2, the two orders happen to coincide. The split is **necessary** for citation: both KU Corollary 4.3 (d^m) and vdH–L Theorem 5.5 (ℓ̄ⁿ) charge the maximum partial degree. Unsplit, the bivariate box would cost (b²/2)²=b⁴/4. Split, the box is b·(⌊(b−1)/2⌋+1)·(b+1)≈b³/2, with maximum individual degree b. Further splitting happens inside the theorems.

## 3. Exponent and point costs — accepted, with a sharper statement

Let W be the largest bit length among A, D and C. No per-leaf powering is needed. Compute alpha^(−1) once. If the inverse fails, gcd(alpha,N) is already a factor. Then compute by binary powering alpha^(A+D), alpha^(2A), alpha^(2Ab), alpha^(2Ab²), alpha^(Ab²+Db) and alpha^C. Each exponent has O(W+log L) bits, possibly negative, and the integer coefficients cost Õ(W+log L). Finite differences then give everything else:

- c_(j+1)=c_j·r_j, with r_(j+1)=r_j·alpha^(2A);
- X_(k+1)=X_k·alpha^(2Ab) and X_(k+1)^b=X_k^b·alpha^(2Ab²);
- Y_(k+1)=Y_k·s_k, with s_(k+1)=s_k·alpha^(2Ab²);
- the tail starts from Y_K with ratio alpha^(A+D)·X_K.

That is O(b+L/b) multiplications. So the exponent widths enter **additively**, as O((W+log L)·I(log N)). The parent's multiplicative poly(W) factor is valid but needlessly weak. Huge or negative coefficients change nothing else: the products sit in Z/NZ and the exponents are never reduced modulo an unknown order.

## 4. The evaluation theorem: original statements, model, and scope

**KU Corollary 4.3, as read.** For every constant δ>0, multivariate multipoint evaluation over Z/rZ with parameters d, m and N (individual degrees ≤d−1, N points) runs in time (d^m+N)^(1+δ)·log^(1+o(1)) r, "for all d, m, N with d sufficiently large and m≤d^(o(1))". The algorithm MULTIMODULAR handles arbitrary r. It lifts to integers in {0..r−1}, reduces modulo all primes ≤16 log(d^m(r−1)^(md)), recurses t=2 or 3 times, tabulates every point of F_p^m by FFTs, looks the points up, and recombines by CRT. It uses no inversion of point differences, so repeated points and zero values are fine. With fixed m=3, the condition m≤d^(o(1)) holds trivially. The proof applies ψ itself to raise m above a constant c(δ), which absorbs the d^t overhead. **Model:** KU count bit operations, but the lookup and table steps assume random access. vdH–L state explicitly that the result "was stated for random access memory machines" and that parts must be adapted for Turing machines.

**vdH–L, the Turing-machine authority.** This is a multitape Turing machine with binary integer representation (§2). Their first stated contribution is that the KU bounds hold in that model. Their Theorem 5.5 covers 𝔸=(Z/rZ)[z]/(θ), θ monic of degree k, with fixed ε>0 and fixed m̄≥2:

```
(1+ε)^(2m̄n) (N + (m̄n)^(m̄n) ℓ̄^n log^(m̄n)((1+ε)m̄nℓ̄^(1/m̄))) Õ(n^10 ℓ̄^(7/m̄) k log r).
```

Take n=3, ℓ̄=b+1 and m̄=⌈c/ε⌉. Embed Z/rZ into (Z/rZ)[z]/(z²), with k=2, at a constant-factor cost. Their §4 assumes k≥2, so I do not rely on k=1. The result is

```
O_ε((L/b + b³) · b^ε · Õ(log N))
```

for arbitrary composite r=N, with no field assumption. I checked the statements and the proof structures of Theorem 5.5, Theorem 3.10, Theorem 4.4 and Proposition 5.7. I did **not** re-verify their 40-page lemma chain, so this is an imported theorem. KU Corollary 4.3 can still be cited as the original RAM statement.

**Uniformity and constants.** For each fixed ε, the theorem gives one uniform algorithm. Parameter choices are computable from ε, and below the theorem's threshold (Cor 4.3's "d sufficiently large" or vdH–L's η≤ε threshold) a direct loop costs O(1). The exponent is uniform in inputs and non-uniform in ε, which is the usual reading of L^(3/4+ε). The hidden constants are astronomically large: the Theorem 5.5 factor (m̄n)^(m̄n) with m̄n≈21/ε exceeds 200^200 at ε=0.1, and the polylog factor carries exponent m̄n. No feasible crossover is implied.

**Repaired primitive (accepted).** For each fixed ε>0, there is a deterministic multitape Turing machine. Its input is N≥2, alpha, binary A, D, C (width W) and L≥1. Take b=⌈L^(1/4)⌉ (an integer fourth root, then a ceiling). The machine returns ∏_(i<L)(1−alpha^f(i)) mod N, or a gcd if alpha is a nonunit, in

```
O_ε( L^(3/4+ε)·Õ(log N) + (W+log L+1)·I(log N) )
```

bit operations. This includes construction, layout changes, points, the tail and the final product. The parent's form (b³+L/b+1)^(1+ε)·poly(log N, W, log L) is implied by it.

**Localization.** A shift by a gives D'=D+2Aa and C'=C+Da+Aa², of width W+O(log L). The W020 rule computes one child product per level and descends. The L^(3/4+ε) parts form a geometric sum. The additive exponent setup is paid at each of the ⌈log₂L⌉ levels, which gives total cost O_ε(L^(3/4+ε)Õ(log N) + log L·(W+log L)·I(log N)), plus decoding a singleton. Every level rebuilds F, because c_j depends on D'. Balanced halving gives the depth O(log L) that W020 requires. The certificate's shift case S1 matched a direct product over the original indices [9,20).

**Zero leaves.** If A≠0, the integer roots of f come from an exact isqrt of D²−4AC, at cost Õ(W). If A=0 and D≠0, the root is −C/D when it is exact. If A=D=0 and C≠0, there is no zero. f≡0 is rejected. Cutting out at most two indices leaves at most three subintervals, each with the same algorithm, and every remaining leaf has a nonzero integer exponent E=±f(i), as W020 requires. Coverage on the retained domain stays an **external** obligation.

## 5. Equal-input comparators and prior art

Every comparator below gets the same binary input (N, alpha, A, D, C, L) and is charged the same O((W+log L)I(log N)) setup:

| Method | Cost (bit ops) | Scope |
|---|---|---|
| Direct loop with finite differences | O(L·I(log N)) | any A |
| Row-by-row univariate evaluation (parent's own control) | Õ((b³+L)log N) | no saving, as the parent states |
| **W021 + vdH–L Thm 5.5** | **O_ε(L^(3/4+ε)Õ(log N))** | any A; huge constants |
| Linear exponent A=0: (c;q)_L q-Pochhammer, Õ(√L) | Õ(√L log N) | Bostan–Yurkevich Thm 1 over fields; over Z/NZ the monic subproduct and remainder-tree route needs no inverses |
| Sum ∑alpha^f(i) (Nogneng–Schost) | Õ(√L log N) | sums only; a sum does not localize zero factors |

When A=0, X_k=1 and W021 collapses to the univariate q-Pochhammer case. So any claimed advantage is specific to **A≠0**. The quadratic product is **not** q-holonomic in the standard sense: its recurrence coefficient 1−c·q^(n²)r^n is not a polynomial in q^n. Its q-degree also grows like Σn²≈L³/3, while the cited Garoufalidis theorem (title only, BY ref. [66]; not read) says q-holonomic degrees are quadratic quasi-polynomials. So the Õ(√L) q-holonomic machinery does not apply directly. That remark is supporting, not load-bearing. I did not check algebraic bivariate methods such as Nüsken–Ziegler, which are matrix-based and field-oriented. Their interpolation through distinct points is not a drop-in method over composite N with repeated points, and I do not rely on them.

**Prior-art result.** This was a focused, bounded search, with queries, retrieved texts, hashes and read scopes in [source retrieval](W021-quadratic-product-review-evidence/source-retrieval.json). It found the sum analogue, the linear-exponent product and the general KU/vdH–L evaluation theorems. It found no primary source stating a sublinear bound for ∏(1−alpha^(quadratic)). The primitive is a short composition of known ingredients: the Nogneng–Schost/TCH block identity, the ψ map of KU, and KU/vdH–L evaluation. It should be treated as plausibly folklore. **No novelty claim.** I did not show L^(3/4) to be optimal for this problem, and whether a better exponent exists for A≠0 remains open.

## 6. Frozen certificate — passed, toy only

I preregistered the cases and the code ([preregistration](W021-quadratic-product-review-evidence/certificate-preregistration.md), [script](W021-quadratic-product-review-evidence/certificate.py)) and froze them ([freeze](W021-quadratic-product-review-evidence/certificate-freeze.json): prereg `15413ead…`, script `771d5aae…`). I then ran it once with `python3 -I` ([log](W021-quadratic-product-review-evidence/certificate-run.log), [results](W021-quadratic-product-review-evidence/certificate-results.json)).

All 8 cases passed: K1–K7 and the shifted case S1. They cover N∈{15, 91, 1001, 45, 221, 1155, 35}, the zero factor f(0)=0, signed exponents, C=2^70+5, A=−(2^64+3) with C=−2^90, alpha=−1, collapsed points (one distinct point across all 7 blocks in K2), 9 zero leaves in K4, odd tails, and L<b. The checks were:

- C1: block G = F = direct product, for every block and every tail leaf;
- C2: the totals agree;
- C3: the degree bounds hold;
- C4: the shift matches.

The run used 3,873 of 20,000 charged events (3,669 candidate, 204 reference) in 0.0015 s. There were no failures, tuning or reruns. One deviation: the command ran from a scratch cwd (`/tmp/w021run`) with absolute paths, not from the evidence directory as preregistered. Code and cases were unchanged. N1-control evaluations were charged to the candidate meter. The certificate uses monomial evaluation, **not** KU. It establishes exact algebra on these inputs only, not asymptotics.

## 7. Disposition and actual remaining factoring questions

**Accepted (repaired):** an exact supplied-product evaluator that costs O_ε(L^(3/4+ε)Õ(log N)) plus an additive exponent setup on a multitape Turing machine, for arbitrary composite N, with an L^(3/4+ε) localization envelope. **Rejected:**

- any claim of this bound as ring operations in a field;
- any reading of KU Corollary 4.3 alone as a Turing-machine proof;
- any advantage for A=0;
- any novelty.

**Not affected:** W020 stands as accepted, and nothing here reinstates high order, componentwise uniqueness or global-tag recovery. W021 does not compute W019's modular root/carry table. §B's density loss and §C were outside this audit.

What still separates this from factoring:

1. **Coverage.** No quadratic family is known for which, for every composite N, uniform alpha has some leaf with ord_p(alpha) | f(i) for some p|N, with constant probability and the zero indices excluded. Nonunit leaves need f(i) to be a multiple of an unknown local order. A single leaf with a huge smooth exponent already reproduces Pollard p−1 and supplies no general coverage. Quadratic values are sparse: L values spread over a range of order |A|L². Any covering argument must show why quadratic structure hits unknown orders or unknown factor-dependent residues (such as q mod ord_p) more efficiently per occurrence than an arithmetic progression.
2. **Acquisition.** A, D, C and L must be computed from N alone. Every auxiliary prime, root, interval or dyadic schedule must be paid, along with the tail, the small-ℓ fallback and every localization level.
3. **Required length.** For splitting work below a target T·poly(log N), the family needs L^(3/4+ε) ≤ T. The relevant comparator also has to match the model. The W020 consumer is randomized Las Vegas, so randomized bounds apply, including rigorous subexponential randomized factoring (Lenstra–Pomerance, L[1/2,1+o(1)]; cited from memory, not retrieved here), not only deterministic N^(1/5). An exponential-in-log N family length cannot be competitive with that baseline.
4. **Exponent for A≠0.** The question is whether a method better than L^(3/4+ε) exists, or whether a lower-bound style barrier holds for this block structure. This matters only once (1) to (3) are addressed.

No installs, delegation, commits, solver/Lean/STATE/registry edits or parameter sweeps occurred. [Method and read scope](W021-quadratic-product-review-evidence/method-and-read-scope.json), the [verification](W021-quadratic-product-review-evidence/verification.json) and the [delivery manifest](W021-quadratic-product-review-evidence/delivery-manifest.json) preserve the audit boundary.
