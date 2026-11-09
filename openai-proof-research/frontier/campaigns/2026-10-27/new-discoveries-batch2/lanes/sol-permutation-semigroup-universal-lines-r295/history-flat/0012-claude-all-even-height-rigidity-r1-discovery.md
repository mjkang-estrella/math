# All-even height rigidity: mathematical record (claude-all-even-height-rigidity-r1)

Outcome: **no full proof, no counterexample, zero nominations.** No PROOF.md is delivered.
Counts are unchanged: 9 additional, 39 total, next number 40. Only the root accepts, counts or stages.

## 1. Source fidelity (read from the frozen full body)

The source is Kalmanovich and Nivasch, *All-even sets in R^2 and R^3*, arXiv:2610.38864v1 [cs.CG],
28 Oct 2026. The frozen copy is `frozen/even.pdf`, sha256 `e70c94f4…9464ad`. It is byte-identical to the
r213 original. The text was extracted with `pdftotext -layout` and all 32 pages were read.

* **Definitions (p.3).** n_S(ℓ) is the number of affine lines parallel to ℓ that meet S. ℓ is an *odd line
  direction* if n_S(ℓ) is odd. A set is *line-all-even* if it has no odd line direction.
* **Conjecture 2.1 (strong conjecture, p.4), literal statement.** "Let S ⊂ R³ be a finite set that affinely
  spans R³. Then there exists a direction ℓ ∈ P(R³) such that n_S(ℓ) is odd." This is a universal
  statement over all finite spanning S, with no size bound. Prop 2.2 shows it implies the weak Conjecture 1.2
  (Seoane-Sepúlveda's question).
* **Theorem 3.3 (p.6).** Conjecture 2.1 is equivalent to "every all-even set A ⊂ R² is height-rigid".
  Height-rigid means every admissible z : A → R is affine. Admissible means: whenever q−p = λ(s−r) with
  p≠q and r≠s, then z(q)−z(p) = λ(z(s)−z(r)).

  I checked the proof. Lemma 3.1 shows the lift of A by an admissible z is line-all-even iff A is all-even.
  Lemma 3.2 gives a generic projection that creates no new parallelisms. The reverse direction uses that
  projection plus a shear. The argument is correct as written. Section 4 restates rigidity as
  rank R(A) = n−3, and Corollary 4.2 restates all-evenness as odd directional ranks. Remark 4.6 says
  explicitly that the passage from directional parity to global rank is open.
* **Theorem 8.1 (p.20), exact hypotheses.** A ⊂ R² is all-even and there exists *one* direction ℓ with
  n_A(ℓ) ≤ 6. Then A is height-rigid. There is no bound on |A|.

  Consequence (p.20): a non-rigid all-even set has n_A(ℓ) ≥ 8 for *every* ℓ, and |A| ≥ 10. The case
  k = 6 uses a computer-assisted classification (Appendix A, via allowable sequences). The only configurations
  that survive are the heptagon minus a vertex and the hexagon. These are handled by trapezoid relations and
  by F₂[R] real-exponent polynomials.

  Problem 9.2 (the ≤ 8 case) and Conjecture 9.1 (monotone contagion) are left open.
* **Chronology and prior art (bounded).** The source exists only as v1, dated 28 Oct 2026. On 2026-10-30
  I ran these arXiv API queries:
  * `"all-even"`: 469 hits by relevance or date. The only relevant hit is the source itself.
  * `"height-rigid"`: 2 hits, the source and an unrelated entire-function paper.
  * Author listings for Kalmanovich (11 items) and Nivasch (24 items): no follow-up.
  * Seoane AND projection AND odd: 0 hits.

  No public resolution was found. These checks cover arXiv only. MathSciNet, zbMATH and the live proof
  registries were not checked (inherited access denials), so worldwide absence is not certified.

## 2. Rigorous partial statements (restricted cases; non-credit; proofs complete)

### Prop A (two parallel hyperplanes): subsumed by the source

Statement: if a finite S ⊂ R^d meets exactly two parallel hyperplanes, then S has a singly-determined
direction, and therefore an odd line direction.

Proof sketch: put the hyperplanes at x_d = 0 and x_d = 1, and project them to A and B in R^{d−1}. Every
line that is not parallel to the hyperplanes contains at most one pair. Let a* be the lexicographic minimum
of A and b* the lexicographic maximum of B. Then b*−a* arises only from (a*, b*), so
n = |S|−1 (Lemma 7.1). Equivalently, f_A^* f_B ≠ 0 in the domain F₂[R^{d−1}].

**Novelty: none.** This is the argument of source Prop 7.3, whose proof never uses all-evenness beyond
Lemma 7.1. Check C1 verifies it on random rational sets.

### Prop B (two non-parallel planes, one side one-sided)

Setup: S ⊂ H₁ ∪ H₂, where H₁ and H₂ are distinct non-parallel planes and K = H₁∩H₂. Assume S ⊄ H_i for
each i, and assume S∩H₁∖K lies in one open half-plane of H₁∖K. Then S has a singly-determined direction.

Proof:
* Coordinates: H₁ = {z = 0} with points (x, y), y > 0. H₂ = {y = 0} with points (x, z). Replace z by −z if
  needed so that some point of S∩H₂∖K has z > 0.
* A transverse line meets each plane once. A cross pair (a, b) has direction b−a = (x_b−x_a, −y_a, z_b), and
  the direction determines the pair (κ, μ) = (z_b/y_a, (x_b−x_a)/y_a).
* Choose a* ∈ S₁ as follows: first minimise y, then minimise x. Choose b* ∈ S₂ with z > 0 as follows:
  first maximise z, then maximise x.
* Suppose another cross pair (a, b) has the same (κ, μ). Then z_b ≤ z_{b*} and y_a ≥ y_{a*}, so
  equality of κ forces equality of both. Then x_b ≤ x_{b*} and x_a ≥ x_{a*}, so equality of μ forces
  equality of both.
* Points on K and in-plane pairs cannot lie on a transverse line through a cross pair, so b*−a* is
  singly determined. ∎

The algebraic version: G⁰ = {(x,y) ↦ (x+μy, κy), κ > 0} is bi-orderable (κ first, then μ; conjugation
scales μ by κ⁻¹ > 0). Hence F₂[G⁰] has no zero divisors, and the cross condition f₂f₁^* = 0 is impossible.
Check C2 runs 31 random rational instances, including cases with S₂ on both sides and points on K.

**Two-sided obstruction (exact).** In the full group G = G⁰ ⋊ ⟨t⟩ there are zero divisors
(1+τ)² = 0, where τ is an affine reflection fixing K. The solutions f_i = c_i(1+τ) correspond to S
centrally symmetric about a point of K. Those sets fail for another reason: the line through the centre has
odd count. The remaining two-sided case reduces to extreme-row matching identities between the two
half-planes, which I did not close.

### Prop C (products S = Q × H, Q ⊂ R^a finite with |Q| ≥ 2, H ⊂ R with |H| ≥ 2)

Definitions:
* g is the minimum gap of H, and c_g = #{h : h+g ∈ H}.
* D is the Euclidean diameter of Q, attained in direction u.
* By the parallelogram law, the diameter line is the only line parallel to u that carries a chord of length D.

Claim: in direction (D/g · u, 1), the collisions are exactly the pairs (max end, h+g) ~ (min end, h), and
they form a matching. Hence n = |S| − c_g. **So if c_g is odd, S has an odd line direction.**

The companion extreme (λ = d_u/δ_H, where d_u is the minimum gap along u and δ_H the span of H) gives
n = |S| − N_u, with N_u = #{q : q − d_u u ∈ Q}.

So a line-all-even product needs c_g(H) even and N_u(Q) even for all u. I did not close the c_g-even case.
Numerically, every product of a source all-even set with nine different H has between 26 and 339 odd
directions (`runs/products.out`). Check C3 verifies the c_g-odd prediction exactly.

### Lemma D (single-swap Ak-type modification cannot leave a plane)

Hypotheses:
* B ⊂ {z = −1, 0, 1} is centrally symmetric about o ∉ B.
* B₀ = B∩{z = 0} lies on a line through o.
* q ∈ B₀, and p ∈ {z = 2}.

Conclusion: if S = (B∖q) ∪ {p} is line-all-even, then S is coplanar.

Proof:
* By central symmetry, n_B(ℓ) is odd iff the line through o in direction ℓ meets B.
* Removing q and adding p give the parity identity 1[O_B] + 1[D_q] + 1[D_p] ≡ 0 for non-horizontal
  directions (w, 1), where D_x is the set of directions from x to B∖q.
* Put the B₀ line on the x-axis and let Y be the set of y-coordinates of B₁. Every y-level used by D_p must
  lie in Y, so p_y−Y ⊂ Y, p_y/2 ∈ Y and (p_y+Y)/3 ⊂ Y.
* With c = p_y/2 and Y′ = Y−c, the set Y′ is finite, symmetric and satisfies Y′/3 ⊂ Y′. Hence Y′ = {0}.
* Therefore all of S lies in the plane y = c·z. ∎

So the source's planar Ak mechanism (Lemma 6.3) has no 3-D single-swap analogue. Check C4 confirms that the
planar instance A₁ is all-even, and that 40 random non-planar instances have ≥ 9 odd directions.

### Observation E (lattice-convex sets)

If S = conv(S) ∩ Z^k, then every lattice line meets S in a run, so n_S(d) = |S| − |S∩(S+d)| for primitive d.
Line-all-even is then the bilinear condition "r_S(d) even for every primitive d".

A spanning example in any Z^k, k ≥ 3, would project to a counterexample in R³. This transfer is the source's
§2 remark, so it is not new.

Sampled lattice-convex sets show no example even in the plane. In 2-D the best had 2 odd directions; in
3-D and 4-D the best had 6 and 11 (`runs/latconv_*.out`).

## 3. Exact missing lemma

**Missing Lemma (fibre parity rigidity).**
* Let P ⊂ R² be finite, non-collinear, with |P| even and |P| ≥ 8.
* Let T_p ⊂ R (p ∈ P) be nonempty finite fibres, and S = {(p, t) : t ∈ T_p}.
* Assume |S| is even, and that for every secant direction u of P and every σ ∈ R,
  Σ_{M ∥ u} |∪_{p∈M} (T_p − σ·t_M(p))| is even. Here t_M is the coordinate along u.

Then S is coplanar.

Taking P = π_ℓ(S) for any secant direction ℓ of a hypothetical counterexample shows that this lemma is
*equivalent* to Conjecture 2.1. The source proves it for |P| ≤ 6, and P must have no singly-determined
direction (§7).

**Obstruction for every order.** When no line of P carries ≥ 3 points, the hypothesis becomes the bilinear
F₂[R] system Σ_{(i,j)∈J_u} D_{1/d_ij}(F_i^* F_j) = 0. That is the source's eq. (5)–(7), generalised.

Leading-term (Newton-polytope or bi-order) arguments close a case only when the top product is unique:
Props A and B, Prop C with c_g odd, and every equal-length class. In general they fail at every order,
because coplanar fibre data, i.e. affine lifts of planar all-even sets, satisfy every identity of the system.

Example: the P13 string 1110110111000 with singleton fibres solves the system, as the exhaustive control
reproduces. A proof must therefore separate non-affine fibres from affine ones beyond leading terms. When
some line of P carries ≥ 3 columns, the count is not even bilinear: inclusion–exclusion produces trilinear
"midpoint" terms. For example, Q×{0,1,2} needs #{(q, q+v) : q+v/2 ∉ Q} even for every v.

## 4. Status

Conjecture 2.1 is **unresolved** in this lane. Every statement above is restricted or subsumed, and none
is nominated. Numerical and exhaustive searches are support evidence only.
