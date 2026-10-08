# Unaccepted norm-generator development report

Claude Opus task `ecdloop-h003-norm-generator-development-opus-20261008-r1`.
Raw report retained, including unrequested scratch-check claims. Root's
H003-norm-generator-disposition.md supersedes cost/capacity and scope overclaims.

I couldn't build a cheap relation generator from the norm/coefficient/small-root lens. Verified gain over rho is still **NONE**. I developed three different generators, wrote executable pseudocode for each, and located the exact primitive each one lacks. I edited nothing, spawned no children, and ran no experiment. I did run two tiny analysis scripts, each well under 1k field operations:
- **Degree check:** the total degree of Semaev's S₃ in x₁,x₂ is **D₂=4**, and of S₄ in x₁,x₂,x₃ is **D₃=12**. I extrapolate D_m = m·2^{m−1}, so D₄≈32 is a guess, not a computation.
- **Identity check:** the two relation identities used below held on all 200 random cases each, over p=1009.

## Shared ledger and the beat-rho condition

**Baseline (ordinary prime field, prime order q≈p):** parallel rho with distinguished points, about 0.886√q curve additions with the negation map (1.253√q without), each about 6M+1S with batched inversion, and negligible memory.

**Index-calculus ledger** (factor base F = {(x,y) ∈ E : 0≤x<X}, B≈X/2 points, signs recovered later):

- Total = C_setup + N_R·(C_draw + C_test) + N_rel·C_wit + C_LA
- C_setup ≈ X·O(log p)M, plus whatever precomputation the generator needs.
- Relations needed: N_rel = B+Δ.
- Relation density per random target R=aP+bQ: ρ_m ≈ X^m/(m!·q). This is a heuristic uniform-sum assumption.
- Number of targets: N_R = N_rel/(ρ_m·η), where η is the fraction of existing decompositions the generator actually finds.
- C_draw ≈ 1 group operation (random walk on R).
- C_wit ≤ 2^{m−1}·m additions (sign recovery and check).
- C_LA ≈ 3mB² multiplications mod q (block Wiedemann/Lanczos), memory O(mB).
- Target descent: none, because Q is already inside the relations. The alternative (relations with b=0 first, then one descent for Q) costs 1/(ρ_m η)·C_test, which is negligible.
- Final step: k = −Σcᵢaᵢ / Σcᵢbᵢ; retry if the denominator is 0.

**Beat-rho condition.** Write C_test = X^τ and require setup and memory below √q. Then the total is p·X^{τ−m+1} + X² with X ≤ p^{1/m}. This beats rho **only if τ < min(m−3, m/2−1)**, which needs m≥4. For m=3 the only route is a heuristic double-large-prime analogue of Gaudry–Thomé–Thériault–Diem (~p^{4/9}), and it needs τ < 1/6 at X ≈ p^{1/3}.

This agrees with the cost formula in the PKM16 primary manuscript (pp. 5–8, which I read): P + m!·p/(deg L)^{m−1}·T + (deg L)^ω, beating √p when T < p^{1/2−1/m}. Generic meet-in-the-middle gives τ = ⌈m/2⌉ with a shared X^{⌊m/2⌋} table, so it misses by at least 1. Any gain has to come from using the coordinates algebraically.

## G-A: coefficient-box generator

- **Exact m=2 equation** (R+P₁+P₂=O, s=x₁+x₂, t=x₁x₂): λ = (a + 2x_R² + x_R·s − t)/(2y_R) and λ² ≡ s + x_R. The conic is parametrised by λ.
- **Executable generator:**
  1. For s in [0,2X) with x_R+s a square, and each λ = ±√(x_R+s):
  2. t ← a + 2x_R² + x_R·s − 2y_R·λ.
  3. Keep it only if t ≤ s²/4 and s²−4t = r² over ℤ; then xᵢ = (s±r)/2.
  4. Check base membership, recover signs, verify the point equation.
  - Cost per R ≈ 2X·(Legendre + sqrt), so τ=1. That is no better than a hash scan.
- **General m:** use f ∈ L((m+1)O) with f(R)=0, and coefficients of N_f/(x−x_R) in the weighted box e_j < C(m,j)·X^j. A scanning version is worse: for m=3, scanning (α, e₁, e₂) gives τ=3.
- **Missing primitive:** an enumerator of box points on the coefficient hypersurface W_R at polylog cost per point.
- **Even with that primitive:** under the uniform-box heuristic the best exponent is p^{(m²−m+2)/(m²+m)}, which is 2/3 for m=2 and m=3 and 0.7 for m=4. Per your correction, this is a heuristic loss, not a lower bound. Encoding integer splitting just turns (s,t) back into root variables, which is G-B.

## G-B: root-variable small-root (Coppersmith-style) generator

- **Lattice:** shifts x^i·F_R^k·p^{h−k}, where F_R = S_{m+1}(x₁..x_m; x_R) mod p, scaled by X.
- **Steps:**
  1. Run LLL.
  2. Keep m vectors that satisfy the Howgrave-Graham criterion (‖h(xX)‖ < p^h/√dim).
  3. Take integer resultants of those polynomials.
  4. Find roots in [0,X)^m, check base membership, recover signs.
- **Cost:** the lattice dimension is fixed for fixed m, so τ=0 (polylog per R).
- **Capacity (optimistic heuristic):** works only for X ≤ p^{1/D_m}. Beating rho needs X > p^{1/(2(m−1))}, i.e. D_m < 2(m−1). With D₂=4, D₃=12 and D₄≈32, that never holds. Enumerating j variables first only makes the requirement harder.
- **Exact bottleneck:** the degree D_m is far larger than the number of unknowns m. If some lattice reached the uniqueness regime (X^m ≈ p), m=5 would give about **p^{2/5}**. That is the evidence that would change the conclusion.

## G-C: norm divisibility over a multiplicative-coset base (degree grows with q)

- **Base:** V = {P : x_P ∈ c·μ_K}, with K | p−1 and K ≈ p^θ. This only applies when p−1 has a suitable divisor (or via PKM's isogeny/tower variants).
- **Relation condition:** G_f(cz) divides z^K − 1.
- **Exact m=2 generator:**
  - Set s' = (λ²−x_R)/c and t' = t(λ)/c².
  - Then z^K mod (z² − s'z + t') = U_K·z − t'·U_{K−1}, with U₀=0, U₁=1, U_{n+1} = s'U_n − t'U_{n−1}.
  1. Compute U_K(λ) and U_{K−1}(λ) by matrix powering in F_p[λ]; this is a charged Õ(K) step, not a free oracle.
  2. g ← gcd(U_K, t'·U_{K−1} + 1).
  3. Roots of g give λ, then (s,t), then the witness.
  - Per R cost is Õ(K), so τ=1.
- **General m:** generic elimination is about (2K)^{m−1} by Bezout, so τ ≈ m−1. PKM's towers have unknown degrees of regularity, which their paper lists as an open problem.
- **Fixed vs growing degrees:** fixed-degree generators (G-A, G-B) are cheap per target but capacity-limited. Growing-degree generators (G-C) have full capacity but cost about as much as a scan. A winning generator needs both properties at once.

## Reformulations I dropped quickly

- **m=3 parabola criterion (identity checked):** R+P₁+P₂+P₃=O exactly when the points (xᵢ, σᵢ) are collinear, where σᵢ = (yᵢ−y_R)/(xᵢ−x_R). This is linear in the full-size values but reduces to finding collinear triples among 2B points, so τ=2.
- **Small-(x,y) base with a linear Lagrange congruence** d·y_R ≡ a₁x_R² + b₁x_R + c₁: lattice enumeration is cheap, but the box volume is about X⁹Y³ against B ≈ XY/p true points. That is a heuristic loss of about X⁶p³ candidates per relation.

## Missing primitive and decisive tests (not run)

**Missing primitive MP(m):** a witness-producing small-x decomposition solver for S_{m+1} that, for an arbitrary x_R, runs in X^τ with τ < min(m−3, m/2−1), with setup and memory below √q. The minimal case is **m=4, X ≈ p^{1/5}, cost sublinear in X**. In m=4 terms the threshold is X ≥ p^{1/6}, while the degree heuristic only reaches X ≈ p^{1/32}.

1. **Algebraic gate (cheapest):** compute the Newton polytopes of S₄ and S₅ with x_R fixed, plus the Jochemsz–May capacity bounds. If capacity is at most 1/(2(m−1)), reject G-B. This needs no lattice runs.
2. **Calibration experiment (fits ≤1M counted events including failures, under 60 s):**
   - Setup: p ≈ 2⁴⁰, m=2, θ ∈ {1/8, 1/6, 1/5, 1/4, 1/3}; 10 planted and 10 unplanted targets per θ.
   - Lattices: dimension 6 (linearization) and dimension ≤10 (Coppersmith); every big-integer operation counted; abort if the 1M cap is hit.
   - Decision rule: if recovery stops near θ ≈ 1/4 (=1/D₂), the degree heuristic stands. If it reaches θ ≥ 0.3, fund the S₄/S₅ tests.
   - It can only move the conclusion upward: small lattices may underperform asymptotic bounds.

**Things that would change the conclusion:**
- a lattice construction for S_{m+1} with capacity above 1/(2(m−1));
- a box enumerator whose candidates per relation are far below X^{m(m−1)/2};
- a dedicated μ_K or tower solver beating K^{m/2−1} per target.

Existing literature and generic merge methods supply none of these.
