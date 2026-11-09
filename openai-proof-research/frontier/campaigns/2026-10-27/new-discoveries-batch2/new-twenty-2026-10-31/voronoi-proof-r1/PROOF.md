# 371207: 8-player subspace equilibria on Q_n — proof attempt and exact gap

Lane `voronoi-proof-r1`, Claude Opus 5.5, 2026-11-03. This is a hypothesis proof lane, not an acceptance.

**Verdict: PARKED.** There is no complete proof for an infinite family. What this lane establishes:

- exact reductions and identities, with complete proofs (Part B);
- three proofs that no weight-free shortcut can work, as exact counterexamples (Part B.6);
- a rigorous Gaussian-model corner-slope theorem (Part C.1);
- a derived, unproved, local expansion that predicts the empirical ψ rule and matches exact data for t ≤ 8 to three or four digits (Part C.2);
- the precise missing lemma (Part D).

Numerical evidence is not a proof. Nothing in this file refutes the conjecture.

Notation: n is the dimension, t the base multiplicity, h_o = ∫ φ(g)^3 Φ(g)^5 dg ≈ 0.0083306 (φ and Φ are the standard normal density and distribution function), and |c| = Σ_f c_f.

---

## Part A. Fidelity

The game and the conjecture are read from Stylianou, arXiv:2510.25392v1 (29 Oct 2025, the only version listed on 2026-11-03), Section 1 and Conjecture 1.1. The cached text is `expanded-corpus-r134/sources/371207.txt`, sha256 0e4fbb63…. The Bristol seminar abstract of 7 Oct 2025 is cached in `downloads/priorart-1/39932edc.html`.

- **Profile.** A tuple P = (x^(1), …, x^(k)) of vertices of Q_n = {0,1}^n. Positions need not be distinct: the seminar abstract says "these vertices need not be distinct", and the paper's examples include (0^n, 0^n, 1^n, 1^n).
- **Claims and score.** A_i claims x when d(x, x^(i)) ≤ d(x, x^(j)) for all j. With t_P(x) the number of players claiming x, the score is σ_P(A_i) = 2^{-n} Σ_{x claimed by A_i} 1/t_P(x). Ties are split equally, and co-located players count separately: each one claims x.
- **Equilibrium.** For all i and every x' ∈ Q_n, σ_P(A_i) ≥ σ_{P'}(A_i), where P' replaces x^(i) by x'. The paper says "x^(i)' ∈ Q_n is arbitrary", so moving to an occupied vertex is allowed. This is pure Nash with no strictly profitable unilateral move.
- **Conjecture 1.1 (Day–Johnson).** ∀ k ≥ 5 ∃ N ∀ n ≥ N: no k-player profile on Q_n is an equilibrium.
- **Prop to prove (the refutation).** ∃ k ≥ 5 ∀ N ∃ n ≥ N ∃ P a k-player profile on Q_n with P an equilibrium. Here k = 8.

**The subspace profile.** Fix a basis of F_2^3. For each nonzero functional f ∈ {1, …, 7} (a 3-bit mask, with f(a) = parity of popcount(f & a)), take m_f ≥ 0 coordinates whose functional is f, so n = Σ m_f. Player a ∈ F_2^3 sits at the point p_a whose class-f coordinates all equal f(a).

The 8 points p_a are pairwise distinct exactly when the functionals with m_f > 0 span the dual space. This holds for every m used here with all m_f ≥ 1. The profile is legal in any case, since coincidences are allowed. For the family m = (t+1, t, …, t) every m_f ≥ 1, so the 8 points are distinct.

---

## Part B. Exact results (complete proofs)

### B.1 Equal scores, and reduction to one player

**Lemma 1.** Every player of a subspace profile scores exactly 1/8. The profile is an equilibrium if and only if no target v ∈ Q_n gives player 0 a score above 1/8.

*Proof.* Translation τ_b(x) = x ⊕ p_b is an isometry of Q_n. It maps p_a to p_{a+b}, so it permutes the players. It preserves all distances, hence claims and shares, so all 8 scores are equal. They sum to 1 because every voter's unit vote is distributed in full. Hence each score is 1/8.

For the second claim, a deviation of player b to v is carried by τ_b to a deviation of player 0 to v ⊕ p_b against the same opponent set, with the same score. ∎

### B.2 Shape reduction and an exact finite-sum formula

Let the deviator (player 0) move to v. Let c_f be the number of class-f coordinates where v_j = 1, so 0 ≤ c_f ≤ m_f. The shape is c = (c_f).

For a voter x define two signed agreements with 0:

- u_f on the m_f − c_f class-f coordinates outside supp v: (number of coordinates with x_j = 0) − (number with x_j = 1);
- w_f, the same quantity on the c_f class-f coordinates inside supp v.

**Lemma 2.**

- d(x, p_a) − d(x, v) = K_a(x), where K_a = Σ_{f(a)=1} u_f − Σ_{f(a)=0} w_f.
- Consequently σ(v) depends only on c, and

  σ(c) = 2^{-n} Σ_{u,w} Π_f C(m_f − c_f, (m_f − c_f + u_f)/2) · C(c_f, (c_f + w_f)/2) · 1{K ≥ 0} / (1 + #{a ≠ 0 : K_a = 0}).

  The sum runs over u_f ≡ m_f − c_f and w_f ≡ c_f (mod 2), with |u_f| ≤ m_f − c_f and |w_f| ≤ c_f.

*Proof.* Coordinate j contributes [x_j ≠ p_{a,j}] − [x_j ≠ v_j] to d(x, p_a) − d(x, v). This is 0 when p_{a,j} = v_j.

- Outside supp v (v_j = 0) the contribution is nonzero only if f(a) = 1, and it equals +1 if x_j = 0 and −1 if x_j = 1. Summed over the class it gives u_f.
- Inside supp v (v_j = 1) it is nonzero only if f(a) = 0, and it equals −1 if x_j = 0 and +1 if x_j = 1. Summed over the class it gives −w_f.

The voter claims-for-deviator condition and tie count are exactly K ≥ 0 and #{K_a = 0}. The counting weights are the binomials shown. ∎

This is implemented independently in `scripts/smallmoves.py`. It agrees exactly with two other methods: a direct sum over voters (`vk.score_brute`) and the sphere-convolution Walsh–Hadamard method (`vk.scores_all`).

### B.3 Uniform-shift identity and the 4-dimensional lift

**Lemma 3.**

- D_a := d(x, p_a) − d(x, v) = D^0_a + S(x) for all a ≠ 0, where D^0_a = d(x, p_a) − d(x, 0) and S = d(x, 0) − d(x, v).
- The whole configuration is a subspace profile of the 4-dimensional space S̃ = S ⊕ ⟨v⟩. Its 14 coordinate functionals are (f, b) with f ≠ 0, with multiplicities μ(f, 0) = m_f − c_f and μ(f, 1) = c_f. The deviator sits at the point u = (0, 1).

*Proof.* The first item is immediate. For the second, class f splits into the coordinates where v is 0 and where v is 1. On these, the players take value f(a) and the deviator takes value b. ∎

### B.4 The one-step identity, and its exact simplification

Let X be the player-0 statistic of a subspace profile m′: X_a = Σ_{f(a)=1} e_f, where e_f is the signed agreement with 0 in class f. Define

- T_{m′}(y) = E[Sh(X + y)] for y ∈ Z^7, where Sh(z) = 1{z ≥ 0} / (1 + #{a : z_a = 0});
- Δ_{m′}(B) = T(1_B) + T(−1_B) − 2T(0).

Write g⊥ = {a ≠ 0 : g(a) = 0} (3 points) and g1 = {a : g(a) = 1} (4 points).

**Lemma 4 (one coordinate).** Let player 0 move one coordinate j of class g, and let m′ = m − e_g. Then:

1. σ(e_j) − 1/8 = ½ [Δ_{m′}(g⊥) − Δ_{m′}(g1)];
2. Δ_{m′}(g1) = 0 exactly, so σ(e_j) − 1/8 = ½ Δ_{m′}(g⊥).

*Proof.* Let η = ±1 be the voter's agreement with the new v at coordinate j. It is uniform and independent of the other coordinates.

1. By Lemma 2, D_a = X_a + η·[g(a) = 0], where X is the statistic of m′. Before the move, D^0_a = X_a − η·[g(a) = 1]. Take expectations over η = ±1. Use T_{m′}(0) = 1/8 (Lemma 1 applied to m′) and E D-score = 1/8 before the move.
2. The second equation in the proof of item 1 says (T(1_{g1}) + T(−1_{g1}))/2 = σ_m(0) = 1/8 = T_{m′}(0). ∎

Both items were verified in exact rational arithmetic against the convolution checker, for m = (2,1⁶), (1⁷), (3,2⁶) and (2⁷) and every g (`logs/step_K3.log`, `logs/sd_*.log`).

### B.5 Parity lemma

D^0_a ≡ d(0, p_a) = Σ_{f(a)=1} m_f ≡ ψ(a) (mod 2), where ψ = Σ_{f : m_f odd} f ∈ (F_2^3)^*. If ψ = 0, every inter-player distance is even. For m = (t+1, t, …, t), ψ = f_1 ≠ 0 for every t: for odd t, use Σ_{all f} f = 0.

### B.5′ Relation to the 4-player theorem

Stylianou's balanced 4-player profiles are exactly the 2-dimensional subspace profiles (translated so that x^(1) = 0) with no constant coordinate.

- Balanced implies subspace: with x^(1) = 0, each coordinate has exactly one 0 among x^(2), x^(3), x^(4), so x^(4) = x^(2) ⊕ x^(3). His own parametrization 0^m 1^{n−m}, 1^m u, 1^m(1−u) shows this.
- Subspace implies balanced: the values in a coordinate are (0, α, β, α+β) with (α, β) ≠ 0.

So Stylianou's Theorem 1.2 states that **every** 2-dimensional subspace profile is an equilibrium, for every multiplicity vector. The 3-dimensional analogue is false in general: the uniform profiles fail (B.7). The k = 8 question is therefore which multiplicity vectors work.

### B.6 No weight-free proof exists (exact counterexamples)

Each item below is an exact rational computation. The scripts are listed with each item.

1. **Stylianou-type sign-class averaging fails** (`scripts/signavg.py`, `logs/sa_1000000.log`). Fix all 14 magnitudes |e_{f,b}|. Averaging the deviator's share over the sign choices exceeds 1/8 for some patterns in the parity class of (t+1, t, …, t). The worst found is 55/384 > 1/8 at (|e_{f0}|, |e_{f1}|) = (1,2), (1,1), (0,0), (0,0), (3,3), (0,0), (2,2). The c = 0 sanity check gives exactly 1/8 for every pattern. Hence any proof must compare different magnitude patterns, which means it must use the binomial weights.
2. **The one-step integrand is not sign-definite** (`logs/step_K3.log`). The integrand of Lemma 4(1) is not ≤ 0:
   - not pointwise;
   - not after averaging over the 8 translations;
   - not after averaging over all 128 sign flips.

   This holds in every relevant parity class, including those of the family. For example, with all-even m′ (the family with g = f_1), 80 sign classes have a positive average, the worst being 1/4.
3. **No induction m → m + (1,…,1)** (`logs/plus1_3_7.log`). The orbit with functionals {1, 2, 4, 7} each once (n = 4) is an equilibrium, but its +1 is not (n = 11). The same holds for (2,1,1,1,1,0,0) at n = 6.
4. **No local maxima besides 0, but no monotone structure either** (`logs/land_*.log`). For t = 2 and 3 the score has no local maximum over shapes other than c = 0, and the maximum over each level |c| = k is strictly decreasing in k. However, 637 of the unit steps (t = 2) and 5109 (t = 3) increase the score, so no coordinatewise monotonicity holds.

### B.7 Independently verified finite facts

Every item uses my own checker, written from the definitions; vor.py was not reused. Logs and receipts are in `logs/`.

| Profile m | n | Result | Method |
|---|---|---|---|
| (2,1,1,1,1,1,1) | 8 | EQ, max deviation = 1/8 (attained only at v = 0) | full brute force: all 8 players × all 256 targets × all voters, equal to convolution (`t1_small`) |
| (3,2,2,2,2,2,2) | 15 | EQ, max deviation 19919/163840 = 0.9726/8 at c = e_{f1} | all 8 players score 1/8 directly; all 2,916 shapes by brute force equal to convolution; all 32,768 targets by convolution (`verify`, `fam_3222222`) |
| (4,3,3,3,3,3,3) | 22 | EQ, max deviation 1285389/10485760 = 0.98067/8 at c = e_{f1} | convolution over all 2^22 targets; brute force at 33 shapes; small-move enumerator agrees (`verify`, `fam_4333333`, `sm_check3`) |
| (1⁷), (2⁷), (3⁷) | 7, 14, 21 | NOT EQ: 17/128, 1057/8192, 267791/2097152 at a one-coordinate move | convolution and brute force at the argmax |
| (5,5,5,1,0,0,0) | 16 | NOT EQ: 32935/262144 at c = (1,1,1,0,0,0,0) | same |
| (t+1, t, …, t), t = 4…8 | 29…57 | every move with \|c\| ≤ 2 (t = 4, 5, 7) or \|c\| ≤ 1 (t = 6, 8) is unprofitable | exact enumerator (`sm_fam*_t*`; the t = 10 run overflowed int64 and is **invalid**) |

---

## Part C. Analytic route

### C.1 Gaussian corner slope (rigorous within the Gaussian model)

Take uniform multiplicities t and replace each signed agreement by a centred normal with the same variance. The deviator's Gaussian score at shape c is Γ(c) = P(Y ≥ 0), where Y ~ N(0, Σ(c)) and

Σ(c)_{ab} = Σ_{f(a)=f(b)=1} (t − c_f) + Σ_{f(a)=f(b)=0} c_f.

This is affine in c and positive definite.

**Proposition C1.** ∂Γ/∂c_g at c = 0 equals −(3/4) h_o / t for every g. Equivalently, 8Γ(c) = 1 − 6 h_o |c| / t + O(|c|²/t²), with 6h_o ≈ 0.04998.

*Proof.*

1. For moves in class g, Y = X′ − W·1_{g⊥}. Here X′ ~ N(0, Σ_0 − c·1_{g1}1_{g1}^T) and W ~ N(0, c) is independent.
2. By the heat-equation (Plackett) identity, dP(N(0, Σ+εE) ≥ 0)/dε = ½ Σ_{ab} E_{ab} H_{ab}, where H = Hess_s P(X ≥ s) at s = 0. Hence ∂Γ/∂c = ½ (1_{g⊥}^T H 1_{g⊥} − 1_{g1}^T H 1_{g1}).
3. At c = 0, X_a has the law of σ(G_0 − G_a) with G_0, …, G_7 i.i.d. N(0,1) and σ² = 2t: the variance is 4t and the covariances are 2t. So P(X ≥ s) = ∫ φ(g) Π_a Φ(g − s_a/σ) dg.
4. Hence σ² H_{ab} = ∫ φ³ Φ^5 = h_o for a ≠ b, and σ² H_{aa} = −∫ g φ² Φ^6 = h_d. Integration by parts with (φ²)′ = −2gφ² gives h_d = −3h_o; numerically the ratio is −2.9999999999999.
5. Therefore ½[(3h_d + 6h_o) − (4h_d + 12h_o)] / σ² = ½(−h_d − 6h_o) / (2t) = −(3/4) h_o / t. ∎

The Gaussian score function thus has a strict corner maximum at c = 0 in every coordinate direction. This holds for all near-uniform profiles, since only the limit proportions enter. A Monte Carlo check (`scripts/gauss_global.py`, 4·10^5 common random samples, standard error 0.0005; this is not validated numerics) gives the following maxima of 8Γ outside small balls:

| region | max 8Γ |
|---|---|
| \|γ\|₁ ≥ 0.25 | 0.991 |
| \|γ\|₁ ≥ 0.5 | 0.979 |
| \|γ\|₁ ≥ 1 | 0.951 |
| \|γ\|₁ ≥ 2 | 0.883 |

Here γ = c/t, with 3,986 random and structured points of [0,1]^7. At the corners where the deviator coincides with a player, the identically tied opponent is split correctly, giving 8Γ = 0.571.

### C.2 Local expansion for fixed moves (derived, not proved)

For a fixed shape c, σ(c) = E_w[T_{m−c}(R(w))], where R_a = Σ_{f(a)=0} w_f is bounded. This follows from Lemmas 2 and 3. Expand T(y) − T(0) to order 1/t using four facts:

1. the summands are symmetric, so the Edgeworth correction to the local density is of relative order 1/t;
2. each coordinate X_a lives on a spacing-2 lattice with parity π_a = ψ(m − c)(a), and every pair (X_a, X_b) fills its whole parity class (2Z)² + π (proved: the class-f increments separate the pair);
3. ρ′_a(0) = 3u and ρ_{ab}(0, 0) = u, where u = h_o/(2t), from C.1;
4. events where three coordinates sit on the boundary at once are O(t^{-3/2}).

The first-order terms are linear in y and cancel under the symmetric law of w. What remains is

lim_{t→∞} t·(8σ(c) − 1) = 4h_o · E_w[ 3 Σ_a s1(π_a, R_a) + Σ_{a<b} s2(π_a, π_b; R_a, R_b) ],

where:

- s1(π, y) = Σ_{z ∈ π+2Z} 2z [h1(z+y) − h1(z)] is the 1-D lattice sum with unit density slope, with h1 = 1, ½, 0 on z > 0, z = 0, z < 0;
- s2 is the finite 2-D interaction sum with unit density, the corner function h2 (share 1/3 at a double tie), and the single-coordinate parts subtracted.

These are implemented in `scripts/localQ.py` and `scripts/lattice_coeff2.py`. The mixed-parity interaction tables are P2 = {(0,0): 4/3, (0,1): 2, (1,1): 8/3} along (1,1) and Q2 = {(0,0): −2/3, (1,0): 2/3, (0,1) = (1,1): 0} along (1,0).

**Consistency check.** The exact identity Δ(g1) = 0 of Lemma 4(2) is reproduced for all 8 parity functionals.

**Derived result.** For every shape with |c| ≤ 4 (all shapes, by exact rational evaluation of the formula), the value depends only on |c| and on whether ψ(m) is zero:

| ψ(m) | lim t(8σ(c) − 1) / h_o |
|---|---|
| ≠ 0 (the family (t+1, t, …, t)) | −(6\|c\| + 2·[\|c\| odd]): −8, −12, −20, −24 for \|c\| = 1…4 |
| = 0 (uniform t) | −6\|c\| + 14·[\|c\| odd]: **+8** (profitable), −12, −4, −24 |

So the term −6h_o|c| is exactly the Gaussian slope of C.1, and the lattice and tie correction is 0 for even |c| and depends only on ψ for odd |c|. This **derives the empirical ψ rule**: a one-coordinate move is profitable, asymptotically, iff ψ(m) = 0.

**Comparison with exact data** (t·(1 − 8σ); prediction 8h_o = 0.06664 at |c| = 1 and 12h_o = 0.09997 at |c| = 2):

| case | t=3 | t=4 | t=5 | t=6 | t=7 | t=8 | predicted |
|---|---|---|---|---|---|---|---|
| family, move in class f_1 | 0.0607 | 0.0621 | 0.0629 | 0.0635 | 0.0639 | 0.0642 | 0.0666 |
| family, move in another class | 0.0663 | 0.0663 | 0.0664 | 0.06646 | 0.06649 | 0.06652 | 0.0666 |
| family, \|c\| = 2 (c = 2e_{f1}) | 0.0928 | — | 0.0951 | — | 0.0964 | — | 0.1000 |
| uniform, \|c\| = 1 | −0.0646 | −0.0652 | −0.0655 | — | — | −0.0659 | −0.0666 |

Here "t" is n/7 for the family. The convergence is consistent with an O(t^{-1/2}) relative correction. This is evidence, not proof.

### C.3 Lean cost of the analytic route

Mathlib has no multivariate local limit theorem with Edgeworth correction and no multivariate Berry–Esseen theorem with explicit constants. Formalizing Part D would be a multi-person-year project. No Lean draft of the analytic route is offered.

---

## Part D. The exact gap

What a refutation of 371207 by the family m_t = (t+1, t, …, t) (n = 7t + 1) still needs:

**Missing Lemma M (uniform deviation bound).** There are t_0 and κ > 0 such that for all t ≥ t_0 and every shape c ≠ 0 with 0 ≤ c ≤ m_t,

σ_{m_t}(c) ≤ 1/8 − κ·min(|c|, t)/t.

Together with an exact finite check for t < t_0, this gives an equilibrium at every n = 7t + 1 and hence refutes Conjecture 1.1 for k = 8. The finite check is done here only for t ≤ 3; t ≥ 4 has been checked for small moves only.

A proof of M splits into three regimes:

- **M1 (local, |c| ≤ K).** Make C.2 rigorous with an explicit O_K(t^{-3/2}) error: a 7-dimensional lattice local limit theorem with second-order (Edgeworth) control at orthant faces and ties. For fixed K this is classical in form (Bhattacharya–Rao type), but the explicit constants are long.
- **M2 (mesoscopic, K ≤ |c| ≤ εt).** A bound of the form 8σ ≤ 1 − (6h_o − δ)|c|/t, uniform in c. This needs either a uniform version of M1 in which the lattice corrections stay O(1/t) while the Gaussian term grows linearly, or a path argument that bounds each step by Lemma 4-type second differences with uniform constants. Neither is available. This is the hardest part.
- **M3 (macroscopic, |c| ≥ εt).** Validated numerics proving sup_{|γ|₁ ≥ ε} 8Γ(γ) ≤ 1 − η, plus an explicit multivariate Berry–Esseen bound over convex sets. Raič (2019, Bernoulli; constant as recalled, not re-checked against the paper in this lane) gives sup_C |P(W ∈ C) − P(Z ∈ C)| ≤ (42 d^{1/4} + 16) Σ E|Σ^{-1/2} X_i|³ for independent summands, which here is about 84 · O(n^{-1/2}). This forces t_0 to be very large, so the finite check up to t_0 would not be feasible by the present exact methods.

None of M1–M3 is proved here. C.1 supplies the leading constants for M2 and M3, and C.2 supplies the expected constants for M1. The identities B.2–B.4 are the exact interface any proof would use.
