# Analytic discovery r132: PREFREEZE, no nominee

Author: Myeongjin Kang (no affiliation). Original exposition CC BY 4.0; original code MIT.
Runner provenance: Factory Droid / claude-opus-5-5 / high. Upstream pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb;
theorems at the pin are stipulated true. This report assigns no gate, verdict or count.

## Outcome

No exact scope was frozen and nothing is nominated. The round resumed family 088 (Brannen's reverse projection
inequality, open for 4 <= n <= 8) with a new route, not a rerun of r131. The route turns FHLX's lower bound into an
exact formula, extends it to every facet count, and reduces the whole (n+2)-facet class to one inequality (★)
involving a single expectation. (★) is not proved for any n in 4..8, so no full theorem follows. No counterexample
for n <= 8 was found either. First-order analysis off every pair-merge and triangle-merge simplex configuration is
negative for n <= 8 (numerical). Everything below is author derivation or float exploration, not an accepted result.

Notation: P_n(K) = |ΠK| / |K|^(n-1), c_n = (n+1) n^n / n!, E = (E_1, ..., E_m) iid Exp(1), Δ = Δ^(m-1) the standard
simplex in R^m, C_m = [-1/2, 1/2]^m, and D(a) = Σ_{i<j} |a_i - a_j|.

## 1. Exact reduction for polytopes with m facets (author derivation; an equivalent formulation, not a result)

**R1 (exactness of FHLX Prop. 4.1).** Let F ⊂ 1^⊥ ⊂ R^m have dimension n, let q_i = P_F e_i, and let Q_F be the
Minkowski polytope with area vectors -q_i. Then

    P_n(Q_F) = n^n V_F(P_F C_m) · sup_{λ ∈ relint Δ} V_F((λ+F) ∩ Δ).

FHLX (4.1) gives the inequality ≥ for each λ. For equality, translate Q_F so that 0 ∈ int Q_F, put h_i = h_Q(-q_i)
and H = Σ h_i = n V(Q_F), and take λ_i = h_i / H. Indices with q_i = 0 are handled by letting λ_i → 0. Then
(λ+F) ∩ Δ - λ = Q_F / H, because Q_F is the intersection of its facet half-spaces {z_i ≥ -h_i}, and positively
parallel q_i have proportional h_i. So V_F(S) = V(Q)^(1-n) n^(-n), which is Minkowski's equality case.

**R2 (universality).** Every n-polytope K with at most m facets is affinely equivalent to some Q_F. Write the outer
area vectors as the columns of V (n×m) and pad with zero columns if needed. Then V1 = 0, F = rowspace(V) ⊂ 1^⊥, and
V = A U^T with U an orthonormal basis of F and A ∈ GL(n). Choose φ = s(-A)^(-T) with s^(n-1) = |det (-A)^(-T)|^(-1).
Then |det φ| φ^(-T) = -A, so φQ_F and K have the same area measure and are translates (Minkowski uniqueness).
P_n is affine invariant.

**R3 (formula).** Write F^⊥ = span{1, a^1, ..., a^r} with r = m-1-n, and set A = [a^1 ... a^r]. Then:

- V_F(P_F C_m) = Σ_{|J|=r+1} |det[1 A]_J| / sqrt(det G), by McMullen's formula and complementary minors.
- V_F((λ+F) ∩ Δ) = sqrt(det G) f_X(t) / (m-1)!, by the coarea formula, with X = A^T s, s uniform on Δ, t = A^T λ.
- f_X(t) = ((m-1)!/n!) f_{Y_t}(0), where Y_t = (A - 1t^T)^T E. This holds because s = E/S with S ~ Gamma(m)
  independent of s, so Y_t = S(X - t) and E[S^(-r)] = n!/(m-1)!.

Hence

    P_n(Q_F) / c_n = sup_t Ψ(A - 1t^T),     Ψ(A) := (1/(n+1)) Σ_{|J|=r+1} |det[1 A]_J| · f_{A^T E}(0).

Brannen's bound for all polytopes is therefore equivalent to Ψ ≤ 1 for every m and every A. Checks: r = 0 gives
Ψ = 1. For the 3-cube (m = 6, r = 2), Ψ at the centroid evaluates to 0.44444 = 8/18 (scratch/psi2.py, float).

**R4 (n+2 facets).** For r = 1, Ψ = D(a) f_{⟨a,E⟩}(0)/(n+1). Taking the supremum over t gives

    sup over n-polytopes with <= n+2 facets of P_n/c_n = sup_a D(a) ||M(·|a)||_∞ / (n+1)^2,

where M(·|a) is the density of ⟨a,s⟩, that is, the Curry–Schoenberg B-spline with knots a_1, ..., a_{n+2}. This is
FHLX (4.9) with max_t in place of t = ⟨a, 1/m⟩. Equality curve: a = (-1, c^n, 1) at t = c gives Ψ = 1 for every
c ∈ (-1,1); these are simplices.

## 2. Global form (★) of the (n+2)-facet problem

Fix (a,t) and translate so that t = 0. Rescale so that the extreme knots are -(1+c) and 1-c, and call the n middle
knots b ∈ R^n. Set W = Σ_j b_j E_j. The two outer exponentials give an asymmetric Laplace density g_c, and
f_Y(0) = E g_c(-W). Middle knots lie between the outer ones, so D(a) = 2(n+1) + D(b). Hence the sharp bound for all
n-polytopes with at most n+2 facets is equivalent to:

    (★)  for all c ∈ (-1,1) and b ∈ R^n:   (1 + D(b)/(2(n+1))) · E exp(-W^+/(1+c) - W^-/(1-c)) <= 1.

(The box constraint on b may be dropped, because outside it the true D(a) is larger.) A Monte Carlo cross-check
against an independent B-spline evaluation agreed to about 3 digits on 4 random configurations. With c = 0 and b
equally spaced, (★) is exactly FHLX's Γ_0(ε) = (D(a_ε)/D(a_0)) I(ε), because E e^(-ε|W|) = E(1+ε|L|)^(-n).

**First variation (linearisation of ★ at b → 0).** Optimising over c gives

    G*(b) = D(b)/(2(n+1)) - (sqrt P + sqrt N)^2 / 2,    P = E W^+,  N = E W^-.

FHLX (c = 0, b = (-4..4), n = 9) gives G = 0.0992 > 0. Float optimisation of ρ_n = sup_b D(b)/((n+1)(sqrt P + sqrt N)^2)
gives, for n = 2..10: .333 .500 .619 .718 .804 .882 .953 1.0195 1.0817. So, even with optimised directions and
cluster positions, the first-order threshold in the (n+2)-facet class is exactly n = 9, and n = 8 has about a 5% margin.

**More facets.** In R3 coordinates, a simplex configuration arising from r disjoint merged pairs gives a separable
first variation with the same per-column functional, over n+1-r < n perturbable rows. Pair merges with r >= 2 are
therefore worse than r = 1. A single merged triangle group (r = 2, gauge φ_T) gives

    G(B) = Σ_{j<j'} ψ_T(b_j - b_j') / ((n+1) Δ_0) - E φ_T(-Σ b_j E_j),

where ψ_T(v) = Σ_l |det(v, a_l)|. A Monte Carlo screen (common random numbers) found no improvement over pair
merges: n = 4: .62; n = 8: .956 at best; n = 9: .990. A random-start non-perturbative search with m = 11, n = 8 reached
.961, but the same search with m = 12, n = 9 did not find FHLX's violator (.979). That search is uninformative and was
not escalated.

## 3. Strongest integrated reduction and what is unpaid

FHLX §4 (Props. 4.1–4.2, Lemmas 4.3–4.4, Prop. 4.5, lifting (4.19)) supplies the lower bound, the codimension-two
section/projection product, the t = 0 Cavalieri profile and the n >= 9 first variation. R1–R4 and (★) combine that
mechanism with routine classical steps: the Minkowski equality case, the Gale/row-space description of area vectors,
the Curry–Schoenberg identification, and the exponential (Lukacs) representation. Taken alone they are equivalent
formulations and routine, not a finding. The new mathematical content would be any of the following, and none is
supplied:

1. **Gap 1 (main).** Prove (★) for n = 4, ..., 8, for all c and b. This would give the sharp statement "Brannen's
   bound holds for every n-polytope with at most n+2 facets if and only if n <= 8", with the "only if" part being
   FHLX. Difficulty: (★) is a sharp inequality in n+1 real parameters. Its equality set is the boundary point b = 0,
   and at n = 8 the first-order margin is about 5%. The flip between n = 8 and n = 9 mirrors FHLX Lemma 4.4
   (E|h| < E h^2 on an 8-cube). No analytic proof was found. A computer-assisted branch-and-bound proof was judged
   disproportionate here.
2. **Gap 2.** Prove even the linearised inequality D(b) <= (n+1)(sqrt P + sqrt N)^2 for n <= 8. It is necessary for
   Gap 1 but not sufficient. Its dual is an infinite-dimensional moment certificate, and none was constructed.
3. **Gap 3.** Find any counterexample for n <= 8. None was found. The first variation is negative off pair-merge and
   triangle-merge simplex points (numerical only), merges of r >= 3 were not screened, and the global search was
   weak. Products of simplices lie in the (n+2)-facet class and, per I43, none beats c_n for n <= 8.

## 4. Relation to project history

I43 §1.3 parked RP4 after testing only simplex-product partitions. r112 cites I43. r131 was an unfrozen numerical
search over vertex sets in n = 4. Its retained n = 4 output peaks at 1.0000000000000044, which is float noise around
the simplex. That run was not reused, rerun or copied. The present route (exactness, the B-spline form, (★), the
first-variation threshold, the general-m Ψ) has no project antecedent that I found (see reading-limits.md). None of
these is a frozen target, so no old scope is changed.
