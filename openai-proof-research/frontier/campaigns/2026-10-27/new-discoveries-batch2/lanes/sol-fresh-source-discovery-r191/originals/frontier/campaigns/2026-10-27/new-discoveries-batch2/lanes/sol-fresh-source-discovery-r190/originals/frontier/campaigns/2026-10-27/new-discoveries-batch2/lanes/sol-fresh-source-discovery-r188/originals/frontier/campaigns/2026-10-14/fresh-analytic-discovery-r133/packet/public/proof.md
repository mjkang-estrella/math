# Brannen's reverse projection inequality for 4-polytopes with at most six facets: author proof

Author: Myeongjin Kang (no affiliation). Original exposition CC BY 4.0; original code MIT.
Runner provenance: Factory Droid / claude-opus-5-5 / high. Drafted after the freeze recorded in FROZEN-THEOREM.md
(frozen 2026-10-20T17:21:32Z). This is an author proof submitted for review. It assigns itself no gate, verdict or
count.

## Statement (verbatim scope of FROZEN-THEOREM.md)

**Theorem.** Let K be a convex polytope in R^4 with non-empty interior and at most 6 facets. Then
V_4(ΠK) <= (160/3) V_4(K)^3, and equality holds if and only if K is a simplex.

Here h_{ΠK}(u) = V_3(K | u^⊥) for unit u, and 160/3 = c_4, where c_n := (n+1) n^n / n!. Write
P_n(K) := V_n(ΠK) / V_n(K)^(n-1). P_n is invariant under invertible affine maps, and P_n(simplex) = c_n
([FHLX, (1.3)]; also checked numerically in geometry_control.py).

## Notation

E_1, E_2, ... are iid Exp(1) random variables. For c ∈ R^r, D(c) := Σ_{i<j} |c_i - c_j|; for sorted entries
s_1 <= ... <= s_r this equals Σ_i (2i - r - 1) s_i. For b ∈ R^n put W_b := Σ_j b_j E_j,
p(b) := P(W_b > 0), P(b) := E W_b^+, N(b) := E W_b^- = P(-b). Note p(-b) = 1 - p(b) when b ≠ 0, because W_b
then has a density (Lemma 5) and so P(W_b = 0) = 0.

The auxiliary inequality used for n = 4 is

    (S)_n(b):   D(b) p(b)^2 <= (n+1) P(b).

## Classical facts used (cited, not reproved)

- (F1) Minkowski: the facet area vectors w_i = f_i u_i of a polytope satisfy Σ w_i = 0 and span R^n.
- (F2) Cauchy's projection formula: V_{n-1}(K|u^⊥) = (1/2) Σ_i f_i |<u_i, u>|. Hence ΠK is the zonotope
  Σ_i [-w_i/2, w_i/2].
- (F3) Zonotope volume (Shephard, McMullen): V_n(Σ_i [0, w_i]) = Σ_{|J|=n} |det W_J|, where W_J is the n×n matrix
  with columns w_j, j ∈ J.
- (F4) Minkowski's first inequality: for convex bodies K, L with non-empty interiors,
  V(K[n-1], L) = (1/n) Σ_i h_L(u_i) f_i >= V(K)^((n-1)/n) V(L)^(1/n), when K is a polytope with facet data (u_i, f_i).
- (F5) Prékopa: marginals of log-concave functions are log-concave. Consequently convolutions of log-concave
  densities are log-concave, and the survival function of a log-concave density is log-concave.
- (F6) Brunn's concavity principle: for a convex body C of dimension n+1 and a linear functional ℓ, the function
  t -> vol_n(C ∩ {ℓ = t})^(1/n) is concave on the set where it is positive.
- (F7) Coarea formula for a linear function on a simplex; the Gamma-Dirichlet fact: if E = (E_1..E_m) and
  S = Σ E_i, then S ~ Gamma(m) and E/S (uniform on the simplex Δ^{m-1}) are independent.
- (F8) Jacobi's complementary minor identity: for an orthogonal N×N matrix Q and index sets I, J with |I| = |J|,
  |det Q[I, J]| = |det Q[I^c, J^c]|.

## 1. Exact variational formula (equality version of FHLX Prop. 4.1)

Let K ⊂ R^n be a polytope with facets F_1, ..., F_m, distinct outer unit normals u_i, areas f_i > 0, and support
numbers h_i = h_K(u_i). Translate K so that 0 ∈ int K; then h_i > 0. Let w_i = f_i u_i, let W be the n×m matrix
with columns w_i, let R ⊂ R^m be the row space of W (dimension n), and let L := ker W = R^⊥ (dimension m - n). By
(F1), 1 = (1, ..., 1) ∈ L. Let H = {x ∈ R^m : Σ x_i = 1} and Δ = H ∩ [0, ∞)^m. For λ ∈ H put
S_λ := (λ + R) ∩ Δ.

**Lemma 1.** 1 / V(K)^(n-1) = n^n max_{λ ∈ H} H^n(S_λ) / sqrt(det W W^T), and the maximum is attained at
λ* := (f_i h_i / (n V(K)))_i, which lies in the relative interior of Δ.

*Proof.* For λ ∈ H let L_λ := {x ∈ R^n : <w_i, x> <= λ_i for all i}. It is bounded: for x ≠ 0, Σ_i <w_i, x> = 0 and
the w_i span R^n, so <w_i, x> > 0 for some i. The affine map φ(x) := λ - W^T x is injective, satisfies
Σ_i φ(x)_i = 1 - <Σ_i w_i, x> = 1, and maps R^n onto λ + R. Hence φ(L_λ) = S_λ and
H^n(S_λ) = sqrt(det W W^T) V(L_λ).

If int L_λ = ∅ then V(L_λ) = 0. Otherwise, L_λ ⊂ {x : <u_i, x> <= λ_i / f_i} gives h_{L_λ}(u_i) <= λ_i / f_i,
and (F4) gives V(K)^((n-1)/n) V(L_λ)^(1/n) <= (1/n) Σ_i λ_i = 1/n. So n^n V(L_λ) <= V(K)^(-(n-1)) for every λ ∈ H.
For λ = λ*: Σ λ*_i = (Σ f_i h_i)/(n V(K)) = 1 by Minkowski's volume formula, and L_{λ*} = K / (n V(K)), because
<w_i, x> <= f_i h_i / (nV) iff <u_i, x> <= h_i / (nV). Then n^n V(L_{λ*}) = n^n V(K) / (n V(K))^n = V(K)^(1-n).
Finally λ*_i > 0 for all i. ∎

## 2. Gale normalisation for m = n + 2

From now on m = n + 2, so dim L = 2 and L = span{1, a} for some a ∈ L with a ⊥ 1, a ≠ 0. Since Σ a_i = 0 and
a ≠ 0, I := (min_i a_i, max_i a_i) is a non-empty open interval.

**Lemma 2.** V(ΠK) / sqrt(det W W^T) = D(a) / (sqrt(m) |a|).

*Proof.* Let the rows of U (n×m) be an orthonormal basis of R. Then W = M U with M = W U^T ∈ GL(n), so
det W W^T = (det M)^2 and det W_J = det M · det U_J. Let Q be the orthogonal m×m matrix whose rows are those of U
followed by e := 1/sqrt(m) and e' := a/|a| (an orthonormal basis of L = R^⊥). By (F8), for J^c = {i, j}:
|det U_J| = |e_i e'_j - e_j e'_i| = |a_i - a_j| / (sqrt(m) |a|). By (F2) and (F3),
V(ΠK) = Σ_{|J|=n} |det W_J| = |det M| Σ_{i<j} |a_i - a_j| / (sqrt(m) |a|). ∎

## 3. Sections of the simplex and the exponential representation

For t ∈ R let Y_t := Σ_i (a_i - t) E_i. If t ∈ I, some coefficient a_{i+} - t is positive and some a_{i-} - t is
negative. Write Y_t = U_t + Z_t with U_t := (a_{i+} - t) E_{i+} + (a_{i-} - t) E_{i-} and Z_t the remaining sum. U_t
has a bounded continuous density g_t (an asymmetric Laplace density, computed in Section 4). Hence
f_{Y_t}(y) := E g_t(y - Z_t) is a bounded continuous density of Y_t, by dominated convergence. Below,
f_{Y_t}(0) always means this continuous version.

**Lemma 3.** For t ∈ I, σ(t) := H^n({x ∈ Δ : <a, x> = t}) = sqrt(m) |a| f_{Y_t}(0) / (m-2)!.

*Proof.* Let s be uniform on Δ and X := <a, s>. Inside H, the gradient of x -> <a, x> is a (because a ⊥ 1), and
H^{m-1}(Δ) = sqrt(m)/(m-1)!. By (F7) (coarea), φ_X := σ / (|a| H^{m-1}(Δ)) on I, and 0 outside I, is a density of X.
By (F6), σ^(1/n) is concave on I, so φ_X is continuous on I. It is also bounded, since a concave function on a
bounded interval is bounded above.

Fix t ∈ I and let S ~ Gamma(m), independent of s, as in (F7). Then Y_t has the law of S (X - t), since E = S s
in law. A change of variables gives a density ψ(y) = ∫_0^∞ φ_X(t + y/r) r^{-1} γ_m(r) dr, where γ_m is the
Gamma(m) density. Since φ_X is bounded and continuous at t, and r^{-1} γ_m is integrable (m >= 2), ψ is continuous
at 0 and ψ(0) = φ_X(t) E[S^{-1}] = φ_X(t)/(m-1). Two densities of Y_t agree almost everywhere, and both ψ and
f_{Y_t} are continuous at 0, so f_{Y_t}(0) = φ_X(t)/(m-1). Hence
σ(t) = |a| (sqrt(m)/(m-1)!) (m-1) f_{Y_t}(0). ∎

**Proposition A (exact (n+2)-facet formula).** If K ⊂ R^n has exactly n + 2 facets, then

    P_n(K) / c_n = max_{t ∈ I} D(a) f_{Y_t}(0) / (n+1),

and the maximum is attained at t* := <a, λ*>, which lies in I.

*Proof.* For λ ∈ H, λ + R = {x ∈ H : <a, x> = <a, λ>}, since R = L^⊥ = {1, a}^⊥. So H^n(S_λ) = σ(<a, λ>). By
Lemma 1, n^n max_{λ ∈ H} σ(<a,λ>) / sqrt(det WW^T) = V(K)^(1-n), and the maximum is attained at λ*. Since λ* is in
the relative interior of Δ, t* ∈ I, so the maximum over t ∈ I equals the maximum over λ. By Lemmas 2 and 3,
P_n(K) = n^n (D(a) / (sqrt(m)|a|)) σ(t*) = n^n D(a) f_{Y_{t*}}(0) / n!, using m - 2 = n. Divide by
c_n = (n+1) n^n / n!. ∎

(Proposition A, with sup in place of max, is r132's reduction R1–R4. It refines FHLX Prop. 4.1 and (4.9), which give
the inequality ">=" for each λ. The proof above is self-contained given (F1)–(F8). geometry_control.py checks the
normalisation against a direct computation of V(K), the facet areas and V(ΠK) for 40 random 6-facet 4-polytopes,
with agreement to 1e-10. That is a float control, not part of the proof.)

## 4. Normal form

Fix t ∈ I. Choose an index i+ attaining max a and an index i- attaining min a. Set μ := 2 / (max a - min a),
α := μ (t - min a) ∈ (0, 2), β := μ (max a - t) = 2 - α, and let b ∈ R^n be the vector of μ (a_j - t) over
j ∉ {i+, i-}. Then b ∈ [-α, β]^n.

**Lemma 4 (normal form).** D(a) f_{Y_t}(0) / (n+1) = Ψ(α, b), where

    Ψ(α, b) := (1 + D(b)/(2(n+1))) · E exp(-W_b^+/α - W_b^-/β),   β = 2 - α.

*Proof.* Both D(a) and f_{Y_t}(0) are unchanged when a is replaced by a - t 1. Under scaling by μ, D(μc) = μ D(c)
and f_{μY}(0) = f_Y(0)/μ for the continuous versions. The scaled knots are β (at i+), -α (at i-) and b. Since every
b_j lies in [-α, β], each b_j contributes |β - b_j| + |b_j + α| = α + β = 2, so
D(μ(a - t1)) = 2 + 2n + D(b). The variable U := β E' - α E'' (E', E'' iid Exp(1)) has density
g(u) = (α+β)^{-1} exp(-u^+/β - u^-/α) = (1/2) exp(-u^+/β - u^-/α): for u > 0,
g(u) = ∫_0^∞ β^{-1} e^{-(u + α r)/β} e^{-r} dr = e^{-u/β}/(α+β), and symmetrically for u < 0. Hence
f_{μY}(0) = E g(-W_b) = (1/2) E exp(-W_b^-/β - W_b^+/α). Multiplying gives
(2(n+1) + D(b)) / (2(n+1)) · E exp(-W_b^+/α - W_b^-/β). ∎

**Lemma 4' (b ≠ 0 for genuine polytopes).** If K has exactly n + 2 facets, then b ≠ 0 for every t ∈ I.

*Proof.* If b = 0, then v := a - t1 ∈ L is supported on {i+, i-}, with v_{i+} > 0 > v_{i-}. Then
Σ v_i w_i = 0 gives w_{i+} = (|v_{i-}| / v_{i+}) w_{i-}, so u_{i+} = u_{i-}. This is impossible, because distinct
facets have distinct outer normals. ∎

## 5. Convex-order comparison with exponentials (new mechanism)

**Lemma 5 (log-concavity).** If b ≠ 0, W_b has a log-concave density. If moreover p := p(b) ∈ (0, 1), then the
conditional laws X+ := (W_b | W_b > 0) and X- := (-W_b | W_b < 0) have log-concave densities on (0, ∞).

*Proof.* For b_j ≠ 0, b_j E_j has a log-concave density, and zero coefficients do not contribute. Convolutions of
log-concave densities are log-concave (F5). Restricting a log-concave density to (0, ∞), or reflecting it, and then
normalising keeps it log-concave. ∎

**Lemma 6 (HNBUE Laplace bound).** Let X >= 0 have a log-concave density on (0, ∞) and finite mean μ > 0. Then
E e^{-sX} <= 1/(1 + sμ) for all s >= 0.

*Proof.* Let F̄(x) = P(X > x). This function is continuous, and log-concave by (F5). So for each r >= 0 the ratio
F̄(x + r)/F̄(x) is non-increasing in x on {F̄ > 0}. Put G(x) := ∫_x^∞ F̄. Then G(0) = μ, G is C^1, and G' = -F̄.
If F̄(x) > 0, then G(x) = F̄(x) ∫_0^∞ F̄(x+r)/F̄(x) dr <= F̄(x) ∫_0^∞ F̄(r)/F̄(0) dr = μ F̄(x), since F̄(0) = 1. If
F̄(x) = 0, then G(x) = 0. So G <= -μ G', hence (e^{x/μ} G(x))' <= 0 and G(x) <= μ e^{-x/μ}. (This is the HNBUE
property.) By Fubini, E e^{-sX} = 1 - s ∫_0^∞ e^{-sx} F̄(x) dx. Integration by parts gives
∫_0^∞ e^{-sx} F̄ dx = G(0) - s ∫_0^∞ e^{-sx} G dx >= μ - s μ ∫_0^∞ e^{-(s + 1/μ)x} dx = μ/(1 + sμ). Hence
E e^{-sX} <= 1 - sμ/(1 + sμ) = 1/(1 + sμ). ∎

**Proposition B (reduction of the normal form to (S)).** Let n >= 1, α ∈ (0, 2), β = 2 - α, and b ∈ R^n \ {0}.
Assume (S)_n(b) and (S)_n(-b), and assume (S)_n(b) is strict when 0 < p(b) < 1. Then Ψ(α, b) < 1.
(No box constraint on b is needed.)

*Proof.* Write d := D(b)/(2(n+1)), p := p(b), P := P(b), N := N(b). Then (S)_n(b) reads 2 d p^2 <= P, and
(S)_n(-b) reads 2 d (1-p)^2 <= N.

*Case p = 1.* Then W_b > 0 almost surely, P = E W_b > 0, and d <= P/2 < P/α. By Lemmas 5 and 6 with X = W_b,
Ψ <= (1 + d)/(1 + P/α) < 1.

*Case p = 0.* This is symmetric: d <= N/2 < N/β, and Ψ <= (1 + d)/(1 + N/β) < 1.

*Case 0 < p < 1.* Put A := E[X+] = P/p > 0 and B := E[X-] = N/(1-p) > 0. Since P(W_b = 0) = 0, Lemmas 5 and 6
give

    E exp(-W^+/α - W^-/β) = p E e^{-X+/α} + (1-p) E e^{-X-/β} <= p α/(α+A) + (1-p) β/(β+B).

Let Q := 1 - (1+d)[p α/(α+A) + (1-p) β/(β+B)]. Expanding,

    (α+A)(β+B) Q / (αβ) = [P/α + N/β - d] + (AB/(αβ)) [1 - d (p^2 α/P + (1-p)^2 β/N)],

where we used pA = P, (1-p)B = N, pα/A = p^2 α/P and (1-p)β/B = (1-p)^2 β/N. For the second bracket, the two
(S) inequalities give d p^2 α/P <= α/2 and d (1-p)^2 β/N <= β/2, so the bracket is >= 1 - (α+β)/2 = 0. It is
strictly positive, because the first of these inequalities is strict and α > 0. For the first bracket,
sqrt(2d) p <= sqrt(P) and sqrt(2d)(1-p) <= sqrt(N) give sqrt(2d) <= sqrt(P) + sqrt(N). By Cauchy–Schwarz,
(sqrt P + sqrt N)^2 <= (P/α + N/β)(α + β) = 2 (P/α + N/β). So d <= P/α + N/β. Hence Q > 0, that is, Ψ < 1. ∎

*Remark (where the separation comes from).* Replacing b by λb, the condition "Q >= 0" becomes
[P/α + N/β - d] + λ(AB/(αβ))[1 - d(p^2α/P + (1-p)^2β/N)] >= 0, which is affine in λ. Taking the worst α at the
endpoints of (0, 2) turns the second bracket into the scale-free condition (S). For n >= 5, (S)_n fails (see
Section 7), so the method as stated stops at n = 4.

## 6. The certificate for (S)_4

**Lemma 7 (partial fractions).** Let c_1, ..., c_r be distinct non-zero reals, with at least one positive, and
let W = Σ c_j E_j. With A_j := Π_{i≠j} c_j/(c_j - c_i),

    P(W > 0) = Σ_{c_j > 0} A_j,      E W^+ = Σ_{c_j > 0} A_j c_j.

*Proof.* The integrable function g(x) := Σ_j A_j |c_j|^{-1} e^{-x/c_j} 1{x c_j > 0} has two-sided Laplace transform
∫ e^{-sx} g(x) dx = Σ_j A_j/(1 + s c_j) for |s| < min_j 1/|c_j|. This equals Π_j (1 + s c_j)^{-1} = E e^{-sW}: it is
the partial-fraction decomposition, with simple poles, numerator of degree 0 < r, and residues
A_j = Π_{i≠j}(1 - c_i/c_j)^{-1}. Two finite signed measures whose two-sided Laplace transforms agree on an
interval around 0 are equal, by analytic continuation to a vertical strip and Fourier uniqueness. So g is the
density of W. Integrate g and x g(x) over (0, ∞). ∎

**Proposition C ((S)_4).** For every b ∈ R^4, D(b) p(b)^2 <= 5 P(b). The inequality is strict when b has both a
positive and a negative entry.

*Proof.* Both sides are invariant under permutations of b. If b has no positive entry, both sides are 0. Otherwise
b has k >= 1 positive entries u_1 >= ... >= u_k > 0, l >= 0 negative entries -v_1 <= ... <= -v_l < 0, and
z = 4 - k - l zeros. Parametrise by x ∈ [0,∞)^k, y ∈ [0,∞)^l with x_k > 0, y_l > 0, u_i = x_i + ... + x_k and
v_j = y_j + ... + y_l. Put Den := Π_{i,j}(u_i + v_j) > 0 and V(u) := Π_{a<b}(u_a - u_b).

On the dense set where all x_i, y_j > 0, the entries are distinct, and Lemma 7 gives p · Den · V(u) = Ñp and
P · Den · V(u) = ÑP. Here Ñp := Σ_i (-1)^(i-1) u_i^(k-1+l) V(u without u_i) Π_{i'≠i, j}(u_{i'} + v_j), and ÑP is the
same with exponent k + l. This uses V(u) = (-1)^(i-1) Π_{i'≠i}(u_i - u_{i'}) V(u without u_i). The exact
polynomial divisions Np := Ñp / V(u) and NP := ÑP / V(u) succeed; certificate.py performs them factor by factor.
So p = Np/Den and P = NP/Den there.

Both sides of these identities are continuous on the closed parameter domain (x_k, y_l > 0). D is linear. p is
continuous at every b ≠ 0, by the portmanteau theorem, since P(W_b = 0) = 0. P is continuous by dominated
convergence. Hence the identities hold on the whole domain, and with D(b) linear in (x, y),

    5 P - D p^2 = T / Den^2,    T := 5 · NP · Den - D · Np^2 ∈ Q[x, y].

certificate.py computes T exactly for each of the ten patterns (k, l, z) with k >= 1:
(1,0,3), (1,1,2), (1,2,1), (1,3,0), (2,0,2), (2,1,1), (2,2,0), (3,0,1), (3,1,0), (4,0,0). Every coefficient of every
T is non-negative; the minimum non-zero coefficient is 2, and the largest polynomial has 118 terms. Hence T >= 0.
For each pattern T also contains a monomial with positive coefficient that involves only x_k and y_l, which are
positive. So T > 0 everywhere on the domain, which gives strictness, in particular when l >= 1. The script also
checks Np/Den, NP/Den and D against Lemma 7 at random rational points, exactly. As a negative control, the same
checker rejects (S)_5 for the pattern (4,1,0) (minimum coefficient -6). ∎

## 7. Proof of the Theorem

Let K ⊂ R^4 be a polytope with non-empty interior and at most 6 facets. Every 4-polytope has at least 5 facets, and
one with exactly 5 facets is a simplex, so P_4(K) = c_4 in that case. Suppose K has exactly 6 facets = n + 2. By
Proposition A and Lemma 4, P_4(K)/c_4 = Ψ(α, b) for some α ∈ (0, 2) and b ∈ [-α, 2-α]^4, namely the normal form at
t*. By Lemma 4', b ≠ 0. By Proposition C, (S)_4(b) and (S)_4(-b) hold, and (S)_4(b) is strict whenever
0 < p(b) < 1, since then b has entries of both signs. By Proposition B, Ψ(α, b) < 1. Hence P_4(K) < c_4 for every
4-polytope with exactly 6 facets, and P_4(K) = c_4 exactly for simplices. ∎

## 8. Scope, limitations and strongest-reduction comparison

- **Scope.** Only 4-polytopes with at most 6 facets. Nothing is claimed for general convex bodies in R^4, for
  4-polytopes with 7 or more facets, or for dimensions 5 to 8.
- **Integrated reduction (routine/credited).** Lemma 1 is the equality form of FHLX Prop. 4.1 (Minkowski's
  inequality with its equality case). Lemmas 2–4 are the Gale/row-space normalisation, the coarea formula and the
  Gamma–Dirichlet representation. All of these appear at sketch level in r132 (R1–R4 and (★)), which in turn builds
  on FHLX §4. These are equivalent formulations, not results. Lemma 7 is the classical hypoexponential formula.
- **New operations (author).** (i) Log-concavity of W_b plus the HNBUE Laplace bound (Lemmas 5–6) compare the
  conditional positive and negative parts of W_b with exponentials of the same means. This turns the
  infinite-dimensional expectation in (★) into a rational function of (p, P, N, α). (ii) The affine-in-scale
  decomposition (Proposition B) removes both the scale and α, and reduces (★) to the scale-free algebraic inequality
  (S)_n for b and -b. (iii) An exact certificate for (S)_4: non-negative coefficients in ordered variables for all
  ten sign patterns.
- **Why n = 4 only.** (S)_n fails for n >= 5. With b = (-1, ε, ..., ε), D(b)p^2/((n+1)P) tends to
  2(n-1)^2/(n(n+1)), which exceeds 1 for n >= 5 (author asymptotics; float suprema for n = 2..9 are
  .333 .666 .897 1.060 1.181 1.272 1.346 1.405). The loss comes from separating the two brackets in Proposition B.
  The full non-separated condition, with the box constraint, appeared numerically <= 1 for n <= 8 in float searches.
  That was not certified and is not claimed.
- **Novelty limits.** Project history (I43 §1.3, r112, r131, r132) contains no proof of any n = 4 case. In the
  literature read (FHLX introduction, Saroglou arXiv:1409.4347v2 introduction), prior sharp results for Brannen's
  inequality are n <= 3 (all bodies, [CFLXX] as cited by FHLX) and 3-dimensional classes (zonoids, cones, double
  cones; Saroglou 2011, as described by FHLX and Saroglou 2014). No dimension-4 class result was found. This is a
  search-limited statement, not a worldwide-priority claim. See reading-limits.md.

## References

- [FHLX] Y. Feng, S. Hu, W. Liu, L. Xu, On the Reverse Projection Inequality, arXiv:2610.13953v1 (2026). Read in
  full via the I43-retained text: Thm 1.1–1.3, §4 Props. 4.1, 4.2, Lemmas 4.3, 4.4, Props. 4.5, 4.6, (4.9), (4.19).
- [CFLXX] S. Chen, Y. Feng, Y. Li, D. Xi, L. Xu, Petty's conjectured projection inequality in dimension three
  (2026), cited via FHLX Thm 1.1; not read.
- N. S. Brannen, Volumes of projection bodies, Mathematika 43 (1996); cited via FHLX; not read.
- C. Saroglou, Volumes of projection bodies of some classes of convex bodies, Mathematika 57 (2011); not read (PDF
  fetch failed); described via FHLX and Saroglou arXiv:1409.4347v2.
- Source P (pinned preprint "A product counterexample to the simplex maximum for projection body volume",
  2026-09-24): read in full; products of simplices; not used in the proof.
- Classical facts (F1)–(F8): Minkowski, Cauchy, Shephard/McMullen, Prékopa, Brunn, coarea, Lukacs/Dirichlet,
  Jacobi. Cited as standard; the primary bodies were not reread in this round.
- r132 (project, author derivations R1–R4, (★)): credited for the reduction route.
