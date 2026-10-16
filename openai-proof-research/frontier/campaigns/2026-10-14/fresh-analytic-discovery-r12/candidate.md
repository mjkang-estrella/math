# Candidate: sharp one-third stability of Brenier maps for log-concave sources

Author: Myeongjin Kang (no affiliation). Original prose CC BY 4.0; code MIT.

Status: proposed full proof of the frozen target in `original-scope.md`,
submitted for independent parent review. No PASS or count is claimed here.

Source family: openai/math `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`,
`preprints/Sharp-One-Third-Stability-of-Brenier-Maps-September-25-2026/`
(entry 374). Labels such as `cells:calculus` refer to that manuscript;
pinned copies with matching Git blobs are in `inputs/pinned/brenier/`.

## 1. Statement

**Standing hypotheses (H).** `d >= 2`. `K` is a compact convex subset of
`R^d` with nonempty interior. `rho = f dx` is a probability measure with
`f: R^d -> [0, inf)` Borel, `f = 0` off `K`, `f > 0` on `int K`, and `log f`
concave on `int K`. Put `Lambda = sup_{int K} f`. `Y` is a nonempty compact
set, `R, L >= 1`, `K subset B(0,R)`, `Y subset B(0,L)`, and
`P_K = sum_j A_j` with `A_j = |proj_{e_j^perp} K|_{d-1}`.

**Theorem LC.** Under (H):

- (a) for every `lambda` in `P(Y)` there is a unique (`rho`-a.e.) quadratic
  optimal map `T_lambda` from `rho` to `lambda`, and the optimal plan is
  unique;
- (b) for all `mu, nu` in `P(Y)`,
  `||T_mu - T_nu||_{L^2(rho)} <= C_LC W_2(mu,nu)^{1/3}`, where
  `C_LC^2 = 18 d (1 + sqrt 162)^2 R^2 + 52 L^2 Lambda P_K`;
- (c) the exponent `1/3` cannot be raised uniformly over the class (H).

For the uniform source, `Lambda = 1/|K|`, and (b) recovers the pinned
`main:stability` with slightly larger numerical constants (18 and 52 in
place of 12 and 28). The new content is that the constant does not involve
`inf f`, so densities vanishing at `partial K` are allowed (for example
`f` proportional to `dist(x, partial K)`, or to a product of one-sided
exponentials, or a Gaussian restricted to `K`).

## 2. Preliminary facts about the source

**F1. `Lambda < inf` and `f` is continuous on `int K`.** A finite concave
function `phi = log f` on the open convex set `int K` is continuous there
and has a supergradient `p` at a point `x_0`. Then
`phi(x) <= phi(x_0) + |p| 2R` on `int K`, so `f` is bounded above.

**F2. Null sets.** `partial K` has zero volume (pinned `cells:calculus`,
first paragraph). Since `f > 0` on `int K` and `rho << dx`, a subset of `K`
is `rho`-null iff it is Lebesgue-null. In particular the tie hyperplanes of
finite affine maxima are `rho`-null.

**F3. Slices.** If a line `l` meets `int K`, then
`relint(K cap l) = int K cap l` (the pinned segment argument in
`cells:calculus`, valid for any affine subspace). For each coordinate
direction `e_j`, the lines parallel to `e_j` that meet `K` but miss `int K`
project onto `proj K \ proj(int K) = proj K \ int(proj K)`, the boundary of a
convex body in `R^{d-1}`, a null set.

## 3. Cell calculus with weight `f`

Use the notation of pinned `cells:calculus` but with
`M_i = rho(P_i)`, `B_i = int_{P_i} x drho`, and face coefficients

`g_ij = |y_i - y_j|^{-1} int_{F_ij} f dS`,
`b_ij = |y_i - y_j|^{-1} int_{F_ij} x f dS`.

**Proposition 3.1 (weighted `cells:calculus`).** On distinct-site
configurations with all `M_i > 0`, `M_i, B_i` are `C^1` in intercepts and
sites, with

`DM_i[r,v] = sum_{j != i} [ g_ij (r_i - r_j) + b_ij . (v_i - v_j) ]`,

`DB_i[r,v] = sum_{j != i} b_ij (r_i - r_j)
             + sum_{j != i} |y_i - y_j|^{-1} int_{F_ij} x (x . (v_i - v_j)) f dS`.

The graph `{g_ij > 0}` is connected, and `(Gq)_i = DM_i[q,0]` has kernel the
constants and range `{z : sum z_i = 0}`.

*Proof.* Copy the pinned proof with `I_i^phi = int_K phi f prod_j 1{l_ij >= 0} dx`.
The geometric facts (strictly active interior points, distinct equality
planes, null exceptional sets on `H_ij`) use only `M_i > 0`, which by F2
gives cells of positive volume. In the difference quotient, after the
change of variables `x = z + h t n_ij`, the integrand now contains
`f(z + h t n_ij) 1_K(z + h t n_ij)`. For `z in int K` it converges to `f(z)`
by F1; for `z notin K` it is eventually `0`; the remaining `z in partial K cap H_ij`
form a surface-null set (F3 applied in the hyperplane). It is dominated
by `Lambda sup|phi|` on a bounded region. Dominated convergence gives the
displayed formulas with the weight `f` on the face. Continuity of the
coefficients under joint changes of configuration follows in the same way:
the graph maps converge uniformly, `f` composed with them converges at
every point of `int K`, and `Lambda` dominates. For connectivity, the pinned
argument produces, on each change of active index along a segment in
`int K`, a relatively open disk of the common face contained in `int K`;
`f > 0` there, so `g_ij > 0`. Symmetry `g_ij = g_ji` gives
`q . Gq = sum_{i<j} g_ij (q_i - q_j)^2`, hence the kernel and range claims. ∎

**Proposition 3.2 (weighted `cells:weights`).** For positive weights
`m_i` with sum `1` and distinct sites there is a unique intercept vector
with `M_i = m_i` and `sum m_i c_i = 0`; it is `C^1` in the sites.

*Proof.* The pinned proof uses only: `F_y(c) = int max_i(x.y_i + c_i) drho - sum m_i c_i`
is convex and coercive on `H_m` (uses `|x| <= R` on the support of `rho`);
`grad_c F_y = (M_i - m_i)` (a.e. unique maximizer, F2); and invertibility of
`G : H_m -> H_0` (Proposition 3.1). All hold for `rho`. ∎

**Lemma 3.3 (`cells:optimality`).** Unchanged: its proof uses only that
tie sets are `rho`-null (F2).

## 4. Weighted midpoint domination (M)

**Lemma 4.1.** Let `U, V subset K` be compact convex sets of positive
volume, `alpha = rho(U)`, `beta = rho(V)`. There is a coupling `(X, Z)` of
`rho|_U / alpha` and `rho|_V / beta` such that

`sqrt(alpha beta) Law((X+Z)/2) <= rho`  (as measures on `R^d`).

*Proof.* Run the pinned Knothe construction of `moments:midpoint` with the
fiber functions

`p_k(xi) = int_{R^{d-k}} f(xi, eta) 1_{int U}(xi, eta) d eta`,  `p_d = f 1_{int U}`.

Then `p_0 = alpha` (F2). On `D_k = proj_k(int U)`, `p_k` is positive (an open
set of fibre points lies in `int U subset int K`, where `f > 0`) and
continuous: as the prefix tends to `xi_0 in D_k`, the integrand converges
at every `eta` with `(xi_0, eta) in int U` (F1) or `notin U`, the remaining
fibre points `partial U` are fibre-null by the pinned slice-boundary
property, and `Lambda 1_{bounded}` dominates. The conditional density
`t -> p_k(xi,t)/p_{k-1}(xi)` is therefore continuous and positive on an open
interval and zero outside, so the quantile map is well defined, Borel, and
`C^1` in `s_k` with

`d_{s_k} X_k = p_{k-1}(X_1..X_{k-1}) / p_k(X_1..X_k)`.

With `s` uniform on `(0,1)^d`, successive conditioning shows `Law(X) = rho|_U/alpha`,
and the product telescopes to `prod_k d_{s_k} X_k = alpha / f(X)`, where
`X in int U`. Build `Z` from the same `s` for `V`: `prod_k d_{s_k} Z_k = beta / f(Z)`.
For `H = (X+Z)/2`, coordinatewise AM–GM gives

`prod_k d_{s_k} H_k >= sqrt(alpha beta / (f(X) f(Z))) >= sqrt(alpha beta) / f(H)`,

the last step by log-concavity, since `X, Z in int K` and hence
`H in int K` and `f(H) >= sqrt(f(X) f(Z))`. The pinned substitution argument
(which uses only the triangular structure, strict monotonicity and `C^1`
regularity in the last active variable) gives, for every nonnegative Borel
`G`, `int_{(0,1)^d} G(H(s)) prod_k d_{s_k}H_k(s) ds <= int G dx`. Apply it to
`G = g f` with `g >= 0` Borel:

`sqrt(alpha beta) E g(H) = int g(H) f(H) sqrt(alpha beta)/f(H) ds
  <= int g(H) f(H) prod d_{s_k}H_k ds <= int g f dx = int g drho`. ∎

**Remark 4.2 (method boundary; not part of Theorem LC).** Let `f` be
continuous and positive on an open convex set `Omega`. If the conclusion of
Lemma 4.1 holds for every pair of closed balls in `Omega` (with any
coupling), then `log f` is concave on `Omega`. Indeed, for `U = B_r(x)`,
`V = B_r(z)`, the midpoint lies in `B_r((x+z)/2)`, so comparing total masses
gives `sqrt(rho(B_r(x)) rho(B_r(z))) <= rho(B_r((x+z)/2))`; dividing by
`|B_r|` and letting `r -> 0` yields `sqrt(f(x)f(z)) <= f((x+z)/2)`, and
continuous midpoint-log-concave functions are log-concave. Thus the
domination step of the pinned method cannot be transplanted verbatim to
continuous densities that are only bounded above and below.

## 5. The moment estimate (D)

**Proposition 5.1 (weighted `moments:derivative`).** Under (H), at a
distinct-site configuration with all `M_i > 0` and for every `q in R^N`,

`sum_i |DB_i[q,0]|^2 / M_i <= 162 R^2 sum_i |DM_i[q,0]|^2 / M_i`.

*Proof.* Follow the pinned proof word for word, with the single change
that `X_i, Z_i` are coupled by Lemma 4.1 applied to `U = P_i^-`, `V = P_i^+`
(compact, convex, positive volume because `alpha_i, beta_i > 0` and F2),
so that `Law(X_i) = rho|_{P_i^-}/alpha_i`, `Law(Z_i) = rho|_{P_i^+}/beta_i`.
The pinned averaging argument places `(X_i + Z_i)/2` in `P_i`, hence
Lemma 4.1 gives `gamma_i Law((X_i+Z_i)/2) <= rho|_{P_i}`. The rest uses only:
`Phi = R^2 - |x|^2` takes values in `[0, R^2]` on `K`; the identity
`Phi((X+Z)/2) = (Phi(X)+Phi(Z))/2 + |X-Z|^2/4`;
`int_K Phi drho = sum_i alpha_i A_i^- = sum_i beta_i A_i^+` (both perturbed
partitions cover `K` up to `rho`-null overlaps); `|A_i^- - A_i^+| <= 2R sqrt(D_i)`;
continuity of masses in `s` (Proposition 3.1); and the derivative limits
of Proposition 3.1. I rechecked the algebra:

- `(alpha+beta)/2 - gamma = (sqrt alpha - sqrt beta)^2/2 <= delta^2/(8 gamma)`;
- `A/4 <= R^2 B/8 + (R/2) sqrt(A B)` and `(R/2)sqrt(AB) <= A/8 + R^2 B/2` give `A <= 5 R^2 B`;
- `|Delta B_i| <= R|delta_i| + alpha_i sqrt(D_i)`, `alpha_i^2/M_i <= 4 M_i <= 8 gamma_i`,
  `B <= 2E`, hence `sum |Delta B_i|^2/M_i <= 2R^2 E + 16 A <= 2R^2E + 160 R^2 E = 162 R^2 E`. ∎

## 6. Linear potential stability (P)

**Proposition 6.1 (weighted `finite:potentials`).** For finitely supported
`mu, nu` in `B(0,L)` there are convex `L`-Lipschitz finite maxima
`u_0, u_1` with `grad u_0 = T_mu`, `grad u_1 = T_nu` `rho`-a.e., and

`||u_0 - u_1||_{L^2(rho)} <= (1 + sqrt 162) R W_2(mu, nu)`.

*Proof.* The pinned proof uses: an optimal finite coupling and cyclical
monotonicity (independent of `rho`); Proposition 3.2 for `C^1` intercepts
along the interpolated sites; the symmetry identity
`sum_i r_i DM_i[q,0] = - sum_i v_i . DB_i[q,0]`, which follows from
Proposition 3.1 because the same weighted coefficients `g_ij, b_ij` appear
in the mass-site and moment-intercept terms; solvability of
`DM_i[q,0] = m_i r_i` (range statement); Proposition 5.1; `|x| <= R` on `K`;
`rho`-null tie sets (F2); and Lemma 3.3 at the endpoints. Each holds
under (H). ∎

## 7. Weighted gradient interpolation (G)

**Lemma 7.1.** Let `u_0, u_1` be convex and `L`-Lipschitz on `K`, and
`F = u_0 - u_1`. For every `h > 0`,

`||grad u_0 - grad u_1||^2_{L^2(rho)} <= 18 d h^{-2} ||F||^2_{L^2(rho)} + 52 L^2 Lambda P_K h`.

*Proof.* Fix `j`. By F3 and Fubini it suffices to prove, for every line
`x' + R e_j` meeting `int K`, with slice `[a, b]`, `(a, b) subset int K`, and
`g(t) = f(x' + t e_j)`,

`int_a^b |F'|^2 g dt <= 18 h^{-2} int_a^b F^2 g dt + 52 L^2 Lambda h`,   (7.1)

and then integrate over `x'` (the set of such `x'` has measure at most `A_j`).
Here `g` is positive, log-concave and `<= Lambda` on `(a,b)`; the restrictions
of `u_0, u_1` are convex and `L`-Lipschitz, differentiable a.e.

*Splitting.* Put `psi(t) = log g(t+h) - log g(t)` on `(a, b-h)`. Concavity
of `log g` makes `psi` nonincreasing (chord slopes of a concave function
decrease in both endpoints). Let

`J+ = {t in (a, b-h) : g(t+h) >= g(t)}`,  `J- = {t in (a+h, b) : g(t-h) > g(t)}`,
`E = (a,b) \ (J+ cup J-)`.

These are the traces of the Borel sets `{x : x, x + h e_j in int K, f(x+he_j) >= f(x)}`
and its backward analogue, so all integrals below are Fubini-measurable.
If `b - a <= h`, then `J+ = J- = empty` and `|E| <= h`. Otherwise `J+` is an
initial segment of `(a, b-h)`; let `tau in [a, b-h]` be its supremum (`tau = a`
if empty). Then `t - h notin J+` exactly when `t - h > tau` (up to the
endpoint), so `J-` is `(tau+h, b)` up to one point, and every `t in (a,b)`
with `t < tau` lies in `J+`. Hence `E subset [tau, tau+h]` and `|E| <= h`.

*Convexity defects.* For `u in {u_0, u_1}` and a.e. `t`, set
`delta+(t) = (u(t+h) - u(t))/h - u'(t)` on `J+` and
`delta-(t) = u'(t) - (u(t) - u(t-h))/h` on `J-`. Convexity gives
`0 <= delta+(t) <= u'(t+h) - u'(t) <= 2L` and
`0 <= delta-(t) <= u'(t) - u'(t-h) <= 2L`. With `phi = u' + L in [0, 2L]`
and `g(t) <= g(t+h)` on `J+`,

`int_{J+} delta+ g <= int_a^tau (phi(t+h) g(t+h) - phi(t) g(t)) dt
  = int_tau^{tau+h} phi g - int_a^{a+h} phi g <= 2 L Lambda h`

(signed-interval identity; `tau + h <= b`). With `phitilde = L - u' in [0, 2L]`,
`u'(t) - u'(t-h) = phitilde(t-h) - phitilde(t)`, and `g(t) < g(t-h)` on `J-`,

`int_{J-} delta- g <= int_{tau+h}^b (phitilde(t-h) g(t-h) - phitilde(t) g(t)) dt
  = int_tau^{tau+h} phitilde g - int_{b-h}^b phitilde g <= 2 L Lambda h`.

Since `delta^2 <= 2L delta`, each of the four defect integrals
`int_{J+} (delta+_{u_i})^2 g`, `int_{J-} (delta-_{u_i})^2 g` is `<= 4 L^2 Lambda h`.

*Difference quotients.* On `J+`, using `g(t) <= g(t+h)`,
`int_{J+} F(t+h)^2 g(t) dt <= int_{J+ + h} F^2 g`; on `J-`, using `g(t) < g(t-h)`,
`int_{J-} F(t-h)^2 g(t) dt <= int_{J- - h} F^2 g`. The sets `J+ + h subset (a+h, tau+h]`
and `J- - h subset [tau, b-h)` overlap at most in `[tau, tau+h]`, so the two
right sides sum to at most `2 int_a^b F^2 g`; and `J+`, `J-` are disjoint. Hence

`int_{J+} |D+F|^2 g + int_{J-} |D-F|^2 g <= (2/h^2) * 3 int_a^b F^2 g = 6 h^{-2} int_a^b F^2 g`.

*Assembly.* On `J+`, `F' = D+F - delta+_{u_0} + delta+_{u_1}`; on `J-`,
`F' = D-F + delta-_{u_0} - delta-_{u_1}`. By `(x+y+z)^2 <= 3(x^2+y^2+z^2)`,

`int_{J+ cup J-} |F'|^2 g <= 3 (6 h^{-2} int F^2 g + 4 * 4 L^2 Lambda h)
  = 18 h^{-2} int F^2 g + 48 L^2 Lambda h`.

On `E`, `|F'| <= 2L` and `|E| <= h` give at most `4 L^2 Lambda h`. This is (7.1).
Summing over `j`, and using that the coordinate partials form the full
gradient Lebesgue-a.e. in `int K` (pinned `gradient:interpolation`, last
paragraph) and F2, proves the lemma. ∎

No lower bound on `f` enters: the translation step that the pinned proof
pays with translation invariance of `dx` is paid here by choosing, slice by
slice, the difference direction in which the weight does not decrease.

## 8. Proof of Theorem LC

*(b) for finite targets.* With `w = W_2(mu,nu) > 0`, combine Proposition 6.1
and Lemma 7.1 with `h = w^{2/3}`:
`||T_mu - T_nu||^2 <= 18 d (1+sqrt162)^2 R^2 w^{2/3} + 52 L^2 Lambda P_K w^{2/3} = C_LC^2 w^{2/3}`.
If `w = 0`, the potentials agree `rho`-a.e. and letting `h -> 0` in Lemma 7.1
gives `T_mu = T_nu`.

*(a) and (b) in general.* Copy pinned `gradient:extension` and the proof of
`main:stability`: finite `eps_n`-nets and Borel nearest-point selections
`Q_n`, Cauchy property from the finite estimate, identification of the
`L^2(rho)` limit `S` as pushing `rho` to `lambda`, Arzelà–Ascoli for the
potentials, the restricted conjugate and Fenchel equality, and uniqueness
via a.e. coordinate differentiability. These steps use only `rho << dx` on
`K`, F2 (`rho`-null = Lebesgue-null in `K`), `K subset B(0,R)`, and the
finite estimate. Finally `W_2(mu_n, nu_n) <= W_2(mu,nu) + 2 eps_n` and
strong convergence give (b).

*(c).* The uniform measure on `[-1,1]^d` satisfies (H). Pinned
`sharpness:exponent` gives three-atom families in `Y = [-1,1]^d` with
`||T_mu - T_nu|| / W_2^alpha -> inf` for every `alpha > 1/3`. ∎

## 9. Validation performed

- Line-by-line re-derivation of every changed step (Sections 2–7) and of
  the numerical constants 162, 18, 48, 52.
- `experiments/check_slice.py` (pure Python, seed 20261016): 300 random
  trials of (7.1) with random convex Lipschitz pairs and random log-concave
  weights, several `h` per trial; maximal left/right ratio `0.0565`.
- `experiments/check_moment.py` (seed 16102026, 220x220 midpoint grid on
  `[-1,1]^2`): Proposition 5.1 ratio on restricted Gaussian, exponential
  and tent densities; maximal ratio `0.242` against the bound `162`.
  Several random draws were skipped by the script's own filters (small
  cell mass or vanishing denominator).
- These computations are evidence only and are not part of the proof.

## 10. Limits and novelty status

- The proof is an adaptation of the pinned argument. Its new operations
  are Lemma 4.1 (weighted Knothe domination with exact constant through
  log-concavity), Lemma 7.1 (direction-switching slice interpolation with
  no lower density bound), and the verification that the remaining steps
  survive weighting. Section 3 and Section 8 reuse pinned arguments with
  the stated substitutions rather than retyping them in full; a reviewer
  should check those substitutions against the pinned text.
- Not covered: densities only bounded above and below (Remark 4.2 shows
  the exact domination step characterizes log-concavity), log-concave
  sources with unbounded support, per-source sharpness, `d = 1`.
- Novelty: not found in the dated screen of `literature-screen.md`, where
  the best recorded exponent for log-concave compactly supported sources
  is `1/4`. Several items were read at abstract level only, so this is a
  new-to-this-project statement, not a demonstrated new-to-literature
  theorem.
