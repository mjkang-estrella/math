# Original scope (frozen before the proof attempt)

Author: Myeongjin Kang (no affiliation). Original prose CC BY 4.0.

Frozen at checkpoint 2 of `progress.md`, after reading the whole pinned
source family 374 and screening the primary literature listed in
`literature-screen.md`, and before writing any proof text. Later files may
report a proof, a counterexample, or an exact unpaid step for this target.
They may not narrow, widen, or re-quantify it. Any change of target would
need a new scope file and a parent decision.

## Source family

openai/math at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`,
`preprints/Sharp-One-Third-Stability-of-Brenier-Maps-September-25-2026/`
(catalogue entry 374). Theorem `main:stability` there is stated only for the
**uniform** source `rho = 1_K dx / |K|`. Its uniform-density hypothesis is
used in `moments:midpoint` (the measure domination
`Law((X+Z)/2) <= dx / sqrt(|U||V|)`), in the normalization step of
`moments:derivative`, and in the translation step of
`gradient:interpolation`.

## Frozen target (Theorem LC)

Hypotheses.

1. `d >= 2`. `K` is a compact convex subset of `R^d` with nonempty interior.
2. `rho = f dx` is a probability measure, where `f : R^d -> [0, infinity)` is
   Borel, `f = 0` outside `K`, `f > 0` on `int K`, and `log f` is concave on
   `int K`. (Equivalently: `rho` is a log-concave probability measure whose
   support is `K`. Values of `f` on `partial K` are irrelevant.) No lower
   bound on `f`, no smoothness of `f`, and no smoothness or strict convexity
   of `K` is assumed.
3. `Lambda = sup_{int K} f`. (Finite automatically; this is to be proved.)
4. `Y` is a nonempty compact subset of `R^d`; `R, L >= 1` satisfy
   `K subset B(0,R)` and `Y subset B(0,L)`.
5. `P_K = sum_j |proj_{e_j^perp} K|_{d-1}`.

Claims.

- (LC-a) For every `lambda` in `P(Y)` there is a unique (up to `rho`-null
  sets) quadratic optimal map `T_lambda` from `rho` to `lambda`.
- (LC-b) For all `mu, nu` in `P(Y)`,
  `||T_mu - T_nu||_{L^2(rho)} <= C_LC W_2(mu,nu)^{1/3}`, with the explicit
  constant
  `C_LC^2 = 18 d (1 + sqrt(162))^2 R^2 + 52 L^2 Lambda P_K`.
  The constant depends on `rho` only through `R`, `Lambda`, `P_K`; it does not
  depend on `inf f`, on atom counts, masses, separations, or target
  densities.
- (LC-c) The exponent `1/3` cannot be replaced by any larger exponent
  uniformly over this class (already for the uniform cube member, from the
  pinned `sharpness:exponent`).

Intermediate statements that the proof must pay (each with its own proof):

- (M) Weighted midpoint domination: for compact convex `U, V subset K` of
  positive volume there is a coupling `(X, Z)` of `rho|_U / rho(U)` and
  `rho|_V / rho(V)` with
  `sqrt(rho(U) rho(V)) Law((X+Z)/2) <= rho` as measures.
- (D) The moment estimate `moments:derivative` with the same constant 162
  for `rho` as above.
- (P) Linear potential stability for finite targets:
  `||u_0 - u_1||_{L^2(rho)} <= (1 + sqrt(162)) R W_2(mu, nu)`.
- (G) Weighted gradient interpolation without a lower density bound:
  `||grad(u_0 - u_1)||^2_{L^2(rho)} <= 18 d h^{-2} ||u_0 - u_1||^2_{L^2(rho)} + 52 L^2 Lambda P_K h`.

## Explicitly outside the frozen scope (not claimed)

- Source densities merely bounded above and below on a convex body (the
  Delalande–Mérigot class). The exact domination (M) characterizes
  log-concavity among continuous densities, so this class needs a different
  method; at most a method-boundary remark is in scope.
- Log-concave sources with unbounded support (for example the Gaussian).
- Sharpness of `1/3` for each fixed log-concave source other than the
  uniform cube; dimension `d = 1`.
- Any new-to-literature claim beyond the dated screen in
  `literature-screen.md`.

## Admissible outcomes

A complete proof of LC-a, LC-b, LC-c; or a counterexample to LC-b; or a
precise statement of the first unpaid step. No self-awarded PASS or count.
