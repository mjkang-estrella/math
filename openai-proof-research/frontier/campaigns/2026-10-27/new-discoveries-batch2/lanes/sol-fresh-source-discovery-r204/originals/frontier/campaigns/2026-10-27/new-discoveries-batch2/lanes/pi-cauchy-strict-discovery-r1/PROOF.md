# PROOF — Strict total positivity of the Cauchy kernel `K_alpha` for `alpha < 1/n`

**Outcome.** For every integer `n >= 2` and every `alpha` with `0 < alpha < 1/n`, the kernel

```
K_alpha(t, x) = 1 / (t^2 + 2 cos(pi alpha) t x + x^2),      t, x > 0,
```

is strictly totally positive of order `n` (`STP_n`): for every `1 <= m <= n`, every
`0 < t_1 < ... < t_m` and every `0 < s_1 < ... < s_m`,

```
det[ K_alpha(t_i, s_j) ]_{i,j=1..m} > 0.
```

Together with the classical strict cases `alpha = 0` (`K_0` is `STP_infty`, Borchardt; see
Simon 1305.1173, Prop. 1) and `alpha in {1/2, 1/3, ..., 1/n}` (strictness on the reciprocal
set, Simon 1305.1173 Prop. 2.1 / 1412.0132 Remark 2(b)), this resolves the finite-order
positivity conjecture of Simon (arXiv:1305.1173, displayed Conjecture (2); MathDB 325521)
in the full range `alpha in [0, 1/n)`.

---

## 0. Notation and standing hypotheses

Throughout, `n >= 2` and `alpha in (0, 1)` with `alpha < 1/n` are fixed. `Z_alpha` is the
positive alpha-stable random variable with Laplace transform `E[e^{-lambda Z_alpha}] = e^{-lambda^alpha}`,
and `f_alpha` its density on `(0, inf)`, `f_alpha(x) = p_alpha(1, x)` (notation of Simon,
arXiv:1412.0132). For `u = (u_1, ..., u_m)` write `D_x(u) = det[ f_alpha(e^{x_i - u_j}) ]_{i,j}`
and `Omega_m = { u in R^m : u_1 < ... < u_m }` (the open ordered chamber, connected).

## 1. Input A (source): `f_alpha(xy^{-1})` is `TP_n` for `alpha < 1/n`

**Theorem A** (Simon, *Total positivity in stable semigroups*, Theorem 1; arXiv:1412.0132,
published Constr. Approx. 44 (2016) 103-120). *For every `n >= 2`: `p_alpha(t,x)` is `TP_n`
on `(0,inf)^2` iff `alpha in {1/2, ..., 1/n}` or `alpha < 1/n`.*

By the self-similarity `p_alpha(t, x) = t^{-1/alpha} f_alpha(x t^{-1/alpha})` and Karlin's
Theorem 1.2.1 (row/column rescaling by positive functions), `p_alpha` is `TP_n` iff the
multiplicative-convolution kernel `f_alpha(x y^{-1})` on `(0,inf)^2` is `TP_n` (this
reduction is carried out in the proof of Corollary 1 of 1412.0132). Hence:

**Corollary A.** For `alpha < 1/n`, the kernel `A(x, u) := f_alpha(e^{x - u})` on `R x R`
is `TP_n`: for every `1 <= m <= n`, `x_1 < ... < x_m` and `u_1 < ... < u_m`,
`det[ f_alpha(e^{x_i - u_j}) ] >= 0`.

*Proof.* Apply Theorem A (via the reduction above) with `X_i = e^{x_i}`, `Y_j = e^{u_j}`,
both increasing. ∎

## 2. Input B (classical): the convergent series for `f_alpha`

**Theorem B** (Zolotarev; Sato, *Lévy processes and infinitely divisible distributions*,
(14.30)-(14.31); see also 1412.0132 §1, "convergent series representation given e.g. by
(14.30) and (14.31) in [Sato]"). *For `0 < alpha < 1` and every `x > 0`,*

```
f_alpha(x) = (1/pi) * sum_{k>=1} (-1)^{k+1} Gamma(1 + alpha k) sin(pi alpha k)/k! * x^{-alpha k - 1},
```

*the series converging absolutely, locally uniformly on `(0, inf)`.*

*Verification of local uniform convergence.* On a compact `[a, b] ⊂ (0, inf)` the k-th
term is bounded by `Gamma(1+alpha k)/k! a^{-alpha k - 1}`, and the ratio of successive
terms is `~ alpha^alpha a^{-alpha} k^{alpha-1} -> 0`; hence the majorant series converges.
Numerically the formula was validated against the closed form at `alpha = 1/2`
(`f_{1/2}(x) = x^{-3/2} e^{-1/(4x)}/(2 sqrt(pi))`) and against a numerical
inverse-Laplace evaluation of `e^{-lambda^alpha}` for `alpha in {0.3, 0.55, 0.7, 0.9}`
(scripts/check_fast.py and scripts/falpha.py; agreement to ~1e-40 in the well-conditioned
regime). ∎

**Consequences.**
1. `f_alpha` is real-analytic on `(0, inf)` (locally uniform limit of real-analytic functions).
2. The coefficients `c_k := (-1)^{k+1} Gamma(1 + alpha k) sin(pi alpha k)/(pi k!)` satisfy
   `c_k != 0` for `1 <= k <= n`, because `0 < alpha k <= alpha n < 1` gives `0 < alpha k < 1`,
   so `sin(pi alpha k) != 0`.

## 3. The convolution identity (Gram representation of `K_alpha`)

**Lemma 3.1.** *For all `x, y in R`,*

```
int_R f_alpha(e^{x-u}) f_alpha(e^{y-u}) e^{-2u} du = e^{-(x+y)} J_alpha(x - y),
```

*where `J_alpha(d) := int_0^inf v f_alpha(e^{d/2} v) f_alpha(e^{-d/2} v) dv` is the density
of `log(Z_alpha / Z'_alpha)` (`Z'` an independent copy), and*

```
J_alpha(d) = sin(pi alpha) / ( 2 pi ( cosh(alpha d) + cos(pi alpha) ) ).
```

*Proof.* Substitute `u = (x+y)/2 + w` and then `v = e^{-w}` (with `dw = -dv/v`,
`e^{-2w} = v^2`):

```
int_R f(e^{x-u}) f(e^{y-u}) e^{-2u} du
  = e^{-(x+y)} int_R f(e^{(x-y)/2 - w}) f(e^{(y-x)/2 - w}) e^{-2w} dw
  = e^{-(x+y)} int_0^inf f(e^{(x-y)/2} v) f(e^{-(x-y)/2} v) v dv
  = e^{-(x+y)} J_alpha(x-y).
```

Let `h(s) := e^s f_alpha(e^s)`, the density of `log Z_alpha`. With `v = e^s` in `J_alpha`,

```
J_alpha(d) = int_R e^{2s} f(e^{s + d/2}) f(e^{s - d/2}) ds
           = int_R h(s + d/2) h(s - d/2) ds                        [since e^{2s} = e^{s+d/2} e^{s-d/2}]
           = int_R h(t) h(t - d) dt        (t = s + d/2)
           = (h * h~)(d),                  h~(t) := h(-t).
```

So `J_alpha` is the density of `log Z_alpha - log Z'_alpha` and is continuous and in `L^1`.
Its Fourier transform is

```
J^_alpha(xi) = h^(xi) h~^(xi) = |h^(xi)|^2 = |E[Z_alpha^{i xi}]|^2.
```

The Mellin transform of the positive stable law (1412.0132, displayed in the proof of
Lemma 1: `E[Z_alpha^{-i alpha s}] = Gamma(1 + i s)/Gamma(1 + i alpha s)`, i.e. with
`xi = -alpha s`, `E[Z_alpha^{i xi}] = Gamma(1 - i xi/alpha)/Gamma(1 - i xi)`) and the
classical `|Gamma(1 + iu)|^2 = pi u / sinh(pi u)` for `u > 0` give

```
|h^(xi)|^2 = (pi (xi/alpha)/sinh(pi xi/alpha)) / (pi xi/sinh(pi xi))
           = sinh(pi xi) / (alpha sinh(pi xi/alpha)).
```

On the other hand, Simon (1305.1173, proof of Prop. 2) computes the characteristic function
of `g_alpha(x) = sin(pi alpha)/(2 pi alpha (cosh x + cos(pi alpha)))` as
`int e^{isx} g_alpha(x) dx = sinh(pi alpha s)/(alpha sinh(pi s))`. Hence the function
`d -> alpha g_alpha(alpha d) = sin(pi alpha)/(2 pi (cosh(alpha d) + cos(pi alpha)))` has
Fourier transform `xi -> (1/1) * sinh(pi xi/alpha * alpha)/(alpha sinh(pi xi/alpha)) = sinh(pi xi)/(alpha sinh(pi xi/alpha))`,
identical to `J^_alpha`. Both functions are continuous and in `L^1`, so by uniqueness of
the Fourier transform on `L^1` they coincide everywhere. ∎

*Remark.* A tempting derivation of `J_alpha` by inserting the series of Theorem B and
integrating termwise is **invalid**: `sum_k |c_k| int_0^1 v^{-alpha k} dv` diverges for
`k >= 1/alpha`. The Mellin/Fourier route above is the correct one (this trap was
encountered and documented during the work; see progress.md).

**Lemma 3.2 (Gram representation).** *For `1 <= m`, `0 < x_1 < ... < x_m`, `0 < y_1 < ... < y_m` (reals),*

```
det[ K_alpha(e^{alpha x_i}, e^{alpha y_j}) ]_{i,j=1..m}
  = (pi/sin(pi alpha))^m * e^{(1-alpha) m (sum_i x_i + sum_j y_j)} * (1/m!)
    * int_{R^m} D_x(u) D_y(u) prod_{j=1}^m e^{-2 u_j} du,
```

*with `D_x(u) = det[ f_alpha(e^{x_i - u_j}) ]_{i,j=1..m}` and `D_y` analogously.*

*Proof.* By Lemma 3.1 and the algebra check

```
K_alpha(e^{alpha x}, e^{alpha y})
  = e^{-alpha(x+y)} / (2 cosh(alpha(x-y)) + 2 cos(pi alpha))
  = (pi e^{(1-alpha)(x+y)} / sin(pi alpha)) * int_R f(e^{x-u}) f(e^{y-u}) e^{-2u} du,
```

(so each matrix entry is a positive constant times `int phi_{x_i}(u) psi_{y_j}(u) dmu(u)`
with `phi_x(u) = f_alpha(e^{x-u})`, `dmu(u) = e^{-2u} du`). Applying Andreief's identity
(the continuous Cauchy-Binet formula; its discrete form was verified numerically to 1e-12
in scripts/check_final.py, Check B)

```
det[ int phi_i psi_j dmu ]_{i,j} = (1/m!) int_{R^m} det[phi_i(u_j)] det[psi_i(u_j)] prod_j dmu(u_j)
```

(valid since `int |phi_i psi_j| dmu < inf`: the integrand decays like `e^{alpha u}` at
`-inf` and like `e^{(alpha-1)u}` at `+inf`) and multiplying the constants per row/column
gives the claim. ∎

## 4. Strictification lemma

**Lemma 4.1.** *Let `A` be a real kernel on `X x R` and fix `m >= 1`. Assume*

* (H1) *for every increasing `x_1 < ... < x_m` in `X` and `u_1 < ... < u_m` in `R`,
  `D_x(u) := det[A(x_i, u_j)]_{i,j} >= 0` on `Omega_m`;*
* (H2) *`u -> A(x, u)` is real-analytic on `R` for every `x` in `X` (hence `D_x` is
  real-analytic on the connected open set `Omega_m`);*
* (H3) *for every increasing `x`-tuple, `D_x` is not identically zero on `Omega_m`.*

*Then for every increasing `x`- and `y`-tuples, the set `{u in Omega_m : D_x(u) > 0 and D_y(u) > 0}`
is nonempty and open; in particular any measure of the form `D_x(u) D_y(u) w(u) du` with
`w > 0` continuous has a strictly positive integral over `Omega_m`.*

*Proof.* By (H1) `D_x >= 0` and by (H3) `D_x` is not `≡ 0`; hence `{D_x > 0}` is nonempty
(some point has `D_x != 0`, and there it is `> 0`) and open (continuity). It is dense: if
`D_x = 0` on some nonempty open subset of `Omega_m`, the identity theorem for real-analytic
functions on the connected open set `Omega_m` would force `D_x ≡ 0`, contradicting (H3).
The same holds for `D_y`. The intersection of two open dense subsets of `Omega_m` is open
dense, in particular nonempty; on it the integrand `D_x D_y w` is strictly positive, and it
is nonnegative everywhere on `Omega_m` by (H1). A nonnegative measurable function that is
strictly positive on a set of positive measure has a strictly positive integral. ∎

*Remark.* We did not locate this statement in Karlin (1968) or Pinkus (2010) in this form;
Karlin's basic composition formula and its strict variants require the factors to be
*strictly* totally positive, which the fractional-integration factors here never are
(1412.0132, Remark 1 and Remark 2(b): `I_beta` is never `STP_n`). Lemma 4.1 replaces
strictness of the factors by analyticity plus non-degeneracy, which is what the stable
kernel can supply. Even if a cousin of Lemma 4.1 exists in the literature, the outcome
below rests on the *application* (Sections 5-6), which is new.

## 5. Non-degeneracy: `D_x` is not identically zero on the chamber

**Lemma 5.1.** *Let `0 < alpha < 1` with `alpha m < 1` (`m <= n`), let `x_1, ..., x_m` be
pairwise distinct reals and `v_j := j` (any fixed strictly increasing `v_j`). Then with
`z_i := e^{-x_i}`, `w_j := e^{v_j}`, `c_k` as in Section 2,*

```
D_x(U + v_1, ..., U + v_m) = ( prod_{k=1}^m c_k ) * det[ z_i^{alpha k + 1} ]_{i,k=1..m}
                             * det[ w_j^{alpha k + 1} ]_{j,k=1..m}
                             * e^{(m + alpha m(m+1)/2) U} * (1 + o(1))     as U -> -inf.
```

*In particular `D_x` is not identically zero on `Omega_m`.*

*Proof.* By Theorem B, for every `i, j` (with the series absolutely convergent for every
value of the argument, uniformly in `i, j` for `U <= U_0` because `e^{x_i - U - v_j} >=
e^{x_i - U_0 - v_j}` bounds the terms from above when `U <= U_0`):

```
f_alpha(e^{x_i - U - v_j}) = sum_{k>=1} c_k e^{-(alpha k + 1)(x_i - U - v_j)}
                           = sum_{k>=1} c_k e^{(alpha k + 1) U} r_k(i) c'_k(j),
r_k(i) := e^{-(alpha k + 1) x_i} = z_i^{alpha k + 1},   c'_k(j) := e^{(alpha k + 1) v_j} = w_j^{alpha k + 1}.
```

Expanding the determinant multilinearly over the columns (justified by the absolute
convergence above, which dominates the expansion; note `|r_k(i)| <= C` for fixed tuples and
`sum_k |c_k| e^{(alpha k + 1) v_j} < inf` for each `j`):

```
D_x(U + v) = sum_{(k_1,...,k_m) in (N_*)^m} ( prod_j c_{k_j} e^{(alpha k_j + 1)(U + v_j)} )
             * det[ z_i^{alpha k_j + 1} ]_{i,j=1..m}.
```

The determinant factor vanishes unless `k_1, ..., k_m` are pairwise distinct (two equal
indices give two equal columns). For pairwise distinct `(k_j)`, the exponent of `e^U` is
`sum_j (alpha k_j + 1) = m + alpha sum_j k_j >= m + alpha m(m+1)/2`, with equality exactly
for `{k_1, ..., k_m} = {1, ..., m}`. Every other tuple is suppressed by an additional
factor `<= e^{alpha U}` (and `prod_j |c_{k_j}| e^{(alpha k_j+1) v_j} sum_k |c_k| e^{(alpha k+1)v_j}`
times `m! C^m` bounds the infinitely many remaining terms, using `e^{(alpha k+1)U} <= 1`
for `U <= 0`). Hence, extracting the leading layer and summing the `m!` permutations of
`{1, ..., m}` by the (finite) Cauchy-Binet formula,

```
D_x(U + v) = e^{(m + alpha m(m+1)/2) U} * [ (prod_{k=1}^m c_k) * det(R) det(C) + o(1) ],
R = [ z_i^{alpha k + 1} ]_{i,k=1..m},   C = [ w_j^{alpha k + 1} ]_{j,k=1..m}.
```

Both determinants are nonzero: `det[z_i^{alpha k + 1}]_{k=1..m} = (prod_i z_i) * det[(z_i^alpha)^{k-1}]_{k}`
is `prod_i z_i` times the ordinary Vandermonde determinant of the `m` distinct positive
numbers `z_i^alpha`, i.e. `prod_i z_i * prod_{i<j} (z_j^alpha - z_i^alpha) != 0`; likewise
for `C`. Finally `prod_{k=1}^m c_k != 0` by Section 2(2). So the leading coefficient is
nonzero and `D_x(U + v_1, ..., U + v_m) != 0` for all `U` sufficiently negative. ∎

*(The ratio `D_x/(leading)` was verified numerically to converge to 1 for
`(m, alpha) = (2, 0.45), (3, 0.3), (4, 0.2), (5, 0.15), (6, 0.15)` at `U in {-15, -25, -35}`;
scripts/check_fast.py, Check C.)*

## 6. Conclusion

Fix `1 <= m <= n`, `0 < t_1 < ... < t_m`, `0 < s_1 < ... < s_m`. Write `t_i = e^{alpha x_i}`,
`s_j = e^{alpha y_j}` with `x_i = ln(t_i)/alpha`, `y_j = ln(s_j)/alpha` (all distinct and
increasing). By Lemma 3.2,

```
det[ K_alpha(t_i, s_j) ] = P * (1/m!) * int_{R^m} D_x(u) D_y(u) prod_j e^{-2u_j} du,
P := (pi/sin(pi alpha))^m * e^{(1-alpha) m (sum x_i + sum y_j)} > 0.
```

The integrand `D_x D_y prod e^{-2u_j}` is symmetric under coordinate permutations (both
determinants are antisymmetric, the weight symmetric), so the integral over `R^m` equals
`m!` times the integral over the chamber `Omega_m`:

```
det[ K_alpha(t_i, s_j) ] = P * int_{Omega_m} D_x(u) D_y(u) prod_j e^{-2u_j} du.
```

- By Corollary A (Input A), `D_x >= 0` and `D_y >= 0` on `Omega_m` (H1 of Lemma 4.1).
- By Theorem B(1), the entries `f_alpha(e^{x_i - u_j})` are real-analytic in `u`
  (H2); hence so are `D_x`, `D_y`.
- By Lemma 5.1 (which needs only `alpha m < 1`, true since `m <= n`), `D_x` and `D_y` are
  not identically zero on `Omega_m` (H3).

Lemma 4.1 (applied to both determinants) yields a nonempty open set in `Omega_m` on which
`D_x D_y > 0`; the weight `prod e^{-2u_j}` is strictly positive everywhere. Therefore the
chamber integral is strictly positive, and

```
det[ K_alpha(t_i, s_j) ] > 0.
```

For `m = 1` the claim is `K_alpha(t, s) > 0`, evident. Since `m <= n` and the tuples were
arbitrary, `K_alpha in STP_n`. ∎∎

## 7. Boundary of the statement (honest scope)

* `alpha = 0`: `K_0(t,x) = (t+x)^{-2} in STP_infty` (Borchardt / Simon 1305.1173 Prop. 1).
  Not reproved here; already known, uncredited.
* `alpha in {1/2, 1/3, ...}` with `alpha >= 1/n`: strictness on the reciprocal set is known
  (1305.1173 Prop. 2.1; 1412.0132 Remark 2(b)). Not claimed here.
* `alpha > 1/n` (outside the reciprocal set): `K_alpha` is not even `TP_n` (1305.1173
  Theorem (b)); consistent with the sharpness seen numerically (check_fast.py Check 3).
* **Not claimed:** Conjecture 4 of 1305.1173 (`p_alpha in STP_n` for `alpha < 1/n`). The
  Gram/Andreief mechanism is specific to `K_alpha`; no integral representation with a
  nonnegative integrand is available for `p_alpha`, and the method does not transfer.

## 8. Dependence inventory (for formalization)

| # | Item | Status |
|---|------|--------|
| 1 | Andreief / Cauchy–Binet identity | classical; provable in Lean from scratch |
| 2 | Real-analytic zero sets (identity theorem on connected open sets) | standard; Lean-provable (heavy) |
| 3 | Ordinary Vandermonde nonvanishing for distinct positive bases | in mathlib (`Matrix.vandermonde`) |
| 4 | **Theorem A**: `f_alpha(xy^{-1}) in TP_n` for `alpha < 1/n` | **external source** (Simon, Constr. Approx. 2016); NOT in mathlib; proof uses local limit theorem + Karlin Thm 3.2.1 |
| 5 | **Theorem B**: Zolotarev/Sato convergent series for `f_alpha` | **external source**; NOT in mathlib |
| 6 | Mellin transform `E[Z^{i xi}]`, `|Gamma(1+iu)|^2` | external special-function facts (Sato/Gamma) |
| 7 | Fubini/Tonelli over `R^m`, Fourier uniqueness on `L^1` | mathlib-adjacent, substantial |

A literal Lean endpoint therefore cannot rest on mathlib alone; items 4-6 must be proved
from scratch (no `sorry`/`axiom`). See SUMMARY.md for the resulting honest Lean status.
