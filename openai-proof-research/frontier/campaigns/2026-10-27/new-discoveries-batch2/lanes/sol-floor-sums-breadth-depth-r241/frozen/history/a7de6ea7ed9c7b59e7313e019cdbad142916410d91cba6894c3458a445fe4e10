# discovery.md — MathDB 325521 / Simon finite-order strict positivity of the Cauchy kernel

Lane: `lanes/pi-cauchy-strict-discovery-r1` (Pi GLM-5.3-Flash, thinking=high, solo, no children)

## Proposed outcome (ONE nomination)

**Theorem.** For every integer `n >= 2` and every `alpha in (0, 1/n)`, the Cauchy kernel
`K_alpha(t, x) = 1/(t^2 + 2 cos(pi alpha) t x + x^2)` on `(0, inf) x (0, inf)` is strictly
totally positive of order `n`: all minors `det[K_alpha(t_i, s_j)]_{i,j=1..m}`, `1 <= m <= n`,
with `0 < t_1 < ... < t_m`, `0 < s_1 < ... < s_m`, are strictly positive.

This resolves the finite-order positivity conjecture posed by Thomas Simon, "Total
positivity of a Cauchy kernel" (arXiv:1305.1173, 2013; J. Approx. Theory 234 (2018)
238-258, displayed Conjecture before Section 2), recorded open as **MathDB 325521**
("Finite-order strict total positivity conjecture for the Cauchy kernel"; status open,
no solutions/comments as of the 2026-10-27 snapshot in root-special-screen-r6).

Exact source quantifiers of the conjecture (MathDB 325521 statement): "For every `n >= 2`,
one has `alpha < 1/n => K_alpha in STP_n`." The preceding source theorem (1305.1173 (c))
establishes it only under `alpha <= 1/n AND 1/(n^2 - n - 6)_+`; the conjecture is the
optimal range. The companion paper (arXiv:1412.0132, Constr. Approx. 44 (2016) 103-120)
proves the **non-strict** `TP_n` classification `alpha in {1/2,...,1/n} or alpha < 1/n`
(Theorem 1, Corollary 1) and **explicitly leaves the strict `STP_n` case for `alpha < 1/n`
open** (Remark 2(b): "the fractional integration kernels I_beta are never STP_n").
Per the brief, the non-strict corollary does not exclude this target.

## Proof route (complete; see PROOF.md)

1. Gram representation: `K_alpha(e^{alpha x}, e^{alpha y}) = (pi e^{(1-alpha)(x+y)}/sin(pi alpha)) * int_R f_alpha(e^{x-u}) f_alpha(e^{y-u}) e^{-2u} du`,
   rederived self-containedly via the Mellin transform of the stable law (the identity
   `J_alpha(d) = sin(pi alpha)/(2 pi (cosh(alpha d) + cos(pi alpha)))` is the density of
   `log(Z_alpha/Z'_alpha)`); matches the formula displayed in the proof of Corollary 1 of
   1412.0132.
2. Andreief/Cauchy–Binet: the m×m determinant of `K_alpha` equals a positive constant times
   the integral of `D_x(u) D_y(u) e^{-2 sum u_j}` over the ordered chamber.
3. `D_x, D_y >= 0` on the chamber by Theorem 1 of 1412.0132 (`f_alpha(xy^{-1}) in TP_n`
   for `alpha < 1/n`), reparametrized.
4. `D_x, D_y` are real-analytic on the chamber (Zolotarev/Sato convergent series for
   `f_alpha`, valid for all `x > 0` when `0 < alpha < 1`) and not identically zero: as
   `U -> -inf`, `D_x(U + v_1, ..., U + v_m) ~ (prod_{k<=m} c_k) det[z_i^{alpha k+1}] det[w_j^{alpha k+1}] e^{(m + alpha m(m+1)/2) U} != 0`,
   with `c_k = (-1)^{k+1} Gamma(1+alpha k) sin(pi alpha k)/(pi k!) != 0` for `k <= m <= n`.
5. Nonnegative + analytic + not identically zero on a connected open set ⇒ the positive
   set is open dense; two open dense sets intersect; the chamber integral is therefore
   strictly positive ⇒ all minors strictly positive.

The `alpha = 0` case (`K_0 in STP_infty`, Borchardt) and the reciprocal cases
(`alpha = 1/k` strict) are already in the sources and are uncredited helpers here.

## Novelty / prior-art screen (bounded; dates 2026-10-28)

* **MathDB 325521**: status `open`, `solutions: []`, no comments/attachments (snapshot
  `post-325521.json` in root-special-screen-r6). Empty status is not treated as novelty
  evidence by itself.
* **Primary source bodies read**: arXiv:1305.1173 (v1 HTML, full: Theorem, Conjecture (2),
  Prop. 1, Section 5 partial results n=4,5, Conjectures 1–4, Section 6 Corollary) and
  arXiv:1412.0132v1 (full: Theorem 1, Corollary 1, §2.1 proof, §2.2 proof of Corollary 1
  incl. the displayed Gram formula, Remark 1, Remark 2(a),(b), Section 3). Cached in
  root-special-screen-r6 (`simon-cauchy.html`, `simon-stable.html`).
* **Citing papers** (Semantic Scholar API, 2026-10-28): of the JAT published version
  (DOI 10.1016/j.jat.2014.05.014, citationCount 7): 2608.28376 (critical points of
  line restrictions; unrelated), 2607.02828 (Weil quadratic form; unrelated), 2205.15742
  (bidiagonal decompositions; unrelated), 1412.0132, 1604.05267 (Bondesson–Simon,
  Stieltjes functions of finite order; unrelated), 1207.6464 (predates). Of 1412.0132:
  only 1604.05267. **No citing work resolves or attacks the strict conjecture.**
* **Author followups**: Simon's full publication list (univ-lille page, retrieved 2026-10-28)
  shows no total-positivity paper after #40 (Constr. Approx. 2016). No retraction or
  resolution of the conjecture.
* **Published JAT version**: publisher page (doi.org → ScienceDirect) still displays the
  Conjecture with the same quantifiers (snippet-level evidence; full paywalled body not
  read — access limit recorded in provenance.json).
* **Generic-mechanism screen**: 2006.16213 (Belton–Guillot–Khare–Putinar, preservers of
  TP kernels) — preserver classifications, not applicable. 2607.02778 (strict TP via
  spectral Darboux / Toeplitz smoothing; Bessel kernel + PF sequences) — does not cover
  Cauchy/stable kernels. 2606.31647 (Hankel determinants, order-moment transport) — not
  applicable. Karlin's basic composition formula strict variants require STP factors;
  1412.0132 Remark 2(b) itself states the factorization route cannot yield strictness.
  The strictification lemma used here (TP factors + analyticity + non-degeneracy) was
  not located in Karlin (1968) or Pinkus (2010) in this form (book bodies not directly
  accessible — access limit noted); even if a cousin exists, the application to `K_alpha`
  (Sections 5–6 of PROOF.md) is the substantive content and is not a routine corollary.
* **Prior first-batch outcomes** (prior-campaign-context.json, 30 accepted): none touches
  Cauchy/stable kernels or strict TP of Gram-type kernels.

**No worldwide-priority claim is made.** If a public exact proof surfaces, this outcome is
excluded per campaign rules.

## Substantive screen (is it routine?)

Checked whether a standard Karlin strict-composition/analytic PF theorem supplies the
upgrade as a black box. Conclusion: no. The kernel factors in the Gram representation are
merely `TP_n` (never `STP_n`, per the source itself), so Karlin's strict basic composition
formula does not apply; the non-degeneracy must be discharged analytically, which is
exactly Lemmas 3.1 and 5.1. The result is therefore not a helper, parameter instance, or
routine corollary.

## Credit recommendation

`credit: 1` if the campaign's substantive/review gates accept it: a complete ordinary proof
of an open, explicitly conjectured statement (MathDB 325521), with exact source quantifiers
and no prior public resolution found. No formal Lean PASS is claimed from this lane (see
SUMMARY.md); the formal endpoint remains a root-level requirement.
