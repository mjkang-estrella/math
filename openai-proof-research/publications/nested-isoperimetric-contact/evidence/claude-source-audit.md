# Claude source audit: R017 + R018 nested ball/tube and ball/slab contact asymptotics

2026-10-13. Auditor: Claude Opus 5.5 (`claude-opus-5-5`), acting as the review sub-agent the user requested. **This is an AI audit, not human peer review.** It stipulates as true the pinned OpenAI theorem at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Every new deduction was re-derived independently. Earlier AI PASS verdicts (I269, I277) were treated as evidence, not as authority.

## Verdict

| Item | Verdict |
|---|---|
| R017 mathematics (ball–tube, `lim D_R/eps^2 = K(R)`) | **PASS** |
| R018 mathematics (ball–slab, `lim |log eps| L_R/eps^2 = 2pi`) | **PASS** |
| External AFM applicability (Def. 2.5, Thm. 4.2) | **PASS** (hypotheses verified against the exact final PDF) |
| Manuscript dependency and attribution statement | **REPAIR** (presentation only; items D1–D5 below) |

No substantive gap was found in either deduction. The REPAIR items concern how the combined manuscript should state its conditional dependence and cite the regularity input. None of them changes a theorem statement, a constant or a proof step.

## Sources and versions

- **Research pin:** `mjkang-estrella/math@d513e308d86a38004d78bab9b9e88532e92bf56c`, staged at `/tmp/publication-r017-r022`.
  - Manifest `manifest.json` SHA256 `2854605a…76ce7d`; its recorded revision equals the research pin.
- **Upstream (stipulated):** `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
  - Path: `preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/build/paper.tex`.
  - Freshly fetched via the pinned raw URL. SHA256 `ab75095f542adf4073a41a26a3c3ae97be7b55fa19674ec4fb4c288f7145a813`, identical to the hash recorded in I275.
  - Theorem `intro:main` (lines 56–84) was read in full.
  - Note: the path given in R017/R018 links omits `build/`. The tree URL still resolves, but raw links need `build/paper.tex`.
- **AFM:** E. Acerbi, N. Fusco, M. Morini, *Minimality via second variation for a nonlocal isoperimetric problem*, Comm. Math. Phys. 322(2) (2013) 515–557, doi:10.1007/s00220-013-1733-y, arXiv:1211.0164.
  - Author-hosted final PDF fetched fresh from `cvgmt.sns.it/media/doc/paper/540/Acerbi-Fusco-Morini.FINAL.pdf`. SHA256 `7805d5a0b9daf3873a199bbfe23d4064964fc2e72701be6d45303549028d4c72`, identical to the recorded hash.
  - Read: Definition 2.5 (p. 7), Theorem 4.2 (p. 22), the definition of `T^N` (pp. 5–6), and the use of Thm 4.2 for lamellar sets in the proof of Theorem 5.3 (pp. 27–28).
  - The bibliographic data come from a web search result, not from the publisher page.
- **Staged records read in full (SHA256 prefixes):**

  | Record | SHA256 prefix |
  |---|---|
  | R017 | `554e2deb` |
  | R018 | `470347ea` |
  | I263 report | `687450a3` |
  | I263 analysis | `d02db6df` (matches the recorded hash) |
  | I275 | `ab1a54ce` (matches) |
  | I253 | `ac6f099f` (statement and smoothing section) |
  | I269 review | `3564ac5d` |
  | I277 review | `6dc2a091` (matches the parent-recorded hash) |
  | I270 review | `ce568a8a` |
  | I278 review | `20eb28b8` (matches) |
  | I269 parent disposition | `9e91530a` |
  | I277 parent disposition | `58f8f47f` |
  | I278 parent disposition | `e90fa2e0` |

  The I269 and I277 analyses (`94133081`, `955b0ea8`) were consulted selectively, not reread line by line (see "Not inspected").
- **Exact checks:**
  - Script `tmp/checks/exact_checks.py` (`abe107db…`), with output `tmp/checks/exact_checks.out` (`b28411e9…`).
  - Run with SymPy/mpmath in a throwaway venv outside the repository.

## Upstream hypotheses actually needed, and their verification

Theorem `intro:main` gives the profile `min{(36pi)^{1/3}v^{2/3}, 2sqrt(pi v), 2}` with `v = min(V, 1-V)`. Its minimizers, up to an ambient isometry and a null set, are:

- balls for `V ≤ 4pi/81`, i.e. radius `≤ 1/3`;
- tubes about shortest closed geodesics for `4pi/81 ≤ V ≤ 1/pi`, i.e. radius in `[2/9, 1/pi]`;
- slabs of width `V` for `1/pi ≤ V ≤ 1/2`;
- complements of these above `1/2`.

The theorem also states "no further equality cases."

- **R017** needs:
  - inner volume `4piR^3/3` with `R < 1/pi < 1/3`, which is strictly on the ball branch;
  - outer volume `pi(R-eps)^2` with `R - eps ∈ (2/9, 1/pi)` for small `eps`, which is strictly on the tube branch.
- **R018** needs:
  - `R < 1/3`, which puts the inner volume on the ball branch;
  - outer volume `2(R-eps) → 2R ∈ (1/pi, 2/3)`, with `2/3 < 1 - 1/pi ≈ 0.682`. For `V > 1/2`, the complement has width `1 - V ∈ (1/3, 1/2)`, which also lies on the slab branch.
- The script checked strict branch membership near all four endpoints. Each scalar deficit is therefore nonnegative, and every L1 limit of a deficit-zero sequence is classified.
- The isometries used (a common translation plus a signed coordinate permutation) are ambient isometries of the cubic torus. ✔

## R017 audit (I263 + I253; I249 quadratic step re-derived)

1. **Existence and O(eps^2).**
   - Direct method: inclusion a.e. and both volumes pass to L1 limits. ✔
   - Ellipsoid `(r, r, R^3/r^2)`: volume exact, contained in the radius-`r` coaxial tube, longest semiaxis `→ R < 1/2`. Its sphere deficit is `O(eps^2)` and its tube deficit is 0. ✔
2. **Limit identification.**
   - Each deficit is nonnegative and their sum `→ 0`. Lower semicontinuity plus the classification give a ball `B_R` and a tube `C_R`.
   - The transverse projection of the ball is a radius-`R` disk inside the closed radius-`R` disk, so the centers coincide. ✔
3. **Lemma 1 (common two-volume flow).**
   - `X_1` is supported in a small ball about the north pole, inside the open set `C_R`. Hence `∫_{C_R} div X_1 = 0` and `∫_{B_R} div X_1 > 0`.
   - `X_2` is supported at height in `(R, 1/2)`, disjoint from `B_R`, with positive tube flux.
   - The volume map `s ↦ (∫_A det DΦ_s, ∫_B det DΦ_s)` is uniformly C² and its derivative is L1-continuous in `(A, B)`. The contraction argument gives `|s| ≤ Cq`.
   - `P(Φ_s H) ≤ (1 + C|s|) P(H)`, and inclusion is preserved because the same map is applied to both sets. ✔
4. **Lemma 2 (paired quasiminimality).**
   - All six pointwise states were checked for `E ⊂ F` and `H ∈ {0,1}`. This confirms `|(H∩F) Δ E| + |(H∪F) Δ F| = |H Δ E|`, and the analogous identity for `(E∩H, E∪H)` versus `|H Δ F|`.
   - The lattice inequality `P(A∩B) + P(A∪B) ≤ P(A) + P(B)` is standard.
   - Case `P(H) < P(E)` gives a bounded total perimeter, so Lemma 1 applies with uniform constants for `rho < rho_0`.
   - Large balls are handled by `omega ≥ M/rho_0^3`. This matches AFM Def. 2.5 exactly: "for **any** ball `B_r(x_0) ⊂ T^N` and any `F` with `E Δ F ⊂⊂ B_r(x_0)`, `P(E) ≤ P(F) + omega r^N`." ✔
5. **AFM Theorem 4.2.** Hypotheses as printed:
   - a sequence of omega-minimizers with a common omega;
   - `sup P < ∞`;
   - L1 convergence to a C² set in `T^N`, the unit-volume flat torus.

   All three are met separately for `E_n → B_R` and `F_n → C_R`. Tangency between the two limits is irrelevant because the theorem is scalar. The conclusion is a C^{1,1/2} global normal graph over the limit boundary, with `psi_h → 0` in C^{1,alpha}, so there are no extra components. ✔
6. **Expansions.** All four formulas were re-derived:
   - sphere volume `∫(psi + psi^2/R + psi^3/(3R^2)) dS = 0`;
   - tube volume `∫(eta + eta^2/(2r)) dS = 0`;
   - the two area densities;
   - after eliminating the linear terms, `Q_B = ∫|∇psi|^2 - 2psi^2/R^2` and `Q_{C,r} = ∫|∇eta|^2 - eta^2/r^2`. (The SymPy series of the sphere density is in the output.)

   The remainders are bounded by `(||psi||_∞ + ||∇psi||_∞^2) ||psi||_{H1}^2`. ✔
7. **Spectral gaps.**
   - Sphere: `(l(l+1) - 2)/R^2`, with `l = 0` removed (small mean) and `l = 1` removed by centering.
   - Tube: `(m^2 - 1)/r^2 + 4pi^2 k^2`, with `(0,0)` and `(±1,0)` removed. Mode `(0, k ≠ 0)` needs `r > 1/(2pi)`, which holds because `R > 2/9`.

   The ratio to the H1 eigenvalue is bounded below, giving `||·||_{H1} = O(eps)`. ✔
8. **Contact trace.**
   - With regular open representatives, `E ⊂ cl F` pointwise. The tube slice at `z = 0` is star-shaped about the axis, so `|y| ≤ r + eta(phi, 0)`.
   - Taking the dot product with `e_theta` gives exactly `eps + h·e_theta + psi ≤ eta∘phi`.
   - The half-circle L2 argument gives `|h| ≤ C eps`. Composition passes to the limit by density plus uniformly bounded composition operators. ✔
   - Adding the translation Jacobi field `d·omega` leaves the mean and the Q_B energy unchanged, because its Q_B pairing vanishes. ✔
9. **Quadratic minimum** (exactly verified):
   - Averaging over angle is valid because `Q(u) = Q(ū) + Q(u - ū)` and `u - ū` has mean zero.
   - For `u_A = A(1-2|t|)`, `Q_B/2 = 4piA^2`. The Legendre operator gives the same constant `2A` on both hemispheres, so `Q_B(u_A, h) = 0` for mean-zero `h` with zero trace.
   - The Green function `g_R` was checked: `-g'' - g/R^2 = -1` away from 0, derivative jump `-1`, `g'(±1/2) = 0`, mean 0, `B(g,g) = g(0) = G_R`.
   - The Fourier series `G_R = 2Σ_{k≥1} 1/((2pik)^2 - R^{-2})` matches numerically. For `R ∈ (2/9, 1/pi)` we have `1/(2R) ∈ (pi/2, 9/4)`, so `cot < 0` and `G_R > R^2 > 0` trivially.
   - The constrained minimum is `4piR/(R + 4G_R)`, attained at `A* = -R/(R+4G)` and `D* = 4G/(R+4G)` (SymPy). ✔
10. **Recovery (I253).**
    - Containment margin at latitude `tau`: `R(1 - sqrt(1-tau^2)) + eps[-1 + V(Rtau) - U(tau)sqrt(1-tau^2)] + O(eps^2)`. It is positive near the equator by `gamma` and positive away from it at zeroth order.
    - Boundary containment implies region containment: a point outside the tube on a horizontal slice can be moved radially until it exits the bounded inner region, which would produce a boundary point outside the open tube.
    - Volume corrections are `O(eps^2)`. The order of limits is `eps → 0`, then smoothing, then `gamma → 0`. ✔

## R018 audit (I275)

1. **Upper bound.**
   - Per patch: `(1/2) t^2 · 2pi/log(delta/a)`, with `log(delta/a) = ℓ/2 - log ℓ + O(1)` and `t = (1+eta) eps/2`. Four patches give `2pi(1+eta)^2 eps^2/ℓ` (SymPy).
   - C1 smallness: `t||∇chi||_∞ = O(sqrt(eps)/ℓ^2)`.
   - `∫psi^2` and the bump costs are `o(eps^2/ℓ)`. Flat faces have no linear area term.
   - The core margin requires only `2t > eps`. Outside the core, `|x|^2/(2R) ≥ eps ℓ^2/(8R) ≫ eps`.
   - Region containment follows from the extrema of compact vertical slices, and the outer slices are intervals. ✔
2. **Reduction.**
   - Identical mechanism to R017. The limit has the ball tangent to both faces and is therefore centered.
   - AFM applies to the slab. AFM itself applies Thm 4.2 to lamellar sets in the proof of its Theorem 5.3.
   - Slab face means are made exactly zero: `∫V^+ + ∫V^- = 0` by exact volume, and a reference shift `c` maps `(V^+, V^-) → (V^+ - c, V^- + c)`. ✔
   - Coercivity gives `O(eps/sqrt ℓ)`. ✔
3. **Exact chart identity.** `W = sqrt((R+p)^2 - |x|^2) - sqrt(R^2 - |x|^2) = p(2R+p)/[…]`, verified symbolically.
   - The two inclusion inequalities (3), including the sign of `h` on the lower face, were re-derived. ✔
4. **Localization (5)–(6).**
   - The high-mode estimate `∫k^2 ≤ R^2/((N+1)(N+2)) ∫|∇k|^2` and `Q_B(k) ≥ (1 - 2/((N+1)(N+2))) ∫|∇k|^2` are correct.
   - Low modes are finite-dimensional, so they are `o(eps)` uniformly.
   - The order of quantifiers (`delta`, `xi`, `N` fixed before `n → ∞`) is valid.
   - `|∇(V - W)|^2 ≤ 2(|∇V|^2 + |∇W|^2)` gives the factor 1/4. ✔
5. **Annular capacity.**
   - Jensen plus weighted Cauchy–Schwarz give `2pi(m(a) - m(b))^2/log(b/a)` with `log(b/a) = ℓ/2 + O(1)`.
   - The outer radius `b_n ∈ [delta, 2delta]` has `|m(b_n)| = o(eps)` from the L2 bound.
   - At `a = c sqrt(eps)`: `m ≥ (1 - c^2/(2R)) eps ± h - o(eps)`.
   - The inequality `(s+h)_+^2 + (s-h)_+^2 ≥ 2s^2` was checked by cases and by random test.
   - Total: `(1/4)·2·2pi·2 eps^2/ℓ = 2pi eps^2/ℓ` (SymPy). ✔

## Contribution boundaries

I agree with I270/I278 on the following:

- the classical ingredients are credited: the lattice inequality, AFM improved convergence, Jacobi spectra, Green functions, logarithmic droplet contact (Lacasse–Grest–Levine, Lv, Ginot et al., Morse–Witten), equal sharing and annular capacity;
- R018 Section 3 is inherited from R017;
- the increments are R017's paired reduction plus contact-trace limit, and R018's concentrating lower passage.

A bounded web screen on 2026-10-13 (two standard queries and one extended query) found no duplicate. One item may deserve a citation: Stredulinsky–Ziemer (arXiv math/9811046) on nesting of volume-constrained area minimizers in convex sets. It is relevant background to "separate minimizers cannot nest" but does not address the torus contact cost. I did not read it.

Worldwide priority is not established.

## REPAIR items for the manuscript's dependency statement (exact text proposals)

- **D1 (conditionality).** The cubic-torus theorem is an unrefereed, AI-generated preprint that the project stipulates as true. Both main theorems must be stated as conditional, following the house style of `complete-crouzeix-equality/main.tex`. Proposed wording:
  > **Assumption A.** The isoperimetric profile and equality classification of [OpenAI, Thm. `intro:main`] hold at the volumes `4πR³/3` and `π(R−ε)²` (respectively `2(R−ε)`) used below.

  Then: "Assume Assumption A. Then …"
  - Only the profile values and equality classes at these specific volumes are used. Nonnegativity of the deficits uses the profile inequality globally at those volumes.
  - Partial unconditional ranges (Milman's effective ball range up to 0.120582; AFM Thm 5.3 near half volume) do not cover the stated R-intervals and should not be claimed to do so without checking.
- **D2 (AFM provenance).** AFM Theorem 4.2 is stated **without proof** in AFM; they say it "is essentially contained in [3] (see also [41,46,49])", where [3] is Almgren's 1976 Memoir.
  - The manuscript should say this and cite the published CMP version with page and theorem label.
  - It may add a textbook improved-convergence source for (Λ, r_0)-minimizers. Note that Lemma 2 actually proves the stronger `P(E) ≤ P(H) + Λ|H Δ E|` for small balls, which is the standard (Λ, r_0) form. I did not verify a specific textbook theorem number, so the parent should check any number before citing it.
- **D3 (representatives).** State explicitly that the open regular representative bounded by the AFM graph is used, and that inclusion a.e. then implies `E ⊂ cl F` pointwise. I263 §7 states this. I275 §4 uses it only implicitly, and the R017/R018 summaries omit it.
- **D4 (link path).** Use `…/build/paper.tex` for raw source citations, together with the SHA256 above.
- **D5 (scope sentence).** Keep the existing exclusions: no endpoint uniformity, no Γ-limit, no regularity of arbitrary near-minimizers, no contact-set classification. Add one sentence: "The lower bounds hold for every admissible pair because exact minimizers exist and minimize; regularity is proved only for exact minimizers."

## Not inspected

- The proofs underlying AFM Thm 4.2 (Almgren / Tamanini type regularity), and the truth of the upstream theorem (stipulated).
- The I249 original note (only re-derived through I263 §8), I253 beyond its statement and smoothing section, and line-by-line reading of the I269/I277 reconstructions. My R017/R018 checks are an independent re-derivation from I263/I275, not a check of those reconstructions.
- The I270/I278 literature records and excerpts, beyond the reviews. Morse–Witten, Höhler–Weaire, ABLW Thm 4.5, Lacasse–Grest–Levine, Lv and Ginot et al. were not reread by me.
- Any manuscript draft: none existed in the package at audit time, and I did not edit any.
- No formal proof certificate exists. The numerical and SymPy checks verify constants and identities only, not the analysis.
