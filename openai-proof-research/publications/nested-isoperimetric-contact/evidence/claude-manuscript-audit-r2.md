# Claude manuscript audit r2: "Sharp ball–tube and ball–slab nesting costs in the cubic three-torus"

2026-10-13. Auditor: Claude Opus 5.5 (`claude-opus-5-5`), review sub-agent requested by the user, routed through the configured Factory provider. **This is an AI audit, not human peer review.** The pinned OpenAI theorem at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` is stipulated true; only its exact statement was checked. Every new deduction in the manuscript was re-derived independently. The earlier source audit (`evidence/claude-source-audit.md`, PASS) and the prior AI reviews (I269, I277, I270, I278) were treated as evidence, not authority. The earlier r1 manuscript audit produced no verdict and was not used.

## Verdict

| Item | Verdict |
|---|---|
| Theorem 1.2 (ball–tube, `lim D_R/eps^2 = K(R)`) as written in `main.tex` | **PASS** |
| Theorem 1.3 (ball–slab, `lim abs(log eps) L_R/eps^2 = 2pi`) as written | **PASS** |
| Use of the upstream assumption (Assumption 1.1) and AFM Definition 2.5 / Theorem 4.2 | **PASS** |
| Manuscript as a publication (precision, notation, contribution boundary) | **REPAIR** (minor; items M1–M7 below) |

No mathematical gap was found in any step. The REPAIR items are a quantifier tightening in Lemma 2.2 (M1), a slightly imprecise inequality phrase (M2), notation collisions (M3–M5), and missing related-work citations for the contribution boundary (M6–M7). None of them changes a theorem statement, a constant, or the structure of a proof. There is no BLOCK item.

## Exact artifacts reviewed

| Artifact | SHA256 |
|---|---|
| `main.tex` (562 lines, mtime 2026-10-13 12:04:47 -0700) | `556b7e763c07af0aca130d9d00c95805c2f951f5dbba091261385bafc2d4b284` |
| `tmp/main.pdf` (7 pages, CreationDate Tue Oct 13 12:04:47 2026 PDT) | `e066907cab5b7aba42c524597e447e91cb0d8b91f4856b29dd2884affb546469` |
| Upstream `paper.tex` (re-fetched from the pinned raw URL into `tmp/audit-r2/upstream-refetch.tex`) | `ab75095f542adf4073a41a26a3c3ae97be7b55fa19674ec4fb4c288f7145a813`, identical to `tmp/upstream.tex` and `tmp/src/354-paper.tex` |
| AFM final PDF `tmp/src/afm/afm.pdf` | `7805d5a0b9daf3873a199bbfe23d4064964fc2e72701be6d45303549028d4c72` |
| Prior source audit `evidence/claude-source-audit.md` | `458809b603392d8617eb319f44000ffc65a5e3eb8768745e00cbe6b568522cfa` |
| Staged research manifest `/tmp/publication-r017-r022/manifest.json` (revision `d513e308d86a38004d78bab9b9e88532e92bf56c`) | `2854605ad816ee3a4a327833a55bcda06f47cbb7c269030445ffc1563576ce7d` |
| New check script `tmp/audit-r2/checks_r2.py` | `8110349308746469019ef7c2b335532346db8fb7e021a15df153703ef3604ad6` |
| Its output `tmp/audit-r2/checks_r2.out` (47 PASS, 0 FAIL) | `9a449acc4abad7f5fa0efcc957a9a7c43744ac42c166e4cc131b5a82b3d44718` |

**PDF/source correspondence.** A copy of `main.tex` was rebuilt in `tmp/audit-r2/` with the assigned Tectonic binary (`publications/rooted-matching-entropy/tmp/tools/tectonic`). The rebuild has no warnings, undefined references, or overfull boxes. Its PDF hash differs (`aff9fbce…`) only because of embedded timestamps: the `pdftotext -layout` extractions of the reviewed and rebuilt PDFs are byte-identical. All seven pages of `tmp/main.pdf` were read as text. Pages 1 and 6 were also inspected as images, with no rendering defects. The manuscript itself was not edited.

## Upstream statement and branch membership (Assumption 1.1)

The pinned Theorem `intro:main` (Theorem 1.1 of the upstream paper; source lines 56–84) was read in full. Assumption 1.1 restates it faithfully:

- the profile `min{(36pi)^{1/3} v^{2/3}, 2 sqrt(pi v), 2}`;
- balls, tubes about shortest closed geodesics, and coordinate slabs on the open ranges;
- both adjacent types at the transitions and slabs at `V = 1/2`;
- complements above half volume;
- "up to isometry and null sets", matching "up to an ambient isometry and a null set".

The bibliography entry cites the correct pinned `build/paper.tex` path, the date, and the label "Theorem 1.1", so the D4 repair from the source audit is done.

Branch membership was checked exactly (`checks_r2.out`, first block):

- **Tube problem.** `R < 1/pi < 1/3` puts the ball strictly on the ball branch. `R - eps ∈ (2/9, 1/pi)` puts the outer set strictly on the tube branch. The (0,k) Jacobi modes need `r > 1/(2pi)`, which holds because `2/9 > 1/(2pi)`.
- **Slab problem.** `R < 1/3` puts the ball on the ball branch. The outer volume `2(R - eps) → 2R ∈ (1/pi, 2/3)`, and `2/3 < 1 - 1/pi`. Above `1/2`, the complement width lies in `(1/3, 1/2)` and is still on the slab branch.
- **Embedding.** All radii are below `1/2`, so the balls and tubes are embedded.

**Endpoints.** The open radius ranges are necessary, and the manuscript does not claim more ("No endpoint-uniform estimate is asserted").

- **Slab, R = 1/3.** The theorem fails at this endpoint. At inner volume `4pi/81`, Assumption 1.1 also allows a radius-2/9 tube. That tube fits inside a coordinate slab of width `2/3 - 2eps` with no contact, and it has perimeter `4pi/9 = 4piR^2`. Hence `L_{1/3}(eps) = 0` for small `eps`. Excluding `R = 1/3` is therefore essential.
- **Tube, R = 2/9 and slab, R = 1/(2pi).** At these endpoints the outer volume leaves the stated branch for `eps > 0`, so the problem changes.
- **Tube, R = 1/pi.** Not claimed. (A ball of diameter `2/pi` cannot fit in a slab of width `1/pi`, so an extension may be possible, but it was not checked and is not asserted.)

## Line-by-line audit of the deductions

Line numbers refer to `main.tex`.

### Problem definitions and theorems (L43–103)

- The defining infima (1.1) and (1.2) use the correct reference perimeters:
  - `4piR^2` for the ball;
  - `2pi(R - eps)` for the tube in the unit torus (axis length 1);
  - `2` for the slab.
- Theorem 1.2:
  - `G_R = g_R(0) = R^2 - (R/2) cot(1/(2R))`;
  - since `1/(2R) ∈ (pi/2, 9/4) ⊂ (pi/2, pi)`, we have `cot < 0`, so `G_R > R^2 > 0`;
  - consequently `K(R) > 0`. ✔
- The statements say "the infima run over finite-perimeter pairs" with a.e. inclusion, and the proofs use only that. ✔

### Lemma 2.1, common two-volume flow (L113–138)

- **Field choices.**
  - For the tube, `X_1` is supported near the north pole of `∂B_R`, inside the open `C_R`. `X_2` lies on `∂C_R` at axial heights in `(R, 1 - R)`, away from the closed ball.
  - For the slab, `X_1` lies at the sphere's equator (inside the open slab) and `X_2` on a face away from the poles.
- **Volume map.**
  - Off-diagonal entries `∫_{F_0} div X_1` and `∫_{E_0} div X_2` vanish, so `DV(0)` is diagonal and positive.
  - `s ↦ ∫_A det DΦ_s` is `C^2`, uniformly over measurable `A`.
  - The derivative is `L^1`-continuous, and the contraction mapping gives `|s| ≤ Cq`.
- **Nesting and perimeter.** Applying the same diffeomorphism to both sets preserves inclusion, and `P(Φ_s H) ≤ ‖cof DΦ_s‖_∞ P(H)`. ✔

### Lemma 2.2, uniform scalar ω-minimality (L140–173)

- The lattice inequality is standard.
- Both symmetric-difference identities were checked on all `E ⊂ F, H` states:
  - `|(H∩F)ΔE| + |(H∪F)ΔF| = |HΔE|`;
  - `|(E∩H)ΔE| + |(E∪H)ΔF| = |HΔF|`.

  Nesting of both new pairs was checked as well (`checks_r2.out`). ✔
- **Case `P(H) < P(E_j)`.** Then `P(H∩F_j) + P(H∪F_j) ≤ P(H) + P(F_j) < M`. Lemma 2.1 gives

  `P(E_j) + P(F_j) ≤ (1 + C|s|)(P(H) + P(F_j)) ≤ P(H) + P(F_j) + C_M|HΔE_j|`,

  and `|HΔE_j| ≤ |B_ρ| = 4πρ^3/3`.
- **Large balls.** `ω ≥ M/ρ_0^3` makes the inequality trivial.

  This matches AFM Definition 2.5 verbatim: "for any ball `B_r(x_0) ⊂ T^N` and any set of finite perimeter `F` with `EΔF ⊂⊂ B_r(x_0)`, `P(E) ≤ P(F) + ωr^N`". Here `N = 3` and `T^N` is the unit-volume torus `R^N/Z^N` (AFM p. 5, line 275 of the text extraction). ✔ (See M1 for the quantifier.)

### Regularity paragraph (L175–192)

AFM Theorem 4.2 (p. 22) was read verbatim. Its hypotheses are:

- a sequence of ω-minimizers with a common ω;
- `sup P < ∞`;
- `χ_{E_h} → χ_E` in `L^1(T^N)` with `E` of class `C^2`.

Its conclusion is that, for `h` large, `E_h` is `C^{1,1/2}` with `∂E_h = {x + ψ_h(x)ν(x)}` and `ψ_h → 0` in `C^{1,α}` for all `α < 1/2`.

- The manuscript paraphrases this accurately.
- It states correctly that AFM give no proof ("essentially contained in [3]").
- It applies the theorem separately to each component.
- `B_R`, `C_R` and `S_R` are all `C^2`, and a disconnected boundary is allowed. AFM themselves apply Theorem 4.2 to lamellar sets on p. 28.
- Open representatives with `E_j ⊂ cl F_j`: `E_j \ cl F_j` is open and null, hence empty. ✔
- The scope sentence (regularity for exact minimizers only, lower bounds extended through the minimum) is present. ✔

### Section 3, expansions, centering and coercivity (L194–254)

- **Expansions.**
  - Sphere volume `∫(ψ + ψ^2/R + ψ^3/(3R^2)) = 0` and tube volume `∫(η + η^2/(2r)) = 0` were checked exactly.
  - The area densities were checked exactly.
  - Eliminating the linear terms gives `½Q_B` and `½Q_{C,r}` (SymPy series in `checks_r2.out`).
  - The sphere density is exactly linear in `|∇ψ|^2` at first order, with coefficient ½. The remainder is therefore `O(‖ψ‖_∞ ∫ψ^2 + ‖∇ψ‖_∞^2 ∫|∇ψ|^2)`, as stated. ✔
- **Slab.** The exact volume `∫V^+ + ∫V^- = 0` and the Dirichlet expansion hold. ✔
- **Centering.**
  - The moment-map derivative is minus the Gram matrix of the `ω_i`, which is invertible, and the implicit function theorem applies to `C^1`-small graphs.
  - The slab shift `(V^+, V^-) ↦ (V^+ - c, V^- + c)` works because the means sum to zero. ✔
- **Spectra.**
  - Sphere: `(l(l+1) - 2)/R^2`.
  - Tube: `(m^2 - 1)/r^2 + 4π^2k^2`.
  - The removed means are `O(‖·‖_2^2)`. For example, `Q_B(ψ) = Q_B(ψ - ψ̄) - (2/R^2)|∂B_R| ψ̄^2` with `ψ̄ = O(‖ψ‖_2^2)`, which is absorbable. ✔

### Section 4.1, compactness and the equatorial constraint (L256–318)

- **Ellipsoid upper bound.** The ellipsoid with semiaxes `(r, r, R^3/r^2)` lies in the closed `C_r`, has the inner volume, and has its longest semiaxis tending to `R < 1/2`. Numerically, (area − 4πR²)/ε² ≈ 20.12 at R = 0.27 and stabilizes, so the bound `O(ε^2)` holds. ✔
- **Limit identification.**
  - Lower semicontinuity plus nonnegative deficits make each limit a scalar minimizer, which Assumption 1.1 classifies.
  - The ball's projection is a radius-R disk inside a radius-R disk, so the centers coincide.
  - The normalization uses only a translation and a signed permutation, both ambient isometries. ✔
- **Scale (4.1).** The coercivity of Section 3 and `D ≤ Cε^2` give `‖ψ‖_{H^1} + ‖η‖_{H^1} = O(ε)`. ✔
- **Trace compactness.** The traces `H^1 → H^{1/2}(S^1)` embed compactly into `L^2`. ✔
- **(4.2).** Weak lower semicontinuity of the Dirichlet parts, strong `L^2` convergence of the potentials, and `r_j/R → 1` give the bound. ✔
- **(4.3).**
  - The equator point is `y = h + (R + ψ)e_θ` at axial height 0.
  - The tube slice is star-shaped, so `|y| ≤ r + η(arg y, 0)`. Then `y·e_θ ≤ |y|` gives exactly `ε + h·e_θ + ψ ≤ η∘φ`. ✔
- **Bound on h.** On the half circle, `h·e_θ ≤ |η∘φ| + |ψ|`, so `c|h| ≤ O(ε)`. ✔ (See M2.)
- **Composition limit.** This follows by density plus uniform composition bounds. ✔
- **Translation shift.** `ũ = u + d·ω_tr`. Since `Jω_i = 0`, `Q_B(ω_i, f) = 0` for every `f` in `H^1`, so the energy and the mean are unchanged. The equator trace of `d·ω_tr` is `d·e_θ`. ✔

### Section 4.2, quadratic minimum (L320–356), all checked exactly

- **Averaging.** Common rotation about the axis preserves the trace inequality. The forms split orthogonally by angular Fourier mode, and the nonzero modes have zero mean, so their energy is nonnegative.
- **Sphere profile.** For `u_A = A(1 - 2|t|)`:
  - the mean is 0 and `Q_B/2 = 4πA^2`;
  - the Jacobi image is `-2A/R^2` on both hemispheres;
  - so `Q_B(u_A, w) = 0` for `w` with mean zero and trace zero, and `u_A` is the minimizer at trace `A`.
- **Green function `g_R`.**
  - `-g'' - g/R^2 = -1` away from 0, and `g'(0+) = -1/2`, giving a jump of −1.
  - `g'(1/2) = 0` and the mean is 0.
  - `B(g, g) = g(0) = G_R`, which was also matched to the Fourier series `2Σ 1/((2πk)^2 - R^{-2})` at three radii.
- **Cylinder energy.** For axial `v`, `½Q_{C,R}(v) = πR·B(v, v) ≥ πR D^2/G_R` by Cauchy–Schwarz with `v(0) = B(v, g)`.
- **Scalar minimization.** The constrained minimum of a positive-definite quadratic under `D - A ≥ 1` is `4πR/(R + 4G_R)`, at `A = -R/(R + 4G)` and `D = 4G/(R + 4G)`. ✔

### Section 4.3, recovery (L358–378)

- The volume corrections are `O(ε^2)`.
- The margin expansion at height parameter `τ` was checked symbolically to `O(ε)`. At `τ = 0` the bracket equals `γ > 0`, and off a strip the zeroth-order term dominates.
- Slice-maximum containment: the maximizer of transverse distance on a compact slice of `cl E` lies on `∂E`.
- Order of limits: `ε → 0`, then improve the smoothing, then `γ → 0`. ✔

### Section 5.1, logarithmic recovery (L380–422)

- **Cutoff integrals.** `∫|∇χ|^2 = 2π/log(δ/a)`, with `∫χ^2`, `∫χ` and `‖∇χ‖_∞` as stated. Corner smoothing costs `O(ℓ^{-2})`.
- **Core margin.** `2t - ε = ηε`.
- **Outside the core.** The perturbations are nonnegative inward and outward displacements and only help. The unperturbed gap there is `≥ a^2/(8R) - ε = (ℓ^2/(8R) - 1)ε > 0`.
- **C¹ size.** `t‖∇χ‖_∞ = O(√ε/ℓ^2)`.
- **Bump costs.**
  - The bumps have disjoint support from `χ`, so the cross Dirichlet terms vanish.
  - Bump energy is `O_δ(ε^2/ℓ^2)` and the spherical potential is `O_δ(ε^2/ℓ^2)`, both `o(ε^2/ℓ)`.
- **Arithmetic.**
  - `log(δ/a) = ℓ/2 - log ℓ + log δ`, checked.
  - Four patches give `4 · ½ t^2 · 2π/(ℓ/2) = 2π(1 + η)^2 ε^2/ℓ`, checked. ✔

### Section 5.2, minimizers and exact vertical charts (L424–466)

- **Limit pair.** Inclusion centers the ball normally.
- **Branch.** The slab branch applies above half volume.
- **Scale (5.1).** It follows from coercivity and the upper bound.
- **(5.2).** Both signs were re-derived, including the `−h` on the lower face.
- **(5.3).** The identity `W = A·p` holds exactly (`checks_r2.out`).
- **Bounds on `A_j`.**
  - `A_j = 1 + O(δ^2) + o(1)`;
  - `|∇A_j| ≤ Cδ + o(1)`, because `∂_x √(R^2 - |x|^2) = O(δ)` and the `∇p` terms are `o(1)` by `C^1`-smallness. ✔

### Section 5.3, localization and annular capacity (L468–538)

- **Orthogonal splitting.** `Q_B(ψ) = Q_B(b) + Q_B(l) + Q_B(k)`, with `Q_B(l) ≥ 0` (degrees ≥ 2) and `Q_B(b) = O(ε^4/ℓ^2)`.
- **Low modes.** `‖l‖_{C^1} ≤ C_N ‖l‖_2`, so `W - W_hi = A(b + l)∘F = o_N(ε)` uniformly.
- **(5.4).** Young's inequality on `∇(A·k∘F)` and the change of variables give the bound. The pole patches are disjoint, so there is no double counting.
- **Spectral inequalities.** They are correct, since degree `l ≥ N + 1` gives eigenvalue `≥ (N+1)(N+2)/R^2`.
- **Quantifier order.** The order δ, then ξ, then N, all before `j → ∞`, gives `(1 + Cδ^2 + ξ + C_{δ,ξ}/N^2)/(1 - 2/N^2) ≤ 1/(1 - ζ)`. ✔
- **(5.5).** `½|∇V|^2 + ½|∇W|^2 ≥ ¼|∇(V - W)|^2`, which gives the factor ¼. ✔
- **(5.6).**
  - Jensen and weighted Cauchy–Schwarz give the bound, with equality for the log profile (checked).
  - `b_j ∈ [δ, 2δ]` with `|m(b_j)| = O_δ(ε/√ℓ) = o(ε)`, from the `L^2` bound.
  - At `a_j = c√ε`, `R - √(R^2 - a^2) = (c^2/(2R) + o(1))ε`.
  - `log(b/a) = ℓ/2 + O_{δ,c}(1)`. ✔
- **Two-sided inequality.** `(s + h)_+^2 + (s - h)_+^2 ≥ 2s^2` holds by cases and by a random test, so no bound on `h/ε` is needed.
- **Total.** `(1/4) · (4π/ℓ) · 2ε^2 = 2πε^2/ℓ`. ✔

## REPAIR items (manuscript only; no theorem or constant changes)

- **M1. Lemma 2.2, quantifier (L141–146, L162–164).**
  - Problem: Lemma 2.1 needs the pair to be `L^1`-close to `(E_0, F_0)`, which is guaranteed only for `j ≥ j_0`.
  - Replacement: "Then, for all sufficiently large j, both components are scalar ω-minimizers with one constant ω independent of j."
  - AFM Theorem 4.2 concludes "for h large", so the change is harmless.
  - Also define `M := sup_j (P(E_j) + P(F_j))` in the statement, since `M` is used at L170 but introduced only in Lemma 2.1.
- **M2. Bound on h (L303–304).**
  - Problem: "the positive part on the left has `L^2` norm at least `c|h_j|`" is not literally true. The norm is at least `c|h_j| - ‖ψ_j(·,0)‖_2`.
  - Replacement: "On the half-circle where `h_j·e_θ ≥ 0`, (4.3) gives `h_j·e_θ ≤ |η_j(φ_j(θ),0)| + |ψ_j(θ,0)|`; taking `L^2` norms, `c|h_j| ≤ O(ε_j)`."
- **M3. Symbol F_j used twice (L454, L478).**
  - Problem: `F_j` denotes the outer minimizer throughout, and `F_j^±` is then reused for the chart map `x ↦` direction. This collides in the same section.
  - Fix: rename the chart map, e.g. `Θ_j^±`, in (5.3) and in the definition of `W_{j,hi}^±`.
- **M4. Undefined ω_i and ω_tr (L233, L312).**
  - Problem: `ω_i` and `ω_tr` are never defined, and `ω` is also the quasiminimality constant.
  - Fix: add "Let `ν = (x - c)/R` be the unit normal of the reference sphere and `ν_i` its coordinates, the normal components of translations; `ν_tr = (ν_1, ν_2)`." Then use `ν` throughout (L233, L312, L464).
- **M5. Minor overloaded symbols (optional).**
  - `η` is both the tube height and a small parameter in §5.1 (L383). Suggest `κ`.
  - `V` is a volume, the slab heights `V^±`, and the recovery profile `V` (L363).
  - `D` is both `D_R(ε)` and the trace `D` (L345).
  - `A` is a set (Lemma 2.1), a trace, and the coefficient `A_j`.
  - "sphere latitude `τ`" (L366) is actually `τ = cos(polar angle) = z/R`; suggest "at sphere height parameter `τ = z/R`".
- **M6. Contribution boundary, missing primary comparisons (L99–103).**
  - Problem: the contribution reviews in the research pin (I278 and its literature record; I270) identified moving-interface and rigorous logarithmic-selection precedents that the manuscript does not cite. I278 states explicitly that "two moving interfaces" alone is not a sufficient distinction.
  - Suggested replacement for L99–102: "Logarithmic response in droplet contact is classical, including rigid plates [LGL, Lv] and deformable droplet–droplet and bubble–bubble contacts [Morse–Witten; Ginot et al.]. A rigorous logarithmic second-order selection term for undeformed optimal shells, driven by nonlocal interaction, appears in [ABLW, Theorem 4.5]. The present contribution is the sharp nonlinear minimum over all finite-perimeter nested pairs, with both interfaces free; no priority is claimed beyond the sources compared."
  - References to add, as recorded in the research-pin literature files:
    - D. C. Morse and T. A. Witten, *Droplet elasticity in weakly compressed emulsions*, Europhys. Lett. 22 (1993), 549–555, doi:10.1209/0295-5075/22/7/012.
    - G. Ginot, R. Höhler, S. Mariot, A. Kraynik, W. Drenckhan, *Juggling bubbles in square capillaries: an experimental proof of non-pairwise bubble interactions*, Soft Matter (2019), doi:10.1039/C8SM02477D, arXiv:1910.10029.
    - S. Alama, L. Bronsard, X. Lu, C. Wang, *Core shells and double bubbles in a weighted nonlocal isoperimetric problem*, arXiv:2212.06381. Cite the actual Theorem 4.5, not the "4.21" in its v1 introduction.
  - Optional: the journal version of LGL, Phys. Rev. E 54 (1996), 5436–5446, doi:10.1103/PhysRevE.54.5436.
  - These details were taken from the staged I278/I270 literature records. I did not re-read the sources myself, and the parent should confirm the bibliographic data before printing.
- **M7. Scope reminders (optional).** The research records list exclusions that the manuscript leaves implicit: no functional Γ-limit, no contact-set classification, and no regularity of arbitrary near-minimizers. The last is already covered at L190–192. One clause after L94 would complete this: "No Γ-limit or contact-set classification is asserted."

## Checks of the specific concerns raised in the task

- **Finite-perimeter attainment.** Direct method on compact `T^3`: BV compactness, lower semicontinuity of perimeter, and `L^1` continuity of volume and a.e. inclusion. ✔ (L263–265, L425)
- **Quasiminimality and regularity.** Lemma 2.2 gives exactly AFM's Definition 2.5 with a uniform ω (after M1). The hypotheses of AFM Theorem 4.2 were verified verbatim. ✔
- **Shape coercivity.** Spectral gaps after centering, with the mean terms absorbed, give (4.1) and (5.1). ✔
- **Tube sharp constant.** `K(R) = 4πR/(R + 4G_R)` was re-derived exactly, with the lower and upper bounds matching. ✔
- **Logarithmic polar contact 2π.**
  - Upper: 4 patches × `t^2/2` × `4π/ℓ` with `t = ε/2`.
  - Lower: `(1/4)` × `(4π/ℓ)` × `2ε^2`.
  - Both equal `2πε^2/ℓ`. ✔
- **Chart and localization factor.** The exact identity `W = A·p` holds, and the bounds on the distortion and on `∇A` are correct. The `(1 + Cδ^2 + ξ)` and `C_{δ,ξ}/N^2` losses are removed in the correct order. ✔
- **Hidden assumptions.** None found. No symmetry, connectedness or regularity of competitors is used. Containment proofs use slice extrema, not connected slices.
- **Endpoints.** The open intervals are required. `R = 1/3` genuinely fails for the slab problem, as shown above, and no endpoint uniformity is claimed. ✔

## Contribution boundary

- The manuscript credits AFM, the classical status of logarithmic droplet response, and the classical tools (quadratic forms, Green functions, planar capacity).
- It makes no worldwide-priority claim.
- With M6, its contribution statement would match the I270/I278 boundaries: the paired all-BV reduction with the fixed-circle trace limit (tube), and the concentrating lower passage at two shrinking contacts (slab).
- **Literature screen.** A bounded web screen on 2026-10-13 (two queries on nested two-volume perimeter contact and rigorous compressed-droplet logarithmic asymptotics) found no duplicate theorem. Search absence is not evidence of novelty.

## Not inspected

- The truth of the upstream theorem (stipulated) and the proofs behind AFM Theorem 4.2 (Almgren/Tamanini-type regularity).
- Morse–Witten, Ginot et al., ABLW, LGL and Lv in the original. I relied on the staged I278/I270 literature records for their content and bibliographic data.
- The staged I263/I275/I253 research proofs and the I269/I277 reconstructions were not re-read line by line in this round. This audit re-derives the manuscript's own text. The earlier source audit covers those records.
- Stredulinsky–Ziemer (arXiv:math/9811046), which the source audit flagged, was not read.
- The exact journal record of ABLW was not confirmed.
- **Limits of the checks.** No formal proof certificate exists. The SymPy/mpmath checks verify identities, constants and the ellipsoid order only, not the analysis. They were run with `/tmp/nic-audit-venv/bin/python` (SymPy 1.14.0).

## Files written

- `evidence/claude-manuscript-audit-r2.md` (this file).
- `tmp/audit-r2/`: `checks_r2.py`, `checks_r2.out`, the rebuild (`main.tex` copy, `main.pdf`, `main.log`), `orig.txt` and `rebuilt.txt` text extractions, page images `pg-*.png`, and `upstream-refetch.tex`.

No manuscript, index, or shared file was edited. Nothing was staged, committed, or submitted.
