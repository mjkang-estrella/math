# Claude manuscript audit r1: *Sharp ball–tube and ball–slab nesting costs in the cubic three-torus*

2026-10-13. Auditor: Claude Opus 5.5 (`claude-opus-5-5`), acting as the review sub-agent the user requested.

- **This is an AI audit, not human peer review.**
- The pinned OpenAI theorem at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` is stipulated true.
- Every new deduction in the finished manuscript was re-derived from the manuscript text itself. Staged I263/I269/I275/I277 records and my earlier `claude-source-audit.md` were treated as supporting evidence only.
- I made no manuscript edits, commits, index edits or external submissions.

## Files reviewed (exact)

The parent revised `main.tex` and `tmp/main.pdf` while this audit was running. **The verdict applies only to the final snapshot below.**

| File | SHA256 |
|---|---|
| `main.tex` (final, audited) | `238bdd71a37d186a4a07efa95ce7d1b314eeb4dfcb8ddbd6249815d00fa39eb8` |
| `tmp/main.pdf` (final, audited; 7 pp., built 12:27:42 PDT from the `main.tex` above) | `a1d2c9d90d5e843cf42b8b14e61e195b039365c7d0762def28323409954800be` |
| `tmp/audit-build/main.pdf` (my independent Tectonic rebuild of the same `main.tex`) | `a02741250ad1a01eba5826f85ceea02ae2fed5c907b54d7f52663ad12983bb59` |
| Superseded snapshot, read first: `main.tex` | `556b7e763c07af0aca130d9d00c95805c2f951f5dbba091261385bafc2d4b284` |
| Superseded snapshot, read first: `tmp/main.pdf` | `e066907cab5b7aba42c524597e447e91cb0d8b91f4856b29dd2884affb546469` |

On the rebuild:

- The two PDFs differ in bytes only because of timestamps.
- `pdftotext -layout` output of `tmp/main.pdf` and of my rebuild is **identical**. The reviewed PDF therefore corresponds to the audited source.
- All fonts are embedded. The log has no undefined references and no overfull boxes.
- Pages 1 and 7 were visually inspected at 60 dpi.

While I was auditing, the parent independently fixed two issues I had found in the superseded snapshot, so neither is reported below:

- **Lemma 2.2 quantifier.** The superseded snapshot said "independent of j" for all j. The final text says "for all sufficiently large j" and defines M.
- **Tube half-circle bound.** The superseded snapshot said "positive part has L² norm at least c|h_j|", which is false as literally stated. The final text derives `h_j·e_θ ≤ |η_j∘φ_j| + |ψ_j|` and takes L² norms.

## Verdict

| Item | Verdict |
|---|---|
| Theorem 1.2 (ball–tube), full deduction as printed | **PASS**, conditional on Assumption 1.1, with one wording repair (R1) |
| Theorem 1.3 (ball–slab), full deduction as printed | **PASS**, conditional on Assumption 1.1 |
| Assumption 1.1 vs. actual upstream Theorem 1.1 (`intro:main`) | **PASS** |
| AFM use (Def. 2.5, Thm. 4.2) | **PASS** |
| Prior repairs D1–D5 | **all addressed** |
| Bibliography | **REPAIR**, minor completeness (R2) |
| PDF | **PASS** |
| **Overall** | **REPAIR** (two small, mechanical repairs; no mathematical gap, no BLOCK) |

## Required repairs

### R1: `main.tex` line 375 (PDF p. 5, §4.3 "Recovery"); the definition of τ is wrong as written

The current text reads "At sphere height parameter `τ = z/R`". If z is the actual height of the perturbed inner boundary point, then the transverse distance is

`√((R+εU)² − R²τ²) = R√(1−τ²) + εU/√(1−τ²) + O(ε²)`.

Under that reading:

- the first-order bracket is `−1 + V(Rτ) − U/√(1−τ²)`, not the printed `−U(τ)√(1−τ²)`;
- the O(ε²) remainder is not uniform as |τ| → 1.

This was verified symbolically in `tmp/checks/manuscript_checks_r1.out`. The printed bracket is correct when τ is the direction cosine `ν₃` of the boundary point, which is the same variable `t = cos φ` that U depends on. The containment conclusion survives under either reading, because only τ ≈ 0 uses the bracket. The displayed formula is nonetheless false under the stated definition.

Exact replacement:

> At the inner boundary point $(R+\eps U(\tau)+s)\nu$ with $\nu_3=\tau$ (the axial variable $t=\cos\varphi$ of Section 4.2), the tube containment margin is

The display that follows stays unchanged. The superseded snapshot's "latitude τ" was loose but compatible with this reading.

### R2: bibliography completeness (PDF p. 7)

All entries were checked against Crossref or the arXiv API on 2026-10-13. Titles and author names are correct. The following data are missing:

- **[5] Ginot et al.** Add "**15** (2019), no. 22, 4570–4582". Crossref doi:10.1039/C8SM02477D gives Soft Matter vol. 15, issue 22, pp. 4570–4582. The authors are Gaël Ginot, Reinhard Höhler, Sandrine Mariot, Andy Kraynik and Wiebke Drenckhan.
- **[2] Lacasse–Grest–Levine.** The paper was published as Phys. Rev. E **54** (1996), 5436–5446, doi:10.1103/PhysRevE.54.5436 (Crossref; title matches exactly). Cite the journal version, optionally keeping the arXiv ID.
- **[6] Alama–Bronsard–Lu–Wang.** The paper was published in SIAM J. Math. Anal. **56** (2024), 2357–2394, doi:10.1137/22M1538545 (Crossref).
  - Add the journal data.
  - Keep "arXiv:2212.06381v4" as the locator for "Theorem 4.5", because I did **not** verify the theorem number in the published version.
  - The arXiv v4 Section 4.4 "Second order limit" does contain "Theorem 4.5 (Second Γ-limit)", with energy rescaled by |log η|. The manuscript's one-line description ("a logarithmic second-order selection term for optimal shells in a nonlocal problem") is fair.

Entries checked and found correct:

- [1] AFM: Comm. Math. Phys. 322(2) (2013) 515–557, authors E. Acerbi, N. Fusco, M. Morini.
- [3] Lv: arXiv:1704.05830, author Cunjing Lv, title exact. Crossref shows a related 2020 Langmuir paper with a different title and coauthors, so citing the arXiv preprint is acceptable.
- [4] Morse–Witten: EPL 22(7) (1993) 549–555.
- [7] OpenAI:
  - the title and date match the source;
  - the pinned blob URL returns HTTP 200;
  - the raw `build/paper.tex` was freshly fetched, SHA256 `ab75095f…a813`, identical to `tmp/src/354-paper.tex`;
  - `intro:main` is the first theorem in §1, so "Theorem 1.1" is correct.

## Optional (non-blocking) suggestions

- **O1 (notation collisions).** Several letters are reused for different objects:
  - `t`: the axial variable (§4.2), a radius correction (§4.3) and a displacement (§5.1);
  - `η`: the tube height and the slab recovery parameter;
  - `c`: the reference center (§3), a constant in `c|h_j|`, and the constant in `a_j = c√ε_j`;
  - `s`: a correction and the variable in `(s±h)_+`;
  - `A`: a trace and the chart factor `A_j`;
  - `D`: `D_R` and the trace D;
  - `V`: volume, the recovery profile and the slab heights.

  None of these causes a logical error, but renaming the §4.3 and §5.1 parameters would help readers.
- **O2 (slab lower-bound sequence).** §5.2 does not say explicitly, as §4.1 does, that one fixes an arbitrary sequence `ε_j → 0` (or one realizing the lim inf) and passes to subsequences. A one-sentence addition at the start of §5.2 would make the lim inf quantifier explicit.
- **O3 (source status).** Assumption 1.1 makes the theorems conditional, which is mathematically sufficient. Readers may still benefit from a phrase such as "an unrefereed preprint" next to [7].
- **O4 (AFM provenance).** The text says AFM "refer to earlier regularity theory". It could also name AFM's reference [3] (Almgren, Memoirs AMS 1976), as AFM itself does.

## Step-by-step check of the printed deductions

### §1: Assumption 1.1 vs. upstream Theorem 1.1

- **Profile.** The profile formula is identical to the upstream one. `4πR²` equals the ball value, `2πr` the tube value and `2` the slab value.
- **Branches and closed ranges.** Upstream uses closed ranges. "Both listed types occur at each common endpoint" and "no further equality cases" match the manuscript's strict ranges plus its transition sentence. Upstream's "slab of width V" is consistent with "coordinate slabs". Complements above 1/2 match.
- **Theorem 1.2 range.** `R < 1/π < 1/3` places the inner set strictly on the ball branch. `r = R − ε ∈ (2/9, 1/π)` places the outer set strictly on the tube branch for small ε. Also `πr² < 1/2`.
- **Theorem 1.3 range.** `R < 1/3` gives the ball branch. `2(R−ε) → 2R ∈ (1/π, 2/3)`, and `2/3 < 1 − 1/π ≈ 0.6817`. Above 1/2 the complement width `1 − V ∈ (1/3, 1/2)` is again on the slab branch.

### §2: regularity reduction

**Lemma 2.1 (two-volume flow).**

- Fields: `X₁` is compactly supported inside the open outer set near a free patch of `∂B_R`; `X₂` is supported near a patch of the outer boundary disjoint from the closed ball. Both patches exist: the tube's poles and the slab's equator lie in the interior, and the outer free patch lies at height in `(R, 1/2)`, respectively outside the ball's horizontal shadow, whose radius `R < 1/2`.
- Derivative: by the divergence theorem, the derivative of `s ↦ (|Φ_s A|, |Φ_s B|)` at the limit pair is diagonal and positive.
- Uniformity: uniform C² dependence on s and L¹-continuity in `(A, B)` give `|s| ≤ Cq` by a contraction argument.
- Perimeter: `P(Φ_s H) ≤ ‖cof DΦ_s‖ P(H)`.
- Inclusion is preserved because one map is applied to both sets.

**Lemma 2.2 (paired quasiminimality).**

- I checked all pointwise states (e ≤ f, h ∈ {0, 1}) for both identities:
  - `|(H∩F)ΔE| + |(H∪F)ΔF| = |HΔE|`;
  - `|(E∩H)ΔE| + |(E∪H)ΔF| = |HΔF|`.
- The lattice inequality is standard.
- The volume errors are at most `|HΔE_j| ≤ |B_ρ|`, which gives `ωρ³`.
- Large balls (including wrapped balls) are handled by `ω ≥ M/ρ₀³`. This matches AFM Def. 2.5 exactly: "for any ball `B_r(x₀) ⊂ T^N` … `P(E) ≤ P(F) + ωr^N`". I re-read Def. 2.5 in the AFM final PDF, SHA256 `7805d5a0…4c72`, p. 7.

**AFM Theorem 4.2 paraphrase.** It is faithful to the printed statement: a sequence of ω-minimizers, `sup P < ∞`, L¹ convergence to a C² set, and for h large a normal graph with `ψ_h → 0` in C^{1,α} for every α < 1/2.

- The sentence "stated without proof … earlier regularity theory" is accurate: AFM write that it "is essentially contained in [3]".
- The limits are C²: a ball, a straight tube, and the slab with its two-component boundary. AFM themselves apply Theorem 4.2 to lamellar sets.

**Open representatives.** If `E_j` is open and `E_j \ cl(F_j)` is an open null set, that set is empty. Hence `E_j ⊂ cl F_j` and `∂E_j ⊂ cl F_j`. The scope sentence (exact minimizers only) is correct, and the lower bounds transfer because D and L are infima.

### §3: expansions, centering, spectral gaps

- **Re-derived (SymPy):** the sphere volume density `ψ + ψ²/R + ψ³/(3R²)`, the tube volume density `η + η²/(2r)`, and both area densities.
- **Quadratic forms:** after substituting the volume identities, `Q_B = ∫|∇ψ|² − 2ψ²/R²` and `Q_{C,r} = ∫|∇η|² − η²/r²`.
- **Remainders:** they are `≤ C(‖ψ‖_∞ + ‖∇ψ‖_∞)‖ψ‖²_{H¹}`, consistent with the printed bounds. The leading gradient term is exact because the `(1+ψ/R)²` factors cancel.
- **Slab:** P − 2 has no linear term.
- **Centering:** for small C¹ graphs, the moment maps have derivative −Gram (`(4πR²/3)I` on the sphere), and the implicit function theorem applies. For the slab, the face-mean shift `(V⁺ − c, V⁻ + c)` is exact.
- **Gaps:**
  - Sphere: `(l(l+1)−2)/(l(l+1)) ≥ 2/3` for l ≥ 2.
  - Tube: modes `(0, k ≠ 0)` need `4π²k² > 1/r²`, i.e. `r > 1/(2π) ≈ 0.159`, which holds since `r > 2/9`. Modes `(±1, k ≠ 0)` give `4π²k² > 0`.
  - The omitted means are quadratic, so their squares are quartic and absorbable.

### §4: ball–tube

- **Upper bound O(ε²).** The ellipsoid `(r, r, R³/r²)` has the exact inner volume, lies in `C_r`, and is embedded. D ≥ 0 by the profile.
- **Compactness and limit.** The profile and classification identify the limit pair. The projected disk of radius R inside a closed disk of radius R forces equal centers.
- **(4.1) and (4.2).** These follow from coercivity, weak H¹/strong L² compactness, compact trace into L²(circle), and the identification of `Z_r` with `Z_R` up to O(ε) metric changes.
- **(4.3).** The equator point is at `h + (R+ψ)e_θ`, at height 0 because of the common translation. Its distance from the axis is at least the dot product with `e_θ`, and the tube slice is a radial graph. Hence `ε + h·e_θ + ψ ≤ η∘φ`, exactly.
  - The final half-circle bound gives `|h| = O(ε)`.
  - Composition passes to the limit by density.
  - `d·ν_tr` lies in the Jacobi kernel and has mean zero.
- **Quadratic minimum.**
  - Angular averaging is valid because `Q = Q(avg) + Q(rest)` with `Q(rest) ≥ 0` on mean-zero functions.
  - `Q_B(u_A)/2 = 4πA²` and `∫u_A = 0` (verified).
  - The Jacobi image of `u_A` is `−2A/R²` on both hemispheres (verified), so `Q_B(u_A, w) = 0` for mean-zero w with zero trace. The boundary terms vanish at the equator (w = 0) and at the poles (factor 1 − t²).
  - Green function: `−g'' − g/R² = −1` on `(0, 1/2)`, derivative jump −1, `g'(1/2) = 0`, mean 0 (verified).
  - On mean-zero axial v, `Q_{C,R}(v)/2 = πR·B(v,v)`. Since `B(g,v) = v(0)`, Cauchy–Schwarz gives `≥ πR D²/G_R`.
  - The constrained minimum is `4πR/(R+4G)` with `A* = −R/(R+4G)` and `D* = 4G/(R+4G)` (verified).
  - On the whole range, `1/(2R) ∈ (π/2, 9/4)` and `9/4 < π`, so `cot < 0` and `G_R > R² > 0`. Numerical checks at four radii agree.
- **Recovery.**
  - Volume corrections are `s, t = O(ε²)`.
  - Containment margin: correct with the reading of R1. The bracket at τ = 0 equals γ > 0, and the zeroth-order term is ≥ c > 0 away from the equator.
  - Slice-maximum argument: a maximizer of transverse distance on a compact inner slice is not interior, so it lies on ∂E.
  - The order of limits is valid.

### §5: ball–slab

**Upper bound (§5.1).**

- Log-cutoff integrals: `∫|∇χ|² = 2π/log(δ/a)`, and the `χ²`, `χ` and `‖∇χ‖_∞` bounds hold.
- C¹ smallness: `t‖∇χ‖_∞ = O(√ε/ℓ²)`.
- Containment:
  - Moving inward along the normal keeps the set inside `B_R`.
  - Core margin: `R − ε + t − √((R−t)² − |x|²) ≥ 2t − ε = ηε`.
  - Off the core: `|x|²/(2R) ≥ εℓ²/(8R) ≫ ε`.
  - The bumps sit on patches separated from the faces by a positive distance.
- Vertical-slice extrema and the interval structure of slab slices give region containment.
- Constant: `4·½·t²·2π/(ℓ/2) → 2π(1+η)²ε²/ℓ` (verified).

**Charts (§5.2).**

- The limit is the centered ball in a width-2R slab.
- The obstacle inequality (5.2) holds for both signs, including the sign of `h_j` on the lower face. I re-derived the equality case symbolically.
- The chart identity (5.3), `W = A_j p_j`, is exact (rationalized symbolically to 0, plus numeric samples).
- Distortion bounds: `A_j = 1 + O(δ²) + o(1)` and `|∇A_j| ≤ Cδ + o(1)` follow from `|x| < 2δ` and C¹ smallness.

**Localization (§5.3).**

- Bounds: `|b_j| = O(ε²/ℓ)`, and the low modes are `O_N(ε/√ℓ) = o_N(ε)` in C¹ by finite-dimensional norm equivalence.
- (5.4) follows from the product rule, Young's inequality and a change of variables with Jacobian `1 + O(δ²) + o(1)` over two disjoint caps.
- High-mode inequalities: `∫k² ≤ R²/((N+1)(N+2)) ∫|∇k|²` and `Q_B(k) ≥ (1 − 2/((N+1)(N+2))) ∫|∇k|²`. Both hold for degrees ≥ N+1.
- The order "δ, then ξ, then N, then j" is valid because `C_{R,δ,ξ}` is absorbed by N.
- (5.5): `L ≥ ½(1−ζ')Σ(∫|∇W_hi|² + ∫|∇V|²) + o ≥ ((1−ζ)/4) Σ ∫|∇Z|²`.
- (5.6) follows from Jensen plus weighted Cauchy–Schwarz.
- Choice of `b_j`: since `‖Z‖_{L²} = O(ε/√ℓ)`, some radius `b_j ∈ [δ, 2δ]` has `m(b_j)² ≤ C_δ ε²/ℓ = o(ε²)`.
- At the inner radius: `m(a_j) ≥ (1 − c²/(2R))ε ± h − o(ε)`, using `R − √(R² − c²ε) = c²ε/(2R) + O(ε²)` and `log(b/a) = ℓ/2 + O(1)`.
- The inequality `(s+h)_+² + (s−h)_+² ≥ 2s²` was proved by cases and checked on 10⁵ random samples.
- Total: `¼·(4π/ℓ)·2ε² = 2πε²/ℓ` (verified).

## Contribution and literature statements

The introduction:

- credits the logarithmic droplet response ([2]–[5]) and ABLW's logarithmic second Γ-limit;
- states that the quadratic forms, Green functions and capacity are classical;
- describes the result as "the sharp nonlinear minimum over all finite-perimeter nested pairs, with both interfaces free", without a "first" or priority claim.

This is consistent with the I270/I278 boundaries and with my earlier source audit. I did not repeat a literature search; the bounded web screen in `claude-source-audit.md` is unchanged. Stredulinsky–Ziemer (math/9811046) remains an optional background citation.

## Sources and versions

- **Research pin:** `mjkang-estrella/math@d513e308d86a38004d78bab9b9e88532e92bf56c`. Staged at `/tmp/publication-r017-r022`; `manifest.json` SHA256 `2854605ad816ee3a4a327833a55bcda06f47cbb7c269030445ffc1563576ce7d`.
- **Upstream (stipulated):** `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, `preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/build/paper.tex`. Freshly fetched via the pinned raw URL; SHA256 `ab75095f542adf4073a41a26a3c3ae97be7b55fa19674ec4fb4c288f7145a813`. Theorem `intro:main`, lines 56–84, was read in full.
- **AFM:** final PDF `tmp/src/afm/afm.pdf`, SHA256 `7805d5a0b9daf3873a199bbfe23d4064964fc2e72701be6d45303549028d4c72`. I re-read Def. 2.5 and Thm. 4.2 together with the preceding attribution sentence.
- **Bibliographic metadata:** Crossref REST API (AFM, Morse–Witten, Ginot et al., LGL, ABLW) and the arXiv export API (mtrl-th/9603005, 1704.05830, 2212.06381v4), queried 2026-10-13. ABLW v4 HTML §4.4 was read via web fetch, limited to the heading and the Theorem 4.5 statement.
- **Prior evidence consulted:** `evidence/claude-source-audit.md` (SHA256 `458809b6…cfa`), and the staged I278 review and literature record (ABLW reading).
- **Checks:**
  - Script `tmp/checks/manuscript_checks_r1.py`, SHA256 `34adb9235467db8ee3e61f369bd133ae9961e92aaa7aa0fe1f37af94ede0ac07`.
  - Output `tmp/checks/manuscript_checks_r1.out`, SHA256 `17d8340da5bcd43002b17b30422848dc9618e88f10ff94f9e2ff54102e7a45b5`.
  - Run with SymPy 1.14.0 in a throwaway venv at `/tmp/claude-nic-audit/venv`.
  - Rebuild: `tmp/audit-build/` with the specified Tectonic binary. The reviewed `tmp/main.pdf` was not overwritten.

## Not inspected

- The truth of the upstream theorem, which is stipulated.
- The proofs behind AFM Theorem 4.2 (Almgren/Tamanini-type regularity).
- The theorem numbering inside the published SIAM version of ABLW, and ABLW beyond the §4.4 heading and the Theorem 4.5 statement.
- The full texts of Lacasse–Grest–Levine, Lv, Morse–Witten and Ginot et al. Only metadata was checked; their content characterization relies on the I270/I278 records.
- PDF pages 2–6 were checked through text extraction and the source-text match, not visually page by page.
- Any manuscript revision after `main.tex` SHA256 `238bdd71…9eb8`.

The symbolic checks verify constants and identities only. They do not verify the analysis, and there is no formal proof certificate.
