# T296O independent contribution/eligibility review, round 1

Role: contribution and eligibility only, **conditional on proof correctness**. Correctness is reviewed elsewhere; that directory was not read and nothing here infers its result. Integrity checks and finite tests certify no theorem and no contribution.

Frozen author packet: `frontier/campaigns/2026-10-14/fresh-structural-discovery-r77/`, external anchors verified byte-for-byte (MANIFEST.json `c8d45ad7…69c5`, scope-freeze.md `66056cf6…101a5b`, candidate.md `da41f84d…ac857`, comparison.md `fe6bfb5c…f058f6`, reading-limits.md `86522bd0…fc50`). Pinned source: OpenAI math `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, *Relative generation and the generator problem for finite factors* (catalogue 296), stipulated true.

## Verdict

**TECHNICAL** (eligible; not DUPLICATE, not INELIGIBLE, not BLOCKED; not SUBSTANTIAL).

Conditional on correctness, the full unchanged T296O statement is new relative to the pinned source, its companion Lean scope note, the bounded project-history screen, and the three primaries actually read. Its proof, however, is a direct rerun of source `prop:perturbation` with one changed multiplier. The conjugator is *literally the source's left multiplier* `e^{ih}`, with the same `h`. The changed steps are a short freeness computation, a classical grading inequality and a factor-2 envelope. None requires a new construction or a new type of estimate. Statement novelty and correctness do not change this classification.

The frozen target was not narrowed or replaced to reach this verdict.

## 1. What the source pays (ledger, before evaluating the residual)

Read in full: `introduction.tex`, `independence.tex`, `perturbation.tex`, `generation.tex`, `consequences.tex` at the pin.

| Ingredient used by T296O | Source location | Status |
|---|---|---|
| Free Haar `t_j ∈ U(P^ω)` free from any norm-separable `D`; endpoint formula `(free-endpoints)` | `lem:free-haar-extension` | paid |
| `a t b`, `t*` Haar and free; `s_{j+1}=u t_j`, `W`, `y=zW*` Haar free from `D_ℓ` | `lem:haar-absorption`, proof of `prop:perturbation` | paid |
| Prefixes `g_k`, conjugates `Y_p=p y p^{-1}` forming a free Haar family | `prop:perturbation` | paid |
| `h=(α/ℓ)Σ Im(g_j^{-1} y g_j)`, `‖h‖≤α`, `‖h‖₂=α/√(2ℓ)` | `prop:perturbation` | paid, **identical `h` in T296O** |
| Prefix-cancellation identity moving `k`-th perturbation to the front | `(perturbation-prefix)` | paid (template) |
| Multiplicities `n_e=ℓ`, `Σn_p²=2ℓ²−ℓ` | `(perturbation-multiplicity)` | paid, reused verbatim |
| First-order pairings `τ(ξ*Y_pW)=0` (`p≠e`), `τ(ξ*Y_p^{-1}W)=0` | proof of `prop:perturbation` | paid (template for T296O (3),(4)) |
| Degree-grouped exponential expansion, nondecreasing-row majorization `|C_d| ≤ A^d` | `(perturbation-majorization)` | paid (template) |
| Haagerup length-one bound with proof | `lem:length-one-convolution` | paid |
| Polar-decomposition lifting to `U(P)` | proof of `prop:perturbation` | paid |
| Lower semicontinuity of `f_ξ`, Baire continuity points, `G_δ` description | `lem:projection-continuity`, proof of `thm:relative-generation` | paid; norm topology is finer, so the source arguments transfer word for word to a complete metric |

**Unconstrained operator-norm upgrade, also paid** (parent author feedback, credited by the author). `{g_j^{-1} y g_j}` is a free Haar family, so Haagerup gives `‖h‖ ≤ √2α/√ℓ`. Clipping coordinate representatives at that bound represents the same ultrapower element and gives norm-small `e^{ih_n}` in `M`. The source's left perturbation plus Baire on the norm-complete `U(M)` then gives norm-dense `G_δ` unconstrained relative generators. I verified that every step here uses only the source and the faithful-trace moment formula for norms. This is an elementary strengthening and is credited as zero contribution.

## 2. The residual: exact conjugation, step by step

T296O replaces `u' = e^{ih}u` by `u' = e^{ih}ue^{-ih} = (e^{ih}·e^{-i uhu*})·u`. This is again a left perturbation, by the unitary `m = e^{ih}e^{-iuhu*}`. Mapping each changed step to the source:

1. **Prefix identity (candidate (2)).** The source identity applied with multiplier `m` gives `∏_k(e^{iH_k}e^{-iJ_k})W`, where `J_k=g_k u h u* g_k*`. This is formal and identical in method.
2. **β cancellation (candidate (5)).** The new first-order terms are the `q_{kj}=g_k u g_j*` conjugates. The candidate's (3) generalizes the source's `p^{-1}`-centering argument from `p∈G` to arbitrary `p∈U(D_ℓ)` by the same two-line freeness calculation. The diagonal terms give `|τ(u)|²` by `τ(a g b g*)=τ(a)τ(b)` for `g` Haar free from `a,b`. The off-diagonal terms vanish because `g_k^{-1}g_j≠e`. The result `αβ/2` with `β=‖u−τ(u)‖₂²` is the standard first variation of a conjugation constraint, which here projects the response onto the non-commutant direction. This is a few lines of routine free probability with no new idea.
3. **Degree-triangle majorant (candidate Lemma 2.1).** This replaces the source's exact coefficient isometry by an inequality. Orthogonality of different `F`-degrees in `D * L(F)` is classical. One-line proof: `d↦d⊗1`, `g↦g⊗λ(g)` preserves the joint distribution, because `D⊗1` and `{g⊗λ_g}` are free with Haar generators. Hence `τ(w)=τ(w)·δ_{deg w,e}`. Triangle inequality within a degree is immediate. The source already notes that its majorization "already includes all free reductions and all contributions collected at the same resulting word". The degree map sends `q_{kj}yq_{kj}*` to the same `Y_{p_{kj}}` as `p_{kj}yp_{kj}*`, so each new row has the *source* envelope `A_k`.
4. **Doubled rows (candidate (6)–(7)).** There are 2ℓ rows with envelopes `A_1,A_1,…,A_ℓ,A_ℓ`. The source's nondecreasing-sequence argument gives `(2A)^d`, hence `4α` instead of `2α`. This is a factor of 2 with no new estimate.
5. **Norm control (candidate §5).** The conjugator is `e^{ih}`, with the same `h` as the source. Its smallness is exactly the paid upgrade. Conjugation preserves the spectrum automatically.
6. **Baire (candidate §6).** This is the source argument at `u0=v0uv0*`, with `α` depending on `β`. It is unchanged.

**Answer to the assigned question:** β cancellation, the degree-triangle majorant and the doubled rows together form a routine perturbation adaptation, not a substantial new estimate or construction. No new free variables, words, witness, test vector or topology argument is introduced. The only analytic inequality (Haagerup length one) is the source's, applied to an envelope that is twice the source's. The proof could not have been obtained by quoting the source *statement*: `e^{ih}u` leaves the orbit, so the source proof has to be rerun. That rules out DUPLICATE, but rerunning a proof with a constrained multiplier is the defining case of TECHNICAL.

**Generality is formal.** The candidate's "exact spectral orbit, atoms, multiplicities, no diffuseness" headline is equivalent to the two-point (projection) case. For nonscalar `u`, choose a nontrivial spectral projection `q=1_E(u)`. Then `vqv*=1_E(vuv*)∈W*(vuv*)`, so `G(P,q) ⊂ G(P,u)`. Density for `q` therefore gives density for `u`, and `G(P,u)` is `G_δ` anyway. Conversely, apply the theorem to `u=2q−1`. Arbitrary spectral data therefore adds no strength beyond projection orbits. Arbitrary `u`-coefficients are not what makes the residual harder: even `u=2q−1` is non-Haar, so the same degree lemma is needed either way.

## 3. Actual norm-flexible graph encoding vs. arbitrary q and fixed P

Ma–Shi–Yang arXiv:2604.21482v2 was read at the operation level (Lemma 2.2, Lemmas 3.1–3.7, Prop. 3.8, Remark 3.9, the proof of Theorem 1.1, Prop. 3.10, Remark 3.11, Cor. 3.12).

- **Norm flexibility confirmed, not dismissed.** The proof of Lemma 3.7 itself says "we may assume ‖A_n‖ ≤ 2^{-n}". Replacing `A_n` by `δA_n` leaves `W_0^*({A_n})` and `R(A_n)` unchanged. Then `A_0=(P_0−δ²ΣA_n²)^{1/2}→P_0`, `V→P_0`, and `P_0'=V*V` satisfies `‖P_0'−P_0‖=O(δ)`. A near-identity unitary implements this. Prop. 3.8 Case II needs `G(P_0MP_0)=0`, which is paid by the source (`G(M)=0` for all separable II₁ factors, plus the DSSW scaling formula).
- **This pays part of the T296O conclusion.** Take a fixed irreducible `P` and a base point whose nontrivial spectral projection `q` (or `1−q`, with trace ≤ 1/2) lies **in `P`**. Choose a partition `1−q=ΣP_j` in `P` with `τ(P_j)≤τ(q)` and `N≥2`. Prop. 3.8 with scaled `A_n`, applied in `M` (the `A_n` and matrix units lie in `M`), gives `M=W*(q',{P_j}) ⊂ W*(P,q')` with `q'` norm-close to `q`. So at such base points, and at their left `U(P)`-translates (G is left-`U(P)`-invariant), norm-density holds by finite projection encoding with no free probability. The author's phrase "when the initial projection belongs to the prescribed partition" is this case. The review makes it explicit relative to fixed `P` (Optional item O2).
- **It does not cover the general base point.** Recovery in Lemma 3.7 uses `P_0=I−ΣP_n∈N`, so the base projection must lie in the von Neumann algebra of the retained partition, which here lies in `P`. Concrete witness: `M=P*B`, with `B` diffuse abelian and `q∈B` of trace `t`. Then `P⊂M` is irreducible, `E_P(pqp*)=t` for all `p∈U(P)`, and so for every projection `e∈P`, `‖pqp*−e‖ ≥ ‖pqp*−E_P(pqp*)‖₂ = √(t(1−t))`. No MSY-type base point lies within norm distance `√(t(1−t))` of the `U(P)`-orbit of `q`. Replacing `P` by `W*(P,q)` would retain the partition only through the unperturbed `q`. That is exactly the coefficient-algebra change the author identifies. I found no operation in the read passages that closes this gap.
- MSY Prop. 3.10/Remark 3.11 (prescribed real part) changes the added element's spectrum and does not retain `P`, so it is not an orbit statement relative to `P`.

**Conclusion:** the norm-small graph encoding is real and pays T296O's density at "aligned" base points. It does not pay arbitrary `q` relative to an independently fixed `P`. This supports **not DUPLICATE** on the read evidence. It does not support SUBSTANTIAL, which is decided by §2.

## 4. Other comparators, history and companion screen

- **Shi arXiv:1911.07696v2** (lines 1–150: Theorems 3.5 and 4.1 statements). These are unrestricted Φ-norm perturbations that produce irreducible operators. There is no fixed `P`, no orbit constraint and no `W*(P,·)=M`. Adjacent only.
- **DSSW arXiv:0706.1953v2** (abstract/introduction lines 1–60; Lemmas 6.1–6.2 and Theorem 6.3, lines 1040–1090). The downward basic construction `⟨N,e_P⟩≅M` for *finite-index* inclusions gives one-projection relative generation at a specific Jones projection. It offers no genericity, no norm density and no infinite index. Adjacent only. The source credits this itself.
- **Companion:** pinned `lean/docs/296.md` (retrieved to scratch, SHA256 `aaaf849d…5a10`) scopes the formalization to the 2-norm `G_δ` and single generation. There is no orbit or norm statement. Catalogue neighbours 287, 288, 289 and 300 were screened at catalogue-entry level only. Of these, 289 (Kadison–Kastler near-identity conjugacy) moves algebras, not generators, and gives no route to the orbit statement that I could identify.
- **Project history:** repository-wide Markdown searches (excluding `private/`, catalogue copies, the r77 packet and all `t296o-*` directories) for relative generation, generator problem, relative generator, irreducible inclusion, unitary orbit, norm-generic, Popa, free Haar, II1 factor and singly generated found no earlier source-296 development. The only hits were the parent-r10 `screen-289.md` (a path-lifting screen on conjugate algebras, unrelated) and the T286F standard-invariant chain (finite-depth fusion categories, unrelated). `frontier/NEW-TEN-2026-10-14.md` mentions T296O only as this pending round.
- **Chronology and eligibility:** the scope was frozen after disclosed exploration of the β, grading and clipping strategy and before final write-up. No pre-exploration claim is made, and the earlier trace-2-norm idea was rejected pre-freeze for a valid reason (small-corner encoding with `‖Q‖=1`). I checked that elementary argument and agree it pays the 2-norm version. Scope is unchanged (anchor verified). Nothing makes the target INELIGIBLE. Nothing is missing that would make the verdict BLOCKED.

## 5. REQUIRED objections (for any contribution statement, ledger or count use)

1. **R1 — Classification.** Any record must describe T296O as a technical adaptation of source `prop:perturbation`: the same free variables, word, `y`, `h`, conjugator `e^{ih}`, witness and Baire argument, with the multiplier `e^{ih}` replaced by `e^{ih}e^{-iuhu*}`. The β response, degree-triangle bound and doubled envelope must not be called a new estimate or construction.
2. **R2 — No credit for spectral generality.** The "every exact spectral orbit, atoms/multiplicities, no diffuseness" headline must be stated as formally equivalent to the projection-orbit case (§2, `G(P,1_E(u))⊂G(P,u)`). It must not be counted as extra strength. The projection instance must not be counted separately, which the author already concedes.
3. **R3 — Norm upgrade and clipping are zero-credit.** `scope-freeze.md` still lists "norm-controlled descent" as proposed new work. That list is superseded by `comparison.md`. Any integration must cite the comparison's crediting, not the freeze list, and must state that the conjugator equals the source's left multiplier.
4. **R4 — Novelty boundary.** Any wording must say "new relative to the pinned source, its companion note, the bounded project-history screen and the three read primaries". No literature-wide priority claim may be made. In particular, aligned base points (§3) are already reachable by MSY-type finite encoding, so the only uncovered content is density at non-aligned base points.

## 6. Optional items

- O1. The author could note the one-line coaction proof of Lemma 2.1 (§2 item 3) and cite it as classical, which would make the routine character explicit.
- O2. `comparison.md` could restate the MSY coverage relative to fixed `P` ("base points with a nontrivial spectral projection in `P`, up to left `U(P)`") and add the free-product witness of non-coverage (§3).
- O3. The author could record the converse reduction (theorem for projections implies theorem for all nonscalar `u`) in candidate §1.
- O4. A literature screen for "generic relative generation by a projection" and "unitary orbits of projections generating with a subfactor" beyond the three primaries was not done by the author or by me. It could only lower the verdict, not raise it.

## 7. Validation performed (integrity only)

- External anchors of all five named files matched. The author `verify.py` was read, then run in place and on a `/var/tmp` copy with `--anchor`/`--tree`: PASS (25 payloads, 9 canonical blobs, 13,223 tree entries). A wrong anchor gave `MANIFEST_ANCHOR`. A sorted SHA256 list of the frozen packet was identical before and after.
- The author `diagnostics.py` was read, then run from the copy with explicit output `/var/tmp/t296o-contrib-r1/diag-out.json`: PASS, 2,892 exact checks, 3 negative controls detected. The output is byte-identical to the frozen `diagnostics-results.json`. These are finite algebraic checks, not mathematical verdicts.
- The three arXiv v2 PDFs were independently re-downloaded to scratch. All SHA256 values match the author receipts.
- This directory's `verify.py`, adapted from `t133e-contribution-r1/verify.py` with provenance recorded in its docstring and in `input-binding.json`, authenticates this directory and the frozen packet. It rejects links and nonregular entries, binds the nine canonical blobs and primary receipts, and runs copied positive and reason-checked negative controls. The manifest SHA256 is reported externally only.
