# T298P independent full manuscript review, round 1

Reviewer: independent manuscript review sub-agent (Claude Opus 5.5). This is a mathematical and presentation gate for the concrete draft `t298p-manuscript-r1`. It gives no acceptance, novelty-priority or count verdict. A first attempt of this round ended on a provider rate limit with no verdict (`t298p-parent/manuscript-review-r1-failure.json`). This review was done from scratch. The later-round directories `t298p-manuscript-r2`, `t298p-manuscript-review-r3` and `t298p-manuscript-review-r4` were not opened, so this round stays independent.

## Verdict

**NEEDS_REVISION**

There is **one REQUIRED repair**. It is a presentation defect: a broken macro in displayed equation (21). It requires no mathematical change and no change of target. I found no mathematical gap. Every analytic step was re-derived, and the four proof-review completions, the nine optional repairs and the four contribution attribution items are present and correct in the actual text. Section "Re-check scope" below describes the narrow re-check that suffices once R-1 is applied.

## Bound object and authentication

- External manifest anchor `24a3e405e1bceda384a8b6a4e28f610809a4c9ec5b32b0a66e0277b24b2124fe` was recomputed and matched. So were `main.tex` `f08aec0f…a22a6` and `output/pdf/main.pdf` `6242cd71…0bcb2`.
- `verify.py`, `build.py`, `controls.py` and `check_arithmetic.py` were read before execution. `verify.py --anchor … --repo …` returned PASS, with 23 payload files and all 51 `inputs.json` files authenticated. The upstream pin is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
- The frozen anchors were recomputed and matched: r104 `b6c52528…`, candidate `ed09eaca…`, scope `8e9b3f5f…`, proof-r2 `eb7f9e3c…`, contribution-r2 `31e84ba9…`, attribution-r1 `27a968a7…`, attribution-r2 `6c77938d…`, formal-r1 `e8d1d16e…` and formal-review-r2 `e7deca3d…`. See `checks/input-authentication.json`.
- The author package was hashed before and after the review and is byte-identical. Nothing in it was written.

## Theorem scope retained

- Theorem 1.1 is exactly the frozen target. It gives two bounded self-adjoint Z1,Z2 in M_k(W*(X)) with the faithful normal trace tr_k⊗τ, and −∞ < χ < χ* < ∞.
- χ is defined in eqs (5)–(6). It uses the operator-norm cutoff Γ_R with all words of length ≤ m, unnormalized Tr_d Hilbert–Schmidt Lebesgue volume, the normalization (q/2)log d, a limsup over all d, an infimum over (m,γ) and a supremum over R.
- No ultrafilter, liminf, conditioning on supplied matrix units, or multiples-of-k substitute appears in the definition or the proof. §4.3 handles every output size N, and §7's last paragraph states the order explicitly.
- Theorem 1.2 keeps the stronger source-specialized transfer: liminf_{ε↓0} G(E_ε(X)) ≥ k⁻²G(X), with k = 2^32 and n = k²+1 = 2^64+1.
- The paper explicitly disclaims a W*-generation claim, a useful effective ε, and uniformity as k → ∞.

## Mathematical audit (re-derived)

**Source interface (§1).** Checked against source298 `04-signal.tex` and `01-introduction.tex`:
- C = (B_1..B_p, Y) with free variance-one semicirculars and Y uniform on p equally spaced points in [−1,1] in a separate tensor factor.
- X = C + √h S, with S a standard semicircular (p+1)-tuple free from C and 0 < h < min{1, Δ²/64}.
- The explicit choice p = 2^64 (with t = 2^48) satisfies `eq:parameters`.
- Bounded deterministic matrix models exist, and `thm:main` gives the gap ≥ 1/2.
- Φ*(X) ≤ n/h is Voiculescu's free-convolution bound.
- Only these properties are imported. The labels `eq:chistar` (02-conventions line 74) and `eq:freeflow` (04-signal line 107) exist and agree with eqs (7)–(8).

**Conventions (§2).**
- The heat identity (8) follows by shifting (7). The difference ∫_0^T Φ − ∫_t^{T+t} Φ → ∫_0^t Φ because Φ(s) ≤ q/s.
- Covariance bound (9): Cauchy–Schwarz gives ‖ξ_j‖² ≥ 1/v_j, and AM–HM then gives Φ*(A+√sS) ≥ q/(c_A+s). With ∫((1+s)⁻¹ − (c+s)⁻¹) = log c this gives the stated bound.
- Items (i)–(iv) match Shlyakhtenko's printed statements (see "Primary-source checks").

**Geometry (§3).**
- With ⟨V, L(H)⟩ = i·tr(H Σ_s[D_s,V_s]), normality is Σ[D_s,V_s] = 0. The dimension is 2k² − (k²−1) = k²+1.
- L_d = L ⊗ id gives d-independent HS inverse norms and operator-norm inverse norms.
- Global uniqueness holds: [u,D_2]_{i,i+1} = u_ii − u_{i+1,i+1} + (off-diagonal terms), and each off-diagonal term is O(r_0).
- Local-coordinate Jacobian: the ratio is |det(I + L_d⁻¹E)| with E = i[κ,Y]. Its singular values lie in 1 ± Cε in real dimension 2k²d², which gives exp(±Cεd²). This is the proof review's completion (repair 4). There is no "triangular shear" wording.
- Orbit volume (15): the k^{d²/2} factor comes from the Tr_{kd}(I⊗v)² = k·Tr_d v² scaling. Fiber factor (16): (ε√k)^{nd²}.
- Unitary volume (17): the sphere fibre has volume 2π^l/(l−1)!·2^{l−1} = (2π)^l/(l−1)!. Stirling gives c = 3/4 + ½log 2π.
- Asymptotic (18) was recomputed: the log d coefficient is −(k²−1)/2 and the log k coefficient is −(k²+1)/2.

**Lower half of (19).**
- Recomputed: the log d terms cancel because −(k²−1)/2 − n/2 + k² = 0.
- The log k terms give −(k²+1)/2 + n/2 + k² = k², i.e. log k after division by k².
- The constant is C_D = log k + (k²−1)c/k² + log c_D/k² (eq. 20).
- Source subsequences give output sizes kd, so the limsup is preserved.

**Lemma 4.2 (rank).** Telescoping gives L terms of rank ≤ m and norm ≤ 2R_0^L. Then |Tr T| ≤ rank·‖T‖. The compression a − PaP has rank ≤ 2m, and the corner renormalizes by N/rank P. This is proof-review repair 2. (R_0 ≥ 1 is not actually needed.)

**Lemma 4.3 (recovery).**
- Actual band projections are equivalent to E_ii⊗1 through a norm-continuous Riesz path, so τ(p_i) = 1/k without a factor assumption.
- Portmanteau applies on closed gap neighbourhoods.
- Truncated polar maps on [1/3,3] use the continuous extension y·g(y*y), so no inversion near zero occurs.
- Path-tree pullbacks give exact matrix units v_i v_j*.
- Rank-lemma moment transfer through the non-functional-calculus root intersection holds.
- Second truncation: ‖QhQ‖ ≤ 2a_0 from Q ≤ 1_{[−2a_0,2a_0]}(h). There are at most 2k² Hermitian parts per coordinate and 4k² in total, a fixed number (repair 8). Complex entries are within 4a_0 and the pair within 4k²a_0.
- Inverse: coefficient norms ≤ C_k a_0/ε = C'_{k,R}, so R' depends only on (k,R).
- Law identification: the unitary conjugacy reduces to I⊗v by the coefficient-algebra uniqueness.
- The compactness contradiction gives the uniform statement (repair 3; the reviewer completion "uniform moment recovery" is present).

**Upper half (§4.3).**
- Net: (C/η)^{2Nl}.
- Polar transport: w with wPw* = Q and ‖w − 1‖ ≤ Cη. U(r)-invariance of the tube image means no measurable selection is needed.
- Remainder ball (24) recomputed: (N²−r²)log(2πe·2NR²/(2(N²−r²))) has the stated form.
- Corner term recomputed: −k²d² log d = −r² log r + r² log k. The bracket is k⁻²h_d + (n/k²)log ε + C_D + O(ε).
- Size terms: −r² log r − (N²−r²) log N + N² log N = r² log(N/r) ≤ N² log(1/(1−θ)).
- The order of limits (ε, source accuracy and R_out fixed; then η; output accuracy for θ; N → ∞; θ ↓ 0; net slack and source tolerance; supremum over cutoffs) is correct.
- Every residue class of N is covered, because retained d ≥ (1−θ)N/k → ∞.

**Unconditional Fisher bound (§5, U1).**
- Recomputed directly with normalized tensor traces:
  - Hw_bc = w_bc H.
  - The Gram matrix (28) equals k⁻¹δδδ.
  - J*W = 0.
  - dim ker J = k².
  - The ranks add to 2k⁴.
- The entry adjoint (29) was verified on E_ij⊗P: the pairing gives δ_ib δ_jc/k² (τ⊗τ)(∂_aP) on both sides.
- The target projection has coefficient (V_aj)_cb/k. With c = (εk)⁻¹(V_aj)_cb, the leading score is Ξ_j^0 = (εk²)⁻¹ Σ_a V_aj⊗ξ_a.
- The energy in (33) is Σ_{a,e} δ_ae τ(ξ_aξ_e)/(ε²k⁴) = Φ*(U)/(ε²k⁴). The manuscript contains the factor 1/(ε²k⁴), so the omission in the proof review's §6 prose (parent note `leading-score-normalization.md`) is resolved in the paper, and no orthogonality of the ξ_a is assumed.
- Neumann series: corrections are O(1) after unscaling, and the inner coefficient is O(1). Adjoint bounds come from (31), and the inner adjoint is ≤ 2‖η‖_π.
- Squaring the triangle inequality gives (27) for ε ≤ 1.

**Noisy path (§6.1).**
- (1/k)Σ_α B_α⊗s_α realizes a standard pair: Σ_α B_α A B_α = k·Tr_k(A)·I = k² tr_k(A)·I, which divided by k² gives tr_k.
- Rotation to (V,O) and √t/k = ε√u give (34) exactly in law.
- Integrating Prop. 5.1 with ds = ε²k² du gives (35): (1/(2k²))∫Φ*(U(u))du + C_{U_0}ε(1+Φ*(X)).
- The k⁻⁴ → k⁻² conversion is explicit.

**Straightening and Theorem 4.1 (§6.2, U3).**
- K_1 = L⁻¹P_oW depends only on T, because P_o(V⊗U) = 0. The normal part is εVU + O(ε²), so H_ε = U + εR_ε has a regular remainder.
- B = alg(T).
- The T-letter grouping is present: each coefficient is a finite T-word, so it lies in alg(T).
- The inverse is the contraction (37), and both formal compositions are identities.
- The common radius margin meets ‖U_a‖ < min(r_a,R_a).
- Self-adjointness of F and G is shown.
- D_BF = I + O(ε), so |Tr_n⊗τ⊗τ log|D_BF|| ≤ Cnε.
- This is proof-review repair 5, and the reviewer completion "inverse-power-series hypotheses" is written in the text.
- One presentational point remains: optional O3.

**Microstates increment (§6.3).**
- (39) uses only Prop 2.8 + projection (χ(H|B) ≤ χ(H)), Thm 4.1 and Thm 2.19 (U free from W*(T), which is embeddable). It explicitly avoids the reader-left equality of Prop 2.12 (repair 6).
- χ(U) > −∞ follows from Prop 4.2 with the n/2 constant (repair 7).
- Prop 4.1 is applied to H_ε at the same ε. This is legitimate because the constants and threshold are uniform for a fixed coordinate bound, as the proposition states.
- C_D and (n/k²)log ε cancel against the upper half at X, which gives (40).

**Finish (§7).**
- Subtracting (35) from (40) and using χ ≤ χ* at the noisy endpoint gives (41): G(Z_ε) ≥ k⁻²(g − G(X_{U_0})) − Cε. All terms are finite.
- (42): G(X_u) ≤ (n/2)log((u+C_X)/u).
- Taking ε ↓ 0 first and then U_0 → ∞ proves (4).
- The explicit existential order (U_0 with G(X_{U_0}) < g/2, then ε with C_{U_0}ε < g/(4k²)) gives G(Z_ε) > g/(4k²) > 0.
- Finiteness: χ(Z_ε) > −∞ by Prop 4.1, and χ*(Z_ε) < ∞ by (9).
- The two-noise-scale template is credited to source298.

## Proof-review completions and the nine optional repairs, checked in the text

The four reviewer completions are all present:

| Completion | Location |
|---|---|
| Rank perturbation | Lemma 4.2 |
| Uniform moment recovery | Lemma 4.3, final paragraph |
| Tube Jacobian | Lemma 3.1, final paragraph |
| Inverse power-series hypotheses | §6.2 |

The nine optional repairs:

| # | Repair | Status in the text |
|---|---|---|
| 1 | Stale status text | Absent from the theorem narrative; Appendix A marks it as provenance only |
| 2 | Rank lemma | Lemma 4.2 |
| 3 | Uniform recovery | Lemma 4.3 |
| 4 | Jacobian | Lemma 3.1 |
| 5 | Thm 4.1 hypotheses | §6.2 |
| 6 | Prop 2.8 instead of Prop 2.12 | §2(i) and §6.3 |
| 7 | Prop 4.2 n/2 constant | §2(iv) |
| 8 | Fixed 2k²/4k² count | Lemma 4.3 |
| 9 | Ineffective ε | Theorem 1.2 and Appendix A |

All are written correctly.

## Contribution-review required items, tested against the text

**R1.**
- §3.1 end and §8.1 name NSS math/9809081v1 Lemmas 2.6, 2.8, 2.9 and 2.10, and credit Marinov (bib [12], in NSS's Re Tr(ab*) convention).
- The classical unitary volume formula is credited.
- Tube geometry is called supporting analysis.
- The novelty is confined to U1/U2/U3 (§1 and §8.3).
- Satisfied.

**R2.** §8.1 credits Shlyakhtenko §5's pattern and states its limits exactly. The four points match `shlyakhtenko-relative.txt` lines 605–745:

| Manuscript statement | Text in Shlyakhtenko §5 |
|---|---|
| Corner p ≤ e11 with [e11,p] = 0 under supplied matrix-unit conditioning models | "there exists a projection p ≤ e11 of rank k′, [e11,p]=0" |
| Compression by the map T | T = T{e_ij} |
| Measure-preserving packing | "is measure-preserving" |
| Ultrafilter equality with the dilated ultrafilter Nω | equality as printed |
| Ordinary limsup is one-sided and its proof is left to the reader | "left to the reader" |
| The second displayed claim repeats "≥" while its packing proof gives the reverse | "Next, we claim χ^{Nω}(…) ≥ …" |

- §8.2 records the relative degeneracy correctly:
  - ultrafilter relative microstates entropy is −∞, via the easy direction χ^ω(·|ℂ) ≤ χ^ω;
  - the ordinary-limsup relative value is not determined by the one-sided statement;
  - the relative Fisher orbital term ((k²−1)/k²)t⁻¹ is non-integrable, so the relative χ* is −∞, and the coefficient is (k²−1)/(2k²)·log;
  - infinities are never subtracted.
- Satisfied.

**R3.** Satisfied. The credits and their locations:

| Credit | Location |
|---|---|
| Prop 4.2 with its embeddability hypothesis and the n/2 vs printed n correction | §2(iv) |
| Covariance bound, derived | §2 |
| χ ≤ χ* (BCG; JP) | §2 |
| Prop 2.8 + projection | §2(i), §6.3 |
| eq:chistar/eq:freeflow | §2 |
| Two-noise-scale template | §7 |

**R4.**
- §8.3 cites the generation preprint's `thm:main` (two self-adjoint generators for each separable-predual II_1 factor, introduction.tex line 29) and the classical Douglas–Pearcy/Wogen technique via DSSW Prop. 1.1 (introduction.tex lines 139–143).
- It cites `cor:entropy-generators` (consequences.tex line 49), where δ, δ_0 depend on the generating tuple.
- It states "generation only".
- Source287's coordinatewise transport (entropy-dimensions.tex line 53) is credited as not shortening the tuple.
- Satisfied.

`required-item-map.md` matches these locations, and its "Other contribution suggestions" claims also check.

## Primary-source checks at changed interfaces (statement level; extents in reading-limits.md)

- **Shlyakhtenko math/9812079v1.**
  - Def. 2.3 (lines 69–93): sup over conditioning microstates, then limsup ("replacing lim sup by lim_{k→ω}"), inf over (l,ε), sup over R. Def. 2.10 gives the algebra version.
  - Prop. 2.8 (line 151): χ(X|Y) ≤ χ(X:Y).
  - Prop. 2.12 (line 179): the reader-left equality, not used.
  - Thm. 2.19 (line 290 ff.): X free from W*(B, X'), B embeddable ⇒ χ(X|B) = χ(X).
  - §4 (lines 428–479; Thm. 4.1 at line 468): the B[t] class (self-adjointness preserving), the majorant F̂, the multiradius, the Jacobian D_BF ∈ M_n⊗M⊗M, and Thm. 4.1 with both inverse identities and ‖X_i‖ < min(r_i,R_i). The proof is omitted ("almost identical to … [4] … and is therefore omitted").
  - Prop. 4.2 (lines 483–493): printed n log 2πet, proof ends with (n/2) log 2πet.
  - §5: as above.
- **NSS math/9809081v1.**
  - Lemma 2.6: polar measure factorization with C_k.
  - Lemma 2.8: lim k⁻²log C_k + ½log k = 3/4 + ½log 2π, Re Tr(ab*) metric, citing [2] Marinov.
  - Lemma 2.9: upper orbit pattern.
  - Lemma 2.10: lower pattern, with u Haar unitary ∗-free from positive b. This matches "free Haar and positive-variable hypotheses".
- **NSS math/9809080v1 Prop. 4.1** (lines 1197–1260): Φ*({g_ij}:B) = d³Φ*(G:M_d(B)) with X = d⁻¹(ξ_ji) (transpose and 1/d). The scalar case (4.4)–(4.5) is there, and the unconditional inequality comes via Remark 2.6 / Theorem 1.2. I checked the k³ vs k⁴ conversion: real Hermitian coefficients normalized for tr_k carry a further 1/k.
- **Source298, source287 and the generation preprint:** as cited above.

## Formal coverage

- Appendix A is accurate for formal-r1:
  - 4 support declarations, namely `coefficient_isometry` assuming the column Gram identity with nonorthogonal ξ allowed, `leading_score_energy` with ε²k⁴, `gap_transfer` assuming both analytic increment bounds and endpoint comparison, and `strict_gap` under a strict error bound;
  - 4 controls (k² vs k⁴, missing comparison, reversed gap, non-strict error);
  - no conjugate variables, inverse series, recovery, entropy limits, source or main theorem.
- It omits the trust boundary:
  - Lean 4.34.1 kernel;
  - only `propext`, `Classical.choice`, `Quot.sound`;
  - pinned Mathlib `d13f23b7…`;
  - dependency oleans reused from cache and not rebuilt.

  This omission is optional O1.
- The sentence "Independent formal-review outcomes, if subsequently available…" is historical audit-pending text, written before formal-review-r2 PASS (no required findings, 18 declarations, 5 rejected mutations, `e7deca3d…`). It is not an analytic defect. Any update must keep the 4+4 scope.

## Reproduction and visual review

- Fresh standalone build: `build.py` was run from a scratch directory with `/tmp/frontier-typeset/tectonic` (sha `a98aa59a…`, which matches the receipt) and SOURCE_DATE_EPOCH 1792281600. It exited 0 with no warnings and gave a **byte-identical** PDF `6242cd71…`. The extracted text is identical to `validation/extracted-text.txt`. Receipt: `checks/rebuild-receipt.json`.
- `main.tex` has no \input, \include, \bibliography or \includegraphics, so it is single-file and self-contained.
- `check_arithmetic.py` was replayed and matches `validation/arithmetic.json`.
- `controls.py` was replayed on a copy under /var/tmp (1 positive, 8 negatives, transient exclusion) and is identical to `validation/verifier-controls.json`. A first attempt under /tmp failed on a tmpfs user disk quota, which is not a package defect. That copy was deleted and the run repeated under /var/tmp.
- All 18 pages were rendered at 110 dpi and each was opened. `checks/visual-review.json` has the per-page hashes and observations.
- Layout is clean: no clipping, overflow, missing glyphs or broken references, and the fonts are embedded.
- **Exception: eq. (21) on page 6** renders "Γ_{mathrmout,kd}" with italic letters.
- The author's `validation/visual-review.json` says no defects were observed. It is inaccurate on this point.

## Rights, authorship and limitations

- The paper and README state author Myeongjin Kang with no affiliation.
- LICENSE-PAPER grants CC BY 4.0 for original prose, LaTeX and PDF. LICENSE-CODE is standard MIT text for original code.
- THIRD-PARTY.md and Appendix A keep third-party papers, source bodies, fonts and tools out of relicensing, and no third-party full text is bundled.
- AI assistance is disclosed.
- The README limitations accurately disclose:
  - no full formalization;
  - the bounded literature screen;
  - the non-vendored TeX bundle, with no universal bitwise-reproduction claim.
- No negative or worldwide-priority assertion rests on the unread leads (Jung math/0410594; Shlyakhtenko 2201.09503; HMU math/0702745; Ueda 1210.6421, 1610.04118; Izumi–Ueda 1306.5372; Connes–Shlyakhtenko). §8.3 says they were not screened and invokes none of them as a premise. No contribution objection is unresolved, so no bounded body check of those leads was performed or needed. This review makes no claim of exhaustive literature clearance.

## REQUIRED objections

**R-1 (presentation; implement exactly).**
- *Defect:* `main.tex` line 424 reads `\Vol\Gamma_{mathrm{out},kd}`, which renders in the PDF (page 6, eq. 21) as italic "mathrmout".
- *Source fix:* replace it with `\Vol\Gamma_{\mathrm{out},kd}`.
- *Package steps:*
  1. Rebuild in a fresh directory.
  2. Re-render and re-inspect all pages.
  3. Regenerate `validation/` (extracted text, latex log, pdfinfo, build/reproduction receipts, and `visual-review.json`, whose "no defects" statement must reflect the corrected PDF).
  4. Reseal `MANIFEST.json` and report the new external anchor.
- *Constraints:* no other mathematical text needs to change, and the frozen target, constants and order of limits stay untouched.

## Optional (non-blocking)

- **O1. Formal paragraph (Appendix A).**
  - Add the trust boundary: Lean 4.34.1 kernel; standard axioms only (propext, Classical.choice, Quot.sound); pinned Mathlib; cached dependency oleans not rebuilt.
  - Optionally replace the historical "if subsequently available" with the formal-review-r2 PASS record (`e7deca3d…`), keeping coverage 4+4.
  - Optionally note that `gap_transfer` is a statement about finite real numbers with explicit nonnegative errors.
- **O2. §5.3: define Ξ_j.** Define Ξ_j := δ_j*(1⊗1) (unprojected) before the remainder display. Its projection onto L²(W*(Z)) is the conjugate variable. Ξ_j is currently used without definition.
- **O3. §6.2: state the reading of the B[t] class.** Say that B[t] is read as absolutely summable sums of B-monomials in which a U-pattern may repeat, with F̂ summing coefficient-norm products over all monomials. Shlyakhtenko's own application of Thm 4.1 to B-coefficient polynomials in his Thm 4.3 already needs repeated patterns, and composition F∘G requires them. This clarification is literal; it is not a gap.
- **O4. §4.3: the r²/N² multiplier.** The main bracket is multiplied by r²/N² ∈ [(1−θ)², 1]. For a bracket of either sign this costs O(θ(1+|bracket|)), and the bracket is bounded above for fixed ε and source parameters. Either state this, or add "and source parameters" to "Constants here may depend on …". The stated order of limits already makes it harmless.
- **O5. §8.1: NSS attribution precision.** NSS Prop 4.1 is relative to M_d(B) for an arbitrary W*-subalgebra B, with the scalar case in (4.4)–(4.5). The unconditional projection inequalities are their Theorem 1.2 via Remark 2.6, deduced from Prop 4.1.
- **O6. Bibliography.**
  - Add \cite{Marinov} where Marinov is named in §3.1.
  - Bib [5] lists "Theorem 3.1", which the text never uses (the proof review also notes it is unused); drop it or cite it where relevant.
  - Bib [3] links only introduction.tex, while `cor:entropy-generators` is in consequences.tex; add that path.
- **O7. Lemma 4.2.** The hypothesis R_0 ≥ 1 is unnecessary; this is cosmetic.
- **O8. Literature.** The listed orbital/dimension/mutual-information leads remain an optional screen for any later priority statement.

## Re-check scope after R-1

If the revision changes only the R-1 token and regenerates the receipts and manifest, a re-check needs only the following: hash binding, a fresh rebuild, renders of the changed page (or all pages), a source diff confirming the single-token change, and the regenerated receipts. All other findings here carry over. Any further textual change, including adopting optional items, needs review of the changed passages.

## Exact commands run (read-only toward the author package)

```
sha256sum MANIFEST.json main.tex output/pdf/main.pdf
python3 -I -B verify.py --anchor 24a3e405…24fe --repo <repo>
python3 -I -B build.py --tectonic /tmp/frontier-typeset/tectonic --output /tmp/t298p-mr1-review/rebuild
pdftoppm -r 110 -png output/pdf/main.pdf /tmp/t298p-mr1-review/render/p ; pdffonts ; pdftotext -layout
python3 -I -B check_arithmetic.py
python3 -I -B <copy>/controls.py --anchor 24a3e405…24fe   (copy under /var/tmp, deleted afterwards)
```

## Seal

This packet is sealed by `MANIFEST.json`. Its SHA256 is reported externally by the reviewer. `python3 -I -B verify.py --anchor <sha>` checks the packet read-only: exact membership, regular single-link files, sizes and hashes. It can also re-authenticate the bound author anchors with `--repo`. `verify_controls.py` exercises the verifier on a temporary copy under /var/tmp. It runs 1 positive and 9 negative cases: wrong anchor, appended file, same-size flip, missing file, extra file, edited manifest, verdict tamper, symlink and hardlink. The recorded `checks/own-verifier-controls.json` came from a provisional seal made before that receipt existed. The final seal adds the receipt with the verifier and control code unchanged, and a post-seal replay against the final anchor was run with transient output. Integrity checks do not certify mathematics.
