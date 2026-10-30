# T216A independent adversarial proof review, round 1

Reviewer: Factory Droid (Opus 5.5), independent proof gate. Not author assistance. No contribution verdict is given. Pinned source theorems at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true; only new deductions were checked. The parallel contribution review draft was not read. Nothing in the frozen author packet was edited.

## Verdict

**PASS_FULL_T216A**

At the unchanged frozen scope, I find no required objection. Every step of the three-component proof (lattice-interface.md, continuum-boundary-pressure.md, amplitude-assembly.md) was re-derived, including all quantifiers and limit orders. The proof establishes, for the exact model and field convention of original-scope.txt, positive finite constants with

    [p(h)-p(0)] / [h^(16/15) (log 1/h)^(1/15)] -> C_p,
    m(h) / [h^(1/15) (log 1/h)^(1/15)] -> C_m = (16/15) C_p,

along the full real limit h↓0, with C_p = c_* (kappa A_XY)^(16/15) (8/15)^(1/15), kappa = exp[R_D(0,0)/(2K)], K = 2/pi, and c_* the uniformly phased whole-plane ultraviolet circle-average chaos pressure coefficient on D=(-1,1)^2 divided by |D|=4. The ten optional clarifications below do not change the conclusion. The proof has no subsequence, bounded-tilt, finite-box, comparison-constant or conditional-continuum restriction.

The verdict is a proof gate only. Parent assistance, r48 technical status, the 13/20 count and target20 conferred no presumption. The unresolved Gielerak 1986 comparator is not a premise of the candidate and does not bear on this verdict. A contribution verdict belongs to the separate gate.

## Integrity and identity checks (certify no mathematics)

- Recomputed all eight external anchors; all match. Inspected verify.py, controls.py, seal.py and diagnostic.py before execution. `python3 -I -B verify.py ROOT 14f72cc7…0e79` gives `PASS_INTEGRITY_ONLY files=84 directories=15`; the all-zero anchor and a one-hex-digit-changed anchor are rejected. seal.py was not run on the frozen packet.
- The author's 14 controls and arithmetic diagnostic were run only on a disposable copy under `/var/tmp`. All 13 mutations were rejected, the positive copy passed and all 5 arithmetic negative alternatives were detected. The copy re-verified afterwards.
- source-check.py (this directory) independently confirms the following. The canonical complete `sources/preprints-tree.json` has SHA256 `eeecc1da…dc5e09b`, 13223 entries and is not truncated. The **actual bytes** of all 35 selected private source files match their canonical git blob SHAs. The packet's copied continuum note is byte-identical to `t216a-parent/continuum-boundary-pressure.md` and to commit `d7bfa4e1`. Six `pdftotext -layout` replays (ABJJ, MMP, Šidák, JSW, Ginibre, Newman–Wu) are byte-identical to the packet texts I read. Output is recorded in receipts.json.
- Note on the author verifier: it re-checks blobs against the *copied* tree inside the packet. My authentication instead uses the separately anchored repository tree.

## Re-derivation by component

### A. Finite multi-arc pinned-rim lower bound (lattice §1)

Source: L `geometry.tex` 1–959, read in full, including `geo:pinned-sector` and its proof (418–675).

- **Pairing arcs.** The inductive slit construction is rigorous. An arc between interior points does not separate the plane, and the complement of finitely many disjoint compact arcs and holes is connected. Rectilinear dyadic perturbation then keeps every clearance positive. Each hole is incident to exactly **one** arc because the configuration is perfectly matched. Hence the exit geometry at each hole is literally the source's single-exit geometry (strip, guard P_j, endpoint regions H_j and H'_j, guard reaching the wall between them).
- **Single-valued lifts after all cuts.** The branch jumps only across arcs, and every arc lies inside its strip. The domain minus holes and strips is connected (a finite union of disjoint dumbbells does not separate), and no retained loop encircles a hole. So the original branch is single-valued there and zero near F. Each strip is simply connected. The cut energies add to ∫_U|ϑ|².
- **Admissibility.** The "fixed mixed geometry" class (S `02-heights.tex`, `heights:geometry`) allows any finite union of rectangles and pins. This covers k holes and k/2 strips. Cell-pin localization (`geo:cell-pin-localization`) is stated for every fixed dyadic cut mixed geometry.
- **Restorations.** Restoring strip j (with any subset of other strips restored) needs four things. (i) The patch kernel is exactly local to W_j: the guard separates the bonds, and W_j is disjoint from other strips, patches and F. (ii) Both topologies of W_j have one lift (W_j is simply connected and meets only its two holes), so the source patch-loss identity applies. (iii) The exterior of W_j on G' gives a shifted-to-centered ratio ≤ 1 by `prop:comparisons`. This needs no single-valued lift, as the author notes. (iv) The Bayes identity `geo:conditional-pin-identity` holds with D computed in the centered law on the pre-pin geometry G'. That law does not depend on the connection, so the other strips' states are irrelevant. The restoration identity Φ_open=(Φ_cut−L_τ)/(1−L_0) is exact for each ν and ℓ. It is applied k/2 times, and L_0→0 keeps the denominators away from zero. All errors therefore vanish in the order ν→∞, then ℓ↓0. No uniform-in-k estimate is used.

### B. Neutral whole-plane correlations and κ (lattice §2)

- **Bracket (5).** The k-source spin–height duality follows from the Fourier-current proof of L `lem:duality`, applied verbatim with k inserted charges and current paths. The current is supported inside the rim, so the exterior factor cancels in the pinned comparator exactly as in `geo:thermodynamic-bracket`.
- **Energies, re-derived.** Green's identity for φ=Σσ_i log|z−z_i| gives ∫|∇Θ|² = 2πk log(1/t) − 4π Σ_{i<j}σ_iσ_j log|z_ij| + O(t). In the free comparison square Q_R the constant term 4π²[Σ R_Q(z_i,z_i)+2Σσσ G_Q(z_i,z_j)] has log R coefficient (Σσ_i)²/(2π)=0. Its R_D part is R_D(0,0)(Σσ)² + o(1) → 0, so the free and pinned energies agree with (6) as R→∞.
- **Normalization.** The center exterior energy (`geo:single-energy`) is 2π log(1/t)+4π²R_D(0,0). With a=8π, subtracting k times the center gives exp[(4π/2a)Σσσ log|z_ij| + k(4π²/2a)R_D(0,0)] = κ^k Π|z_ij|^{σσ/4}. For k=2 and |z|=1 this reproduces L's c_shape = exp{(4π²/a)R_D(0,0)} = κ², hence B_XY = (κA_XY)². The k-nest attachment (`geo:attachment-factorization`, density 2^k) and the pinned-root argument are already stated for general fixed k. The leading terms of the joining ratio cancel hole by hole, and the cross term is independent of t. Uniformity on compact separated sets follows from the moving-configuration statement by sequential compactness. Nonneutral free correlations vanish by global rotation invariance of the free-box limit.

### C. Block Laplace limits (1) and (2) (lattice §3)

- **Moment bounds.** The Lee–Yang bound (S `fields:lee-yang`) holds in free boxes. Its proof only rotates the measure, and the free law is already rotation invariant, so E X² = v/2. Positivity of signed moments, including repeated sites, follows from the current expansion.
- **Collision bound (9) for E_0.** The free two-point function is dominated by the pinned Q_{Cn} one by Ginibre (strong boundary fields; clarification 5). Then S eq. (20) and a_{Cn}/a_n → C^{-1/8} (L `geo:center-ratio`) give (δ+1/n)³. Collision removal with Hölder over m equal exponents is the source operation (`fields:moments`).
- **Identification of the limit.** Neutral moments converge to κ^k∫Π|z|^{σσ/4}; nonneutral moments are 0. Sub-Gaussian bounds give determinacy and uniform integrability of exponentials. This proves (1) for every fixed t.
- **Pinned (2).** The source field is S_n = n^{-2}Σ a_n^{-1} exp{(G_n(x,x)−G_n(0,0))/(2K)} e^{iθ_x}δ_x with limit V_* = exp(R_D(z,z)/(2K)) μ_D in the circle-average convention (S eq:target-field). Since E Φ_ε² = (2π)^{-1}log(1/ε)+R_D(z,z) exactly for circle averages, the raw field e^{iθ}/a_n converges to exp(−(R_D(z,z)−R_D(0,0))/(2K))·V_* = κμ_D. No spatial weight survives.
- **Collar.** In the Whitney collar, the MMP Proposition 1 bound of conditional parent-square two-point functions by aligned ones is correct. The sum Σ_r (n/r)·r²a_r ≲ n(δn)^{7/8}(log)^{1/16} gives δ^{7/8} after normalization. Lee–Yang upgrades this to C√p δ^{7/8}. The order (collar at fixed δ, n→∞, δ↓0) is valid.
- **Moving tilts.** The uniform bound sup_n E exp(s|Y_n|) < ∞ for every s makes exp(t_n Y_n) uniformly integrable for any t_n→t. Since Y_n converges in law, the Laplace transforms converge along every sequence of real h.

### D. Increment sandwich (lattice §4)

- **Upper (10).** The conditional law on V_n has one-site terms Re[e^{iθ_x}(h + b_c Σ_{y∉V_n} e^{-iφ_y})]. Combine them into one coefficient J'(δ_x) of modulus ≤ h + b_c·#. Pair couplings are identical. MMP Prop. 1 (J(M) ≥ |J'(M)|, read in full in its stated form) then gives ⟨cos θ_x⟩' ≤ ⟨cos θ_x⟩^+_{Q_n,h}. Averaging over the TI state gives |V_n| m(h) ≤ E^+_{Q_n,h} Σ_{V_n} cos θ. Integrating in h yields (10) exactly, because the boundary spins are fixed.
- **Lower (11).** Ginibre's second inequality (Prop. 3) gives f'(s) ≤ Σ_{x∈Q} E_{Λ,s}cos θ_x. Each term is at most m_free(s) by Ginibre monotonicity in Λ, and m_free = p' at h>0 (clarification 6). Hence log E_{Λ,0}e^{hX_Q} ≤ |Q|Δp(h). Let Λ↑Z² at fixed Q.
- **Normalization.** |Q_n|/n², |V_n|/n² → 4 = |D|. The boundary layer costs O(t/(n a_n)) → 0. This yields (12) for each fixed t.

### E. Continuum coefficient equality (copied parent note)

- **Existence of A.** ABJJ Theorem 1.6 and Appendix B (read in full) give lim u^{-16} log P(|μ*(Q(0,1))|>u) = −c*(β) for the circle-average whole-plane chaos on exactly D̄=[-1,1]². The exponent is 4/β²=16 at β=1/2. The corrected lower-bound argument does not use the faulty moment-to-tail inference. Kasahara/Laplace then gives A = sup_u(u−c*u^16) ∈ (0,∞). The independent uniform phase does not change A (upper: e^{t|μ|}; lower: restrict cos U ≥ 1−η). Scaling gives μ*(aD) =_d a^{2−β²/2}μ*(D) = a^{15/8}μ*(D), hence A_{aD} = a²A.
- **Collar moments.** For a Whitney square B with Q=3B⊂D, spatial Markov gives μ_D|_B = e^{iβh}μ_Q|_B. The UV convention adds no variance factor. Positivity of the charge kernel e^{β²E'} (ABJJ (2.7)) makes E|μ_Q(1_B e^{iβh})|^{2N} ≤ E|μ_Q(1_B)|^{2N}. Dilation of the Dirichlet field and ABJJ Lemma 2.5 on the fixed reference pair give C N^{1/16} s^{15/8}. The Whitney count O(1/s) per scale gives δ^{7/8}. Moment-to-Laplace gives C + C(tK)^{16/15}, hence (3) with δ^{14/15}.
- **Small ball.** Coefficient variances satisfy sd(A_k),sd(B_k) ≤ Cρ_1^{-k} by Cauchy–Schwarz on the ρ_1-circle. Standardized thresholds are ≥ c'ε q^{-k}/(k+1)² with q<1. For k ≤ K=C_0 log(e/ε) the product is ≥ exp(−C log²(e/ε)). For k > K the thresholds grow exponentially (choose C_0 > 1/log(1/q)), so the deficits are summable. Šidák (Theorem 1/Corollary 1 read; arbitrary variances and correlations, singular by approximation) applies to each finite prefix. Continuity from above handles the infinite intersection. Zero-variance coordinates give probability one. The independent uniform phase adds a factor ε/(2π).
- **Hölder direction.** Let ψ=U+βh. The bound F_{D,E}((1−η)t) ≤ (1−η)log Z_ψ(t) + η log E exp(((1−η)t/η)|μ_D(1_E(1−e^{iψ}))|) holds for every deterministic ψ, and the last term is ≤ ηC + ηC(t·t^{-2}/η)^p. Then Z_{*,E}(t) ≥ P(G)·inf_G Z_ψ(t) with log P(G) ≥ −C log² t. This gives limsup F_{D,E}(s)/s^p ≤ (1−η)^{1−p}A_E.
- **Reverse expansion.** E(Re μ)^n = 2^{-n}Σ_j C(n,j) E[μ^j μ̄^{n−j}]. Every Dirichlet term is ≥ 0. Whole-plane nonneutral terms are 0, and neutral terms carry the factor exp(−β²Var/2) ≤ 1. Absolute exponential integrability justifies the termwise sum, so Z_* ≤ Z_D for t ≥ 0.
- **Collar restoration.** Hölder gives (1−η)^{1−p}(1−δ)²A + Cη^{1−p}δ^{14/15}. Send δ↓0 at fixed η, then η↓0. The lower bound on D comes from the reverse expansion.

### F. Real-h inversion and convex secants (amplitude assembly)

With N = (t/A)^{8/15}(15/8)^{1/30}h^{-8/15}u^{-1/30} and n=⌊N⌋, we have n/N→1 and log n/u → 8/15. Then h n²a_n → A·(t/A)(15/8)^{1/16}(8/15)^{1/16} = t and n²h^{16/15}u^{1/15} → (t/A)^{16/15}(15/8)^{1/15}. These limits give (4) for every fixed t over all real h↓0. The liminf and limsup are attained along sequences, and the integer n(h,t)→∞, so repeated values of n are harmless. Let t→∞ next. Both bounds then tend to A^{16/15}(8/15)^{1/15}κ^{16/15}c_*. Finally, convexity and differentiability of p on (0,∞), with Δp regularly varying of index 16/15, give the secant limits C_p(λ^{16/15}−1)/(λ−1) and C_p(1−λ^{−16/15})/(1−λ^{−1}). Both tend to (16/15)C_p as λ↓1. The pressure identification (15/16)C_m = C_p follows.

## Objections

### Required

None.

### Optional clarifications

1. **Regularization convention.** continuum-boundary-pressure.md writes Γ_{D,ε} without naming the mollifier. Three objects must share one convention: the lattice μ_* (kernel Π|z_ij|^{σσ/4}), the source μ_D (from V_*), and the Markov coupling μ_* = e^{i(U+βh)}μ_D. They do in the circle-average convention of ABJJ (1.1) and S eq:target-field. I checked that E_h[e^{iβΣσ_j h(z_j)}] times the Dirichlet kernel equals Π|z_ij|^{σσβ²} exactly when Var Γ_ε = log(1/ε)+2πR_D(z,z). A different mollifier would scale both continuum objects by the same constant. The equality of coefficients would survive, but the lattice identification needs the stated convention.
2. **"Assume the standard spatial Markov decomposition".** This is a classical theorem (whole-plane GFF modulo constants restricted to D equals an independent Dirichlet GFF plus harmonic extension; ABJJ §2.4 cites Miller–Sheffield, IG IV, Prop. 2.8). It is not an additional hypothesis of the target. The word "Assume" should be read as a citation. I did not read MS17 (see the reading limits below).
3. **Indicator tests and Green weights in (2).** The source theorem uses C_c^∞ tests and the n-dependent weight exp{(G_n(x,x)−G_n(0,0))/(2K)}. Passing to 1_{E_δ} with the raw normalization is routine but not written out. A thin boundary layer has L² norm ≲ d^{1/2} by the box bounds, and the Green diagonal converges uniformly on compacts (S `correlations:green-diagonal` plus a compactness argument).
4. **k-source duality and k-hole pinned exterior energies.** L `lem:duality` and `geo:pair-exterior` are stated for one or two sources. The general-k versions follow by the same proofs. The energy algebra is verified in B above.
5. **Free ≤ pinned two-point domination in (9).** The domination is cited as "finite comparison". It follows directly from Ginibre's inequality with boundary fields sent to infinity, or from MMP Prop. 1. The citation should say so.
6. **m_free(h) = p'(h).** The text compresses this. One argument: E_{Λ,h}cos θ_x increases in Λ, so p'_Λ(h) ≤ m_free(h). Interior sites give liminf p'_{Λ_L} ≥ E_{Λ_M,h}cos θ_0 for each M. Convex derivatives converge at differentiability points, and Lee–Yang gives differentiability for h>0.
7. **MMP application.** MMP Prop. 1 indexes one coefficient and phase per M. Several single-site terms must first be merged into one complex coefficient, as the author indicates. Stating J(δ_x)=h+b_c·#{exterior neighbours} ≥ |J'(δ_x)| explicitly would close the reading.
8. **Pairing construction.** The minimum-matching option with "small perturbations of an optimal drawing" is less clean than the inductive slit option, which is fully rigorous. The one-exit-per-hole observation in A is worth stating, since it makes the source exit geometry apply literally.
9. **Whitney reference shape.** Fix Q = 3B (Whitney distance ≥ 2·side). A single similarity class then lets ABJJ Lemma 2.5 apply once to the reference pair, with the boundary-intersecting squares handled by |weight| ≤ 1_B and kernel positivity.
10. **formal-plan.md and diagnostic.py are not proofs.** They contributed nothing to this verdict.

## Reading and search limits

- **Read in full:** L geometry.tex 1–959; S 06-correlations.tex 1–531; S 07-fields.tex 1–574 (in three overlapping blocks); ABJJ text 40–479 (definitions, Theorems 1.2–1.6, §2 through Lemma 2.7 start) and 2505–2711 (Appendix B and references); MMP text 30–269 (Propositions 1–2, Lemma 1, Theorem 1).
- **Read in part:** S 01-introduction.tex 1–269, with a few display-skipped lines; lines 70–119 (field and normalization) were re-read fully. S 02-heights.tex 185–264 (geometry, mixed/pin inputs). L heights.tex 1–140 (duality, comparisons). L introduction `thm:main` and `center-definition`. C introduction 1–60 (`thm:main`). Šidák Theorem 1 and Corollary 1 passage. Ginibre text 110–250 (Propositions 1–5).
- **Not read:** S 03/04/05 proofs (sector theorem, localization proof, kernel bounds; their statements are used as stipulated truths through L/S citations). Remaining S 02, C lower sections, and other family-216 companions. JSW body (only located Theorem 1.3; ABJJ Lemma 2.5, read with proof, supplies the operative sharp moment). Newman–Wu, LSZ(W), Fröhlich 1976, CGN 2012, CGN II. Miller–Sheffield IG IV. Dunlop–Newman. Gielerak 1986 (not accessed; not a proof premise).
- **No searches.** I did no web search or prior-art search. Prior-art and Gielerak questions are outside this gate.
- **Retrieval is not reading.** Matching hashes, layout-replayed PDF text, and the author's controls and diagnostics certify identity only.

## Files

- review.md: this report.
- receipts.json: recorded output of source-check.py and the author-packet checks.
- source-check.py: reviewer identity checks. Read-only except a fresh /var/tmp scratch directory.
- verify.py / seal.py / controls.py: exact-inventory seal of this directory, verification with an external anchor, and mutation controls run only on /var/tmp copies.
- manifest.json: inventory produced by seal.py. Its SHA256 is reported externally to the parent and is not stored here.
