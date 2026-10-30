# T117Q manuscript review, round 2

Role: independent manuscript gate, round 2 (Factory Opus 5.5). This directory supersedes the
round-1 directory assignment. Source theorems at OpenAI/math
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated. New deductions and exact interfaces
were audited.

No acceptance, count, ledger, staging, commit, author-packet edit, upload or publication action
was taken. No nested agent was used. Prior gate verdicts, the author repair receipt and the
parent preflight were read as context. None of them substitutes for this gate. The pending
release preparation was not consulted and has no bearing on this verdict.

## Verdict

**REPAIR_REQUIRED_T117Q_MANUSCRIPT** (not PASS_FULL_MANUSCRIPT_T117Q).

- **Required repair R1 (new in v2).** The newly added in-text reproduction paragraph prints all
  four command-line options with an en dash instead of two hyphens. As printed, the PDF build
  command fails. This is a typesetting error, narrow and trivially fixable, but it makes a
  factual statement in the manuscript false. Details and exact locations are in "Required
  repair".
- **Round-1 M1 is closed.** The classical general-metric cardinality bound is now credited to
  Bourgain (1987) and Tomczak-Jaegermann (1974) through GMN §1.3, with the unread originals
  disclosed. Every attribution and every quantitative claim in the new text matches the GMN
  primary, which I read myself. The JLW/MN chain is correctly demoted to a grid-side
  improvement.
- **The mathematics passes.** I re-derived the standalone proof of the full frozen statement
  from the v2 text. It is complete and correct, with no gap, unpaid factor or scope narrowing.
  The theorem and Sections 2–7 are unchanged from v1 apart from three differential thin spaces.
- **Prior required objections.** All of proof E1–E8, contribution RQ1–RQ4, editorial E1–E5 and
  R2-A–D are implemented in the manuscript text. R2-C now carries the M1 attribution and
  nowhere implies a recent origin for the cardinality order.
- **Formal coverage.** The formal-coverage statement is accurate.

If R1 is repaired with no other change, no other required item remains from this review.

## Inputs authenticated (identity only)

All anchors in the brief were recomputed as SHA256 and match.

v2 manuscript (current):

| File | SHA256 |
|---|---|
| manifest.json | 7da5998a…d518 |
| main.tex | 9ed9f7dd…7c13 |
| main.pdf | adcc1c36…2fa8 |

The PDF has 16 pages, and main.tex has 1068 lines plus a trailing newline.

Round 1 and v1:

| File | SHA256 |
|---|---|
| Round-1 review MANIFEST.json | 7f9c9fd1…b801 |
| v1 manifest | 1a127b60…e982 |
| v1 main.tex | e9bd0498…ff9f |
| v1 main.pdf | 634aeabf…a76d |

Prior gates:

| Gate | SHA256 |
|---|---|
| r59 MANIFEST | 053986e5…8ae2 |
| candidate | e32f7a12…aea4 |
| original-scope | fc5a8f87…fe36 |
| proof-r1 | bb6941a2…3cea |
| contribution-r1 | 6d6366df…5013 |
| parent-literature manifest | c93929fe…deb8 |
| parent-literature response | d697cfcb…eb22 |
| contribution-r2 | 855f7729…c4c0 |
| formal-v1 | b741e2d7…9b37 |
| formal-review-r1 | 98fde2d1…9ae4 |

Packet checks:

- **Author verifier.** It accepts the v2 packet with the external anchor (exit 0) and rejects
  an all-zero anchor (exit 1).
- **Author controls.** I read the author's integrity_controls.py first, then ran it on a
  /var/tmp copy. Of 15 cases, only `positive` was accepted, and each rejection gave its
  expected reason.
- **Input copies.** I compared all 21 copies byte for byte with their origin files. All match.
- **Source blobs.** I recomputed the 9 copied source117-1 files as Git blob ids. All 9 appear at
  their exact paths in sources/preprints-tree.json, which has SHA256 eeecc1da…, 13223 entries
  and is not truncated.
- **Copied prior reports.** The proof-r1, contribution-r1, contribution-r2, formal-review-r1
  and parent-literature reports, and original-scope.txt, are byte-identical to their copies
  under inputs/.

The exact values are in evidence.json. Checksums are identity evidence only. They are not
mathematics.

## What changed from v1

I computed the v1→v2 diff independently. Applying the author's validation/v1-to-v2.patch to a
copy of v1 reproduces v2 exactly, giving SHA256 9ed9f7dd…. My own `diff -u` differs from the
recorded patch only in where one unchanged blank line is placed within a hunk, so the recorded
patch exposes every change. The changes are:

1. Line 68: "sharp-cotype grid consequence" is replaced by "classical cotype grid bound".
2. Lines 336, 342 and 459: ",d" is replaced by "\,d" (O1).
3. Lines 803–842 (§8.3): the new classical-attribution paragraph, the reordered JLW/MN
   paragraph, and the new "same order … not an improvement … GMN Question 3" sentences (M1).
4. Lines 942–952: the new "Reproduction" paragraph (O2).
5. Lines 1061–1063: the GMN bibliography note (M1).

The theorem (lines 54–65) and Sections 2–7 (lines 105–704) are otherwise byte-identical to v1.
I nevertheless re-audited the whole proof from the v2 text, as recorded below.

## M1 closure, checked against the GMN primary

I read GMN arXiv 1003.0279v3 §1.3 myself: lines 377–505 of the local text, SHA256 3ffb2213…,
together with bibliography lines 1753–1791. Each new claim of §8.3 (lines 806–817) and
bibliography lines 1061–1063 was checked as follows.

- **Grid notation.** "[m]^d_∞ denotes {0,…,m}^d with the sup metric" matches GMN line 450
  exactly.
- **Bourgain's grid theorem.** "Bourgain's 1987 grid theorem gives distortion ≳_Y d^{1/q} for
  embeddings of [⌈d^{1+1/q}⌉]^d_∞ into a Banach space Y of Rademacher cotype q" matches GMN
  lines 451–455.
  - GMN ref [3] is Bourgain, *Remarks on the extension of Lipschitz maps defined on discrete
    sets and uniform homeomorphisms*, LNM 1267, pp. 157–167, Springer 1987 (lines 1757–1759).
  - GMN writes the side as n^{1+1/q} without rounding. The ceiling is an integer reading; see
    optional O5.
- **GMN Theorem 1.2.** "GMN's Theorem 1.2 also yields this bound" matches line 455, "The same
  result follows from Theorem 1.2".
- **S_1 cotype 2.** "Tomczak-Jaegermann (1974) for cotype 2 of S_1" matches lines 404–405,
  "(for S1 see [18])".
  - Ref [18] is Studia Math. 50 (1974), 163–182 (lines 1785–1786).
  - JLW lines 169–170 independently record the same attribution.
- **Arithmetic.** I checked the order myself.
  - With N = (⌈d^{3/2}⌉+1)^d, log N = d·log(⌈d^{3/2}⌉+1) = (3/2+o(1)) d log d.
  - log log N = (1+o(1)) log d, so √(log N / log log N) = (√(3/2)+o(1))√d.
  - Bourgain's ≳ d^{1/2}, with an implied constant depending only on S_1, therefore gives
    distortion ≥ c√(log N/log log N) for an absolute c. Correct.
- **Disclosure.** The unread Bourgain and Tomczak-Jaegermann originals are disclosed both in the
  text (lines 816–817) and in the GMN bibliography entry (lines 1061–1063). This is the
  attribution route that round 1 allowed.
- **JLW/MN demotion.**
  - "The JLW/MN chain recovers this cardinality order with grid side O(√d), instead of order
    d^{3/2}" (lines 819–820) is correct.
  - "This is the same order in N as the classical bound, not an improvement of that order"
    (lines 836–837) is correct.
  - Line 68 now says "classical cotype grid bound".
  - The conclusion that any novelty is confined to the negative-type specialization (lines
    838–841) is retained. It is correct, because the classical order already exceeds the
    T117Q bi-Lipschitz corollary for general metrics.
- **No residual recent-origin wording.** I searched v2 for "sharp", "stronger", "classical",
  "cardinality", "Bourgain", "Tomczak" and "recent".
  - No remaining sentence attributes the cardinality order to JLW or to 2026.
  - Line 100 ("including the sharp metric-cotype grid bound") names the compared operation and
    implies no origin or date. Optional O6 suggests harmonizing it.

The **retained √d/64 deduction** was re-verified against the primaries.

- **JLW Corollary 6.1.** For even m ≥ √n with m ≥ 4, the constant is 32 (s1-scale2026.txt lines
  1083–1094). Indeed (3√70 + 6)k ≤ 31.2k ≤ 32k when k ≥ √d.
- **Lower bound on D.** For a nonexpanding map of the sup-metric torus with inverse Lipschitz
  constant D, each antipodal term is at least (k/(2D))². Local jumps have sup distance at most
  1. Hence d·k²/(4D²) ≤ (32k)², so D ≥ √d/64. Correct.
- **MN Theorem 1.12.** The proof (mn2008.txt lines 3030–3048) has exactly this structure, with
  MN Theorem 4.1 in place of the sharp inequality. "With the new sharp inequality substituted"
  is accurate.
- **MN Lemma 6.12.** The third assertion (lines 2773–2790) embeds Z_{2m}^n with distortion 1+6ε
  into [m+1]^{(⌈1/ε⌉+1)n}_∞. With ε = 1 the distortion is 7, the side is k/2+1 and the
  dimension is 2d. So "constant distortion … side O(k) and dimension O(d)" is correct.
- **Resulting grid bound.** The grid has log N ≍ d log d and distortion ≥ √d/448, which gives
  c√(log N/log log N). Correct.

## The GMN Question 3 sentence (new in v2, not retained from v1)

The brief calls this comparison "retained". In fact v1 never mentions GMN Question 3 (I checked
by grep), and lines 837–838 are new. I therefore checked them as new text.

- **The question.** GMN Question 3 (lines 483–495) asks whether, for every Banach space Y of
  Rademacher cotype q, embeddings of [n^{1/q}]^n_∞ incur distortion ≳_Y n^{1/q}. For S_1 it
  asks whether the distortion of [√n]^n_∞ is ≳ √n.
- **JLW's own framing.** The JLW abstract (lines 27–29) says the paper settles the
  Mendel–Naor optimal-scaling problem for S_1 "(see also [9, Question 3])". Lines 181–188
  present Question 3 as a motivation. JLW do not state the grid corollary themselves.
- **Independent check that the chain reaches Question 3.**
  - Take N = 2d with √N an integer, and set m' = √N − 1, k = 2m'.
  - Then k ≥ max(4, √d) for large N.
  - By MN Lemma 6.12 (ε = 1), Z_k^d embeds with distortion ≤ 7 into
    [m'+1]^{2d}_∞ = [√N]^N_∞.
  - Hence c_{S_1}([√N]^N_∞) ≥ √d/448 ≍ √N.
  - Other N reduce to this case by monotonicity under isometric subgrids.
- **Conclusion.** The chain does settle the S_1 case of Question 3 positively, up to constants.
  "The sharp scale improves the grid side, addressing the S_1 case of GMN Question 3" is
  therefore accurate and does not overclaim. It also does not credit the T117Q author.
  Optional O7 suggests a more explicit form.

## Full-scope fidelity

Theorem 1.1 (lines 54–65, PDF p.1) states the frozen target exactly:

- **Metrics.** Genuine finite negative-type metrics, positive on distinct points and satisfying
  every triangle inequality (lines 47–51), with n_j → ∞.
- **Hilbert spaces.** Every complex Hilbert space H, with no dimension, separability or rank
  restriction (line 64).
- **Maps.** Every F with ‖F(x)−F(y)‖₁ ≤ d_j(x,y).
- **Averages.** Ordered uniform pair averages including the diagonal (lines 51–52, (1.1)).
- **Constants.** Constant c^{-1} and exponent 9/2.

There is no weighted-only, pseudometric, rational, efficient-construction or bi-Lipschitz
substitute. The bi-Lipschitz remark is presented as a consequence only. The statement matches
original-scope.txt (fc5a8f87…).

Method-shaped chronology (lines 85–87), the non-optimality of 9/2 (line 96) and the weaker
diagonal ℓ₁ consequence (lines 97–99) are all stated. The source scalar contraction is not
asserted to be matrix-valued (lines 79–81, 218).

## Proof audit (standalone v2 text, re-derived)

**§2, Lemma 2.1.**

- Isserlis' identity with repeated indices gives the exact pairing sum.
- The register map V with V*V = ΣX_i² ≤ I is a contraction, and so is V*. Each pairing word sum
  W_π, crossing pairings included, is a composition of contractions, so ‖W_π‖ ≤ 1. No
  positivity of individual W_π is used.
- The sum is positive as the expectation of an even power. Hence
  0 ≤ E(Σg_jX_j)^{2q} ≤ (2q−1)!! I in every dimension (E3).

**§3, Lemma 3.1.** These steps give universality before any dimension is chosen (E2).

- Truncation bias: ≤ (E|G|^{4q})^{1/2} P(|G| > 2√m)^{1/2} ≤ (Cm)^q e^{−cm} < m^{−3q}, using
  q = O(log m).
- Hoeffding: the range is 2B with B = (2√m)^{2q}, so the exponent is
  −c·m^{10q+6}·m^{−6q}/(16^q m^{2q}) = −c m^{2q+6}/16^q. The union bound over m^{2q} words
  still tends to 0.
- Norm event: SN·e^{−cm} → 0, since log SN = O((log m)²). On this event the truncated and
  untruncated empirical moments agree, so every empirical moment is within 2m^{−3q} of its
  Gaussian value.
- Error: ‖X_α‖ ≤ 1 by X_j² ≤ ΣX_k² ≤ I, so the error is
  m^{−q}·m^{2q}·2m^{−3q} = 2m^{−2q}. Then (2q−1)!! m^{−q} + 2m^{−2q} ≤ (4q/m)^q.
- Universality: the event fixes only scalars.
- Source direction events at log S = O((log m)²) are rechecked. Majority charts are unused.
- Pseudoinverse: J^TJ ∈ [N/(2m), 2N/m]·I gives ‖J^+‖ ≤ √(2m/N) ≤ 2√(m/N) and
  |J^+e_i| ≤ (2m/N)·2.

**§4, Lemma 4.1.**

- Bessel: g_j ⊗ e_k is orthonormal in L₂(γ;C^D), so ΣX_j² ≤ I.
- Positive pairing: Y = ΣA_jX_j = E[A sign A] = E|A| ≥ 0 and Tr Y = E‖A(g)‖₁.
- Operator concavity of T^{1/q}: S^{−1}ΣM_s ≤ (N(4q/m)^q)^{1/q} I ≤ 4e(q/m) I, using
  N^{1/q} ≤ e.
- Coverage: I−P_s ≤ M_s/h with h = 8eq/m gives Σ(I−P_s) ≤ S/2, so ΣP_s ≥ (S/2)I.
- Compression: Z^{2q} ≤ M_s^q, so by monotonicity Z² ≤ M_s and ‖ZP_s‖² ≤ h.
- Trace pairing: Tr(YP_s) = Tr(Y^{1/2}P_sY^{1/2}) ≥ 0 without commutation. Expanding
  Σ_jA_{s,j}X_j = Σ_ib_{s,i}Z_{s,i} gives the trace-duality bounds Nt√h and e per chart.
- Result: Tr Y ≤ 2Nt√(8eq/m) + 2e = 2√(8e) Nt√(q/m) + 2e (E8).
- The integral representation proves both fractional-power properties.

**§5, geometry with S = m^{10q}, ε = m^{−200}/S, τ = m^{−2000}/S².** I compared each step with
pinned kernel.tex lines 1–210 and repair.tex (rename A_s→B_s, P_v→𝒫_v).

- Kernel error: 2m^{−79/2} + 36m^{−77/2} + 4m^{−194}·80 log m ≤ m^{−37}, and εSN = m^{−194}.
- p, Dp, D²p: the derivative bounds √m·b·a^{−2j}E|G|^{2j} and εSN log(b/a)(2√m/a)^{2j} give
  ≤ m^{110}, with no √S (E4).
- B_s^0 and DB_s^0: these gain √S through ε^{−1/2} = m^{100}√S, giving ≤ √S m^{300}.
- Chart identities: B_sJ_s = Dp. The derivative identity (5.9) follows from
  B_s(I−JJ^+) + DpJ^+ = B_s.
- Rounding: |x−Jθ| ≤ √Nτ, |J^+x−θ| ≤ 2√mτ and |R_sx| ≤ √Nτ, so the feature error is
  ≤ m^{110}·2√mτ + √S m^{300}√Nτ ≤ √S m^{305}τ.
- Squared distances: the error is ≤ C√S m^{415}τ ≤ S m^{610}τ = m^{−1390}/S ≪ r.
- Local angles: the two error sources are C√S m^{411}τ and CS m^{605}τ, both negligible against
  (m/N) log m.
- Repair: the hypothesis is ≥ −min{r, δ(v,z), δ(y,z)}. The repair cost is 8δ(1 + log(r/δ)),
  with log(r/δ) = 1997 log m + 2 log S − log(C₀ log m) = O((log m)²). Adjacent distances are
  therefore ≤ Cτ(m/N)(log m)³.
- Genuine metric: δ > 0 within a chart and 8r between charts.
- Size: H₀ = N(1+8√m/τ) gives |V| ≤ S(H₀+1)^m = exp(Cm(log m)²), and diam ≤ Cm.
- Macro average: E|θ−η| ≥ (2m/3)/(2√m) = √m/3, so the first-chart average is ≥ cm.

**§6.**

- Smoothing: ‖H_s−f_s‖₁ ≤ c_*√m·√mλ + Cr, and the mismatch is ≤ Cr·‖ρ'‖₁/λ.
- Jumps and coefficients: each jump is ≤ Cτ(m/N)(log m)³. The distributional-gradient
  coefficients are u_{ij}/|u_i| times the surface integrals.
- Coarea: some |u_{ij₀}| ≥ 1/(2√m), so ∫|h_i'| ≤ C√m/λ. Hence τΣh(kτ) ≤ 1 + Cτ√m/λ ≤ 2, which
  gives the pointwise budget.
- Lemma 4.1 applies with e = Cm·r/λ = Cm^{−5}. Then 2√(8e)·N·C(m/N)(log m)³·√(q/m) =
  C√m(log m)^{7/2}.
- Cube lemma: θ_j = 2Φ(G_j)−1 is uniform, the coefficients 2φ/√(2/π) lie in [0,1], and the
  contraction principle (noise plus Jensen) gives the constant (π/2)√(2/π) = √(π/2) (E5).
- Hermitian dilation: ‖𝒟(B)‖₁ = 2‖B‖₁.

**§7.**

- Copies: k_v = Mw_v + e_v with e_v ∈ (0,1], so TV(μ,w) ≤ |V|/M ≤ m^{−2}. The product law has
  TV ≤ 2m^{−2}, so each expectation changes by ≤ 2C/m.
- Equilateral term: d' = d₀ + ζ1_{x≠y} is a direct sum of squared Hilbert distances, hence a
  genuine negative-type metric. With ζ ≤ d_min/m², representatives are
  (1+m^{−2})-nonexpanding.
- Order of reduction (E1, E6): separable K from the ranges of F and F*, finite-rank compression,
  representatives, dilation, the finite bound, and the trace-norm limit via finite-rank
  approximation. This covers nonseparable H.
- Constant (E7): m^m ≤ n ≤ exp(Cm(log m)²) gives log log n ≥ log m and
  √(log n) ≤ C√m log m. Hence √m/(log m)^{7/2} ≥ c√(log n)/(log log n)^{9/2}, with C = c^{−1}.

**§8 new explicit comparisons.**

- **CEE (37), p = 1.** Read at cee2023.txt lines 503–512 and 1943–1980:
  2τ^{−1}a₁/Σψ^{−1}(1/σ_i)^{−1}. (123) is pre-bi-Lipschitz, and (125) uses only the upper bound.
- **ψ^{−1} bound.** ψ^{−1}(u) ≤ 2u log(e+u), because 2u log(e+u) ≤ 2u(e+u)/e ≤ 2eu + u² and
  e ≤ e².
- **Cap.** a₁ ≤ ½Σσ_i via the coordinate path, using ρ ∈ {0,1} on edges (CEE lines 1965–1971).
  Together these give cap (8.1).
- **ψ₁,₁.** ψ₁,₁(t) = t/log(e+t) matches LWW lines 11 and 67.
- **Coordinate sum.** Σ_i|u_{ij}| ≤ √N·√(2N/m) gives C m^{3/2}(log m)³.
- **Proposition 8.1.** 2Σ_h h(k+1−h)/(k+1)² = k(k+2)/(3(k+1)). The six-point form is
  2·5 + 2·5 − 2·9 = 2.
- **Diagonal example.** (Σ‖e_je_j^*‖₁²)^{1/2} = √m and E‖Σg_je_je_j^*‖₁ = m√(2/π).

## Source and primary interfaces

- **Appendix A labels.** All 17 source labels cited in Appendix A (lines 963–990) exist in the
  pinned files I checked. The reused formulas in kernel.tex and repair.tex match §5 after the
  stated renaming. Source truth was not audited.
- **JLW** (2610.21445v1, posted 15 Oct 2026, line 10). The following are cited correctly:
  - Theorem 1.3 with (3√70 m + 6√n)² (lines 197–204);
  - Corollary 6.1 with 32 (lines 1083–1094);
  - (4.5) (line 484), Proposition 5.2 with 6√70 (lines 239 and 603);
  - Steps II–III (lines 983 and 1035).
- **MN.** Theorem 1.12 (line 422), its proof, and Lemma 6.12 are cited correctly.
- **GMN.** As above.
- **CEE.** Theorems 13 and 42 are cited correctly.
- **LWW Theorem 1.1** (lines 78–88), **KNT Theorem 34** (lines 1642–1646), **EGM §3.2 and
  Question 2** (lines 221–231), **Naor–Young Question 13**, and **NPS on commutative coordinate
  sampling** (lines 280–339) are all described accurately.

## Formal coverage

§9 (lines 906–940) matches formal-review-r1:

- Lean 4.34.1 and mathlib d13f23b7…;
- 31 support and 15 control declarations, with standard axioms only;
- an exact list of covered and uncovered steps;
- a trusted cache, not rebuilt;
- eigenbasis independence not formalized;
- the abstract zero-threshold distinction;
- an explicit statement that this is not a formal proof of Theorem 1.1.

The new pointer to t117q-formal-v1/rebuild.py and its options --output, --lean and --cache
matches that script (argparse lines 26–28, SHA256 e767e8fd…). Only the dash typesetting of
those options is defective (R1).

## Attribution, rights and priority

- **Novelty wording.** "New to this project … literature priority is not claimed" appears at
  lines 41–42 and 707–711. There is no "first", Heisenberg or EGM Question 2 claim (lines
  102–103, 719–721 and 734–735).
- **Tools.** Standard tools are credited as paid.
- **JLW credit.** JLW is credited as a prior antecedent, posted October 15, before the
  candidate.
- **Classical credit.** The classical grid bound is now credited (M1).
- **Assistance.** Parent assistance is disclosed as author work, not independent review (lines
  1012–1016).
- **Licensing.** CC BY 4.0 / MIT, with third-party separation (LICENSES.md and lines
  1016–1018). Private bodies are excluded from redistribution.

## Implementation of prior objections (v2 line numbers)

| Item | Status | Location in v2 main.tex |
|---|---|---|
| Proof E1 reduction order | Implemented | 659–690 |
| Proof E2 m^(−q), m^(2q) words | Implemented | 182–200 |
| Proof E3 repeated Wick indices | Implemented | 117–132 |
| Proof E4 √S tracking | Implemented | 349–357, 392–399, 421, 440–444 |
| Proof E5 √(π/2) | Implemented | 575–605 |
| Proof E6 all-H compression | Implemented | 659–690 |
| Proof E7 c^(−1) | Implemented | 61, 71–72 |
| Proof E8 2√(8e) | Implemented | 251, 280 |
| RQ1 NPS/NY/CEE/LWW/KNT/quantum | Implemented | 713–792 |
| RQ2 bounded-search wording | Implemented | 41–42, 102–103, 707–711 |
| RQ3 JLW sharp cotype | Implemented; M1 attribution now correct | 793–904 |
| RQ4 method-shaped 9/2; weaker diagonal ℓ₁ | Implemented | 85–87, 96–99 |
| Editorial E1–E5 (r1) | Implemented | 61; 141–145, 220–223; 236–238; 991–998 |
| R2-A influence cap, L₁/S₁ symmetry, missing family | Implemented | 744–792 |
| R2-B operation-level cotype/smoothing reasons | Implemented | 877–901 |
| R2-C general-metric grid bound, negative-type limitation | Implemented with classical attribution | 66–70, 806–843 |
| R2-D all items in text, JLW 15 Oct prior | Implemented | 723–735, 794–795, 85–99 |
| R2 optional E2 JLW Bessel/dilation credit | Added | 902–904 |
| Manuscript-r1 M1 | Closed | 68, 806–841, 1061–1063 |
| Manuscript-r1 O1 differentials | Fixed; rendered correctly on p.5 and p.7 | 336, 342, 459 |
| Manuscript-r1 O2 reproduction pointer | Added, but defective as typeset (R1) | 942–952 |

## Required repair

**R1. The in-text reproduction commands print en dashes instead of `--`.**

Location: main.tex lines 945, 949 and 950 (PDF p.14, paragraph "Reproduction").

The source writes `\texttt{python3 -B build.py --output /var/tmp/NEW-PDF-BUILD}`,
`\texttt{--output}`, `\texttt{--lean}` and `\texttt{--cache}`. With T1-encoded Latin Modern
typewriter, `--` is typeset as the en-dash ligature. Three independent observations confirm
this:

- **Text layer.** Text extracted from the byte-identical rebuilt PDF (pdftotext, identical to
  the packet's validation/main.txt) contains U+2013 in all four places, at text lines 779,
  782 and 783.
- **Rendering.** A 200 dpi render of p.14 shows a single dash before `output`, `lean` and
  `cache`.
- **Behaviour.** On a /var/tmp copy, I ran the command exactly as printed,
  `python3 -B build.py –output …`. Its argparse exits with code 2 ("the following arguments
  are required: --output") and writes nothing.

So the sentence "The accompanying packet README gives the PDF command" is false as printed. The
README's actual command uses `--output`, and the printed one does not run.

Why this is required rather than optional:

- NEW-TEN line 15 makes reproducibility instructions part of the accepted manuscript.
- Round 1 accepted package-level instructions, and the in-text pointer was optional. But once
  the manuscript prints commands, they must be correct.
- It is a new factual error introduced in v2, not a style preference.

The defect does not touch the mathematics, scope, attribution or formal-coverage claims. The
author's visual QA and the parent preflight inspected layout and did not check glyph identity.

Acceptable fixes (either one):

- (a) Write `\texttt{-{}-output}`, `\texttt{-{}-lean}` and `\texttt{-{}-cache}` (or use
  `\verb|--output|` and similar) at lines 945, 949 and 950. Then rebuild, and confirm that
  the PDF text layer contains ASCII `--output`, `--lean` and `--cache`.
- (b) Remove the literal commands and refer to the packet README and the formal packet README
  only. This is the package-level state that round 1 already accepted.

No other change is required.

## Optional editorial (not required)

- **O3 (carried).** NPS, CEE and GMN are cited as preprint versions. JLW's bibliography lists
  GMN as J. Funct. Anal. 260 (2011) 164–194 and CEE as Analysis & PDE 16 (2023) 571–612. I
  read these entries in JLW but did not verify them independently.
- **O4 (carried).** R2 optional E1 (expander/Fréchet remark) and E3 (NPS S_1→S_q
  nonreduction) remain optional and unnecessary.
- **O5.** GMN writes Bourgain's grid side as n^{1+1/q} without rounding. The manuscript's
  ⌈d^{1+1/q}⌉ is a harmless integer reading that does not affect the order. "Side of order
  d^{1+1/q}" would follow the source more literally.
- **O6.** Line 100 still reads "including the sharp metric-cotype grid bound". It names an
  operation, not an origin or a date, and §8.3 and line 68 are explicit, so it is not
  misleading. "The classical and sharp-scale metric-cotype grid bounds" would match M1 more
  closely. The same applies to the historical phrase "stronger general-metric grid
  consequence" in Appendix line 1008.
- **O7.** The Question 3 sentence could be made more explicit. Through MN Lemma 6.12, the chain
  gives c_{S_1}([⌊√n⌋]^n_∞) ≳ √n, which settles the S_1 case of GMN Question 3 positively up
  to constants. JLW point to Question 3 but do not state this grid corollary. "Addressing" is
  already accurate.

## Build and page inspection

I copied the packet to /var/tmp and rebuilt it with the author's build.py, which I had read
first. The build used Tectonic 0.17.0 (binary SHA256 a98aa59a…, matching the receipt) at
SOURCE_DATE_EPOCH 1792281600.

- The PDF is byte-identical to the packet's main.pdf (adcc1c36…) and has 16 pages.
- pdftotext output is byte-identical to the packet's validation/main.txt.
- The log has no warnings, no overfull boxes and no undefined references. There is no "??"
  in the text.
- pdffonts lists 24 fonts, all embedded and subset.

All 16 pages were rendered at 80 dpi and viewed one by one, with a 200 dpi zoom of p.14.

- There is no clipping or overlap.
- The O1 differentials now display as dσ, dt and dℓ.
- The new §8.3 text is on p.12 and the bibliography note on p.16. Both are clean.
- The only rendering defect is R1.

## Limits

See reading-limits.md. Build, identity and control results are identity and build checks only.
They are not mathematical evidence and were not used as such. The mathematical verdict rests on
reading the proof.

## Package

Members:

- review.md;
- reading-limits.md;
- evidence.json;
- verify_review.py;
- review_controls.py;
- controls-result.json, generated on /var/tmp copies of the pre-final seal;
- MANIFEST.json, which seals the others.

Verify with `python3 -B verify_review.py verify <dir> --anchor <SHA256 of MANIFEST.json>`,
taking the anchor from outside the package. Optionally add `--repo <openai-proof-research
root>` to recheck the immutable external inputs listed in evidence.json.

The final seal adds only controls-result.json to the pre-final base. Final positive and
wrong-anchor checks are reported outside the package.
