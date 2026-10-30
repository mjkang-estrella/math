# T117Q manuscript review, round 1

Role: independent manuscript gate (Factory Opus 5.5). Source theorems at OpenAI/math
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated; new deductions and exact
interfaces were audited. No acceptance, count, ledger, staging, commit, author-packet
edit, upload or publication action was taken. No nested agent was used. Prior gate
verdicts were read as context and were not substituted for this gate.

## Verdict

**REPAIR_REQUIRED_T117Q_MANUSCRIPT** (not PASS_FULL_MANUSCRIPT_T117Q).

There is exactly one required repair, M1. It is an attribution repair in the
general-metric comparison (Section 1 after Theorem 1.1, and Section 8.3). It does not
affect the theorem, its proof, the scope, or the manuscript's own conclusion that no new
general-metric bi-Lipschitz bound is claimed.

The mathematics passes. The standalone proof of the full frozen statement is complete and
correct as written. I found no proof gap, no unpaid factor and no scope narrowing. All
prior required objections (proof E1–E8, contribution RQ1–RQ4, round-1 editorial
E1–E5, R2-A–D) are implemented in the manuscript text. The formal-coverage statement is
accurate. The PDF rebuilds byte-identically, and all 16 pages were inspected.

## Inputs authenticated (identity only)

All anchors from the brief were recomputed as SHA256 and match:

- manuscript manifest 1a127b60…e982, main.tex e9bd0498…ff9f, main.pdf 634aeabf…a76d
  (16 pages; TeX has 1035 lines plus trailing newline);
- author r59 MANIFEST 053986e5…8ae2, candidate e32f7a12…aea4, original-scope fc5a8f87…fe36;
- proof-r1 bb6941a2…3cea; contribution-r1 6d6366df…5013; parent literature
  manifest c93929fe…deb8 and response d697cfcb…eb22; contribution-r2 855f7729…c4c0;
  formal-v1 b741e2d7…9b37; formal-review-r1 98fde2d1…9ae4.

The author verifier accepts the manuscript packet with the external anchor (exit 0) and
rejects a zero anchor (exit 1). The author's 15 integrity controls were replayed on a
/var/tmp copy. Only the positive case was accepted, and each rejection gave its expected
reason. The nine copied source117-1 blobs were recomputed as Git blob ids. All nine match
sources/preprints-tree.json (SHA256 eeecc1da…, 13223 entries, not truncated). Exact
values are in evidence.json. Checksums are identity evidence only, not mathematics.

## Full-scope fidelity

Theorem 1.1 (main.tex lines 54–65, PDF p.1) states the frozen target exactly:

- genuine finite negative-type metrics (strict positivity and all triangle inequalities,
  lines 47–51), with n_j → ∞;
- every complex Hilbert space H, with no dimension, separability or rank restriction
  (line 65);
- every map with ||F(x)−F(y)||_1 ≤ d_j(x,y);
- ordered uniform pair averages including the diagonal (lines 51–52, display (1.1));
- constant c^{-1} and exponent 9/2.

There is no weighted-only, pseudometric, rational, efficient-construction or
bi-Lipschitz substitute. The bi-Lipschitz remark (lines 66–72) is presented as a
consequence only. It matches original-scope.txt, including c^{-1} (proof E7). Lines
86–87 state that the exponent and chart number were chosen by the method before the
freeze, and that the freeze preceded the complete proof but not the method (RQ4).

## Proof audit (standalone manuscript)

I re-derived each step from the manuscript text, not from the prior reports.

- **Wick register (§2, Lemma 2.1).** Isserlis' identity covers repeated indices (E3).
  Each pairing, including crossing pairings, is a composition of contractive register
  operations under Σ X_j² ≤ I. This gives the Loewner bound (2q−1)!! I in every
  dimension.
- **Universal directions (§3, Lemma 3.1).** The scalar monomial coefficients are matched
  before any matrix dimension is fixed.
  - Truncation is at |G| ≤ 2√m.
  - Hoeffding gives the exponent c·m^(10q+6)·m^(−6q)/(16^q m^(2q)), followed by a union
    bound over m^(2q) ordered words.
  - The averaged error m^(−q)·m^(2q)·2m^(−3q) = 2m^(−2q) is absorbed by
    (2q−1)!! m^(−q) + 2m^(−2q) ≤ (4q/m)^q (E2).
  - The source direction events hold with S = m^(10q), because log S = O((log m)²).
- **Spectral selector (§4, Lemma 4.1).**
  - Bessel's inequality gives Σ X_j² ≤ I.
  - The pairing Y = E|A(g)| ≥ 0 is positive, with Tr Y = E||A(g)||_1.
  - Concavity and monotonicity of T^(1/q) follow from the integral representation
    (lines 291–300).
  - Coverage Σ_s P_s ≥ (S/2)I and the compression bound ||Z P_s||² ≤ h hold.
  - The trace pairing with noncommuting P_s uses only Y ≥ 0 (Tr(Y P_s) =
    Tr(Y^(1/2) P_s Y^(1/2))). Expanded summands are bounded in absolute value by duality.
  - Constant: (S/2) Tr Y ≤ SN·t√h + Se with h = 8e·q/m gives
    Tr Y ≤ 2√(8e) N t √(q/m) + 2e (E8).
- **Geometry (§5).**
  - εSN = m^(−194).
  - p, Dp and D²p are bounded by m^(110) with no √S factor (E4).
  - B_s and DB_s are bounded by √S m^(300); the feature error is √S m^(305) τ.
  - Angle error terms are C√S m^(411) τ and CS m^(605) τ. With τ = m^(−2000)/S², both
    are negligible.
  - The repair logarithm is O((log m)²), giving (log m)³ adjacency and
    |V| ≤ exp(Cm(log m)²).
  - I checked each against the source kernel/repair/metric formulas, including the
    renaming A_s→B_s, Q_s→R_s, P_s→𝒫_s.
- **Contraction (§6).**
  - The pointwise coefficient budget combines with Lemma 4.1 to give
    C√m(log m)^(7/2).
  - The Banach-valued cube lemma has constant (π/2)·√(2/π) = √(π/2) (E5).
  - Hermitian dilation handles complex values.
- **Completion (§7).**
  - Uniform copies give TV ≤ m^(−2).
  - The added equilateral term ζ keeps the metric genuine and of negative type.
  - Arbitrary H is handled in the order: separable range, finite-rank compression,
    representatives, dilation, finite bound, trace-norm limit. This covers nonseparable
    H (E1, E6).
  - Conversion: log log n ≥ log m and √(log n) ≤ C√m log m give exponent 9/2.

The new §8 deductions were also verified:

- the CEE (123)/(125) pair-average reading;
- the cap ψ^(−1)(u) ≤ 2u log(e+u), since e + 2u log(e+u) ≤ (e+u)²;
- a_1 ≤ ½ Σσ_i, which gives cap (8.1);
- the coordinate-sum estimate C m^(3/2)(log m)³;
- Proposition 8.1: E|U−V| = k(k+2)/(3(k+1)), and the six-point form equals 2;
- the diagonal smoothing example, with l_2 sum √m and E||Σ g_j e_j e_j^*||_1 = m√(2/π);
- the JLW/MN chain. From d(k/(2D))² ≤ (32k)², we get D ≥ √d/64.

## Source and primary interfaces

Appendix A (lines 925–960) lists each reused source label. I read the operative
passages of directions.tex, directions-proof.tex, kernel.tex, repair.tex, metric.tex,
contraction.tex and reduction.tex lines 100–200, and confirmed:

- the source contraction uses exponent 3, S = m³ and scalar majority charts;
- the manuscript does not use the majority charts and re-proves every modified bound.

Primary passages were checked against the stated readings. The text hashes are listed in
evidence.json.

- **JLW** (arXiv 2610.21445v1): Theorem 1.3 has constant (3√70 k + 6√d)² with ε uniform
  on {−1,0,1}^d. Corollary 6.1 has constant 32 for even k ≥ max(4,√d). (4.5),
  Proposition 5.2 (6√70) and Steps II–III are cited correctly. The posting date of
  15 October 2026 is credited.
- **MN:** the Theorem 1.12 argument and the third assertion of Lemma 6.12 (Z_{2m}^n into
  [m+1]^{(⌈1/ε⌉+1)n}_∞, distortion 1+6ε) are cited correctly.
- **CEE:** Theorem 13 and proof (122)–(125) are read correctly, and Theorem 42 is
  correct.
- **Other primaries:** LWW Theorem 1.1, KNT Theorem 34, Naor–Young Question 13, NPS
  lines 280–339 and EGM Section 3.2 are described accurately.

## Formal coverage

Section 9 matches formal-v1 and formal-review-r1:

- Lean 4.34.1 and mathlib d13f23b7…;
- 31 support and 15 control declarations, with standard axioms only;
- an exact covered/uncovered list, and the trusted dependency cache;
- eigenbasis independence is not formalized;
- the zero-threshold distinction is explained;
- it states plainly that this is not a formal proof of Theorem 1.1.

## Attribution, rights and priority

- **Novelty wording.** "New to this project; a bounded search found no antecedent;
  literature priority is not claimed" appears at lines 41–43 and 707–712. There is no
  "first", Heisenberg or EGM Question 2 claim (lines 102–103, 719–721, 734–735).
- **Tools.** Standard tools are credited as paid: Haagerup–Pisier and Buchholz,
  Seymour–Zaslavsky, Pisier, and the parallel JLW devices.
- **Assistance and licensing.** Parent assistance is disclosed as author work. The CC BY
  4.0 / MIT license statement and the third-party separation are present.
- **Gap.** The one attribution gap is M1.

## Implementation of prior objections

| Item | Status | Location (main.tex lines) |
|---|---|---|
| Proof E1 reduction order | Implemented | 659–690 |
| Proof E2 m^(−q), m^(2q) words | Implemented | 182–200 |
| Proof E3 repeated Wick indices | Implemented | 117–132 |
| Proof E4 √S tracking | Implemented | 357, 392–399, 421, 440–445 |
| Proof E5 √(π/2) | Implemented | 575–601 |
| Proof E6 all-H compression | Implemented | 659–690 |
| Proof E7 c^(−1) | Implemented | 63, 70–72 |
| Proof E8 2√(8e) | Implemented | 251, 280 |
| RQ1 NPS/NY/CEE/LWW comparisons | Implemented | 713–792 |
| RQ2 bounded-search wording only | Implemented | 41–43, 102–103, 707–712 |
| RQ3 JLW sharp cotype | Implemented, with attribution gap M1 | 793–886 |
| RQ4 method-shaped 9/2; weaker diagonal ℓ1 | Implemented | 86–87, 96–99 |
| R1 editorial E1–E5 | Implemented | 63; 141–145, 220–223; 235–238; 963–965; 961–963 |
| R2-A influence cap; L1/S1 symmetry; missing family | Implemented | 744–792 |
| R2-B cotype/smoothing operation-level reasons | Implemented | 859–883 |
| R2-C stronger general-metric grid bound | Implemented as requested; precise attribution gap M1 | 66–69, 805–826 |
| R2-D KNT, EGM, JLW priority, method shape | Implemented | 723–735, 794–795, 86–99 |
| R2 optional E2 JLW Bessel/dilation credit | Added | 884–886 |
| R2 optional E1, E3 | Not added; remain optional | — |

## Required repair

**M1. Credit the classical general-metric S_1 grid bound.**

Locations:

- main.tex lines 66–69 (PDF p.1, paragraph after Theorem 1.1): "weaker than the
  sharp-cotype grid consequence";
- lines 805–826 (PDF p.12, §8.3), from "The classical grid nonembedding deduction" to
  "under the bounded-search qualification above";
- the bibliography, lines 991–1034.

The manuscript derives the general-metric bound c√(log 𝒩/log log 𝒩) for S_1 only through
JLW Corollary 6.1 (posted 15 October 2026) and calls it the "sharp-cotype grid
consequence". The section it cites, GMN §1.3 (gmn2011.txt lines 450–455 and 403–407,
refs [3] and [18]), records the following:

- Bourgain (LNM 1267, 1987) proved that any embedding of the grid [n^(1+1/q)]^n_∞ into a
  Banach space with Rademacher cotype q has distortion ≳_Y n^(1/q).
- GMN's own Theorem 1.2 gives the same.
- S_1 has Rademacher cotype 2 (Tomczak-Jaegermann, 1974).

With q = 2, 𝒩 = (n^(3/2)+1)^n gives log 𝒩 = (3/2 + o(1)) n log n. The resulting bound is
≳ √n ≍ √(log 𝒩/log log 𝒩), which is already the order the manuscript derives. The author
lists GMN lines 377–505 as read.

So the general-metric 𝒩-point rate into S_1 predates the October 2026 sharp-scale
inequality by decades. The sharp scale improves the grid side, from n^(3/2) to order √n,
which is the GMN Question 3 regime. It does not improve the order of the 𝒩-point bound.
The current wording therefore misattributes the strongest known general-metric
comparator and its date.

The required change is attribution only:

- Credit Bourgain's grid theorem and GMN Theorem 1.2 (as recorded in GMN §1.3), together
  with S_1 cotype 2 (Tomczak-Jaegermann), for the c√(log 𝒩/log log 𝒩) general-metric
  bound.
- State that the JLW/MN chain recovers this order with grid side O(√d).
- Adjust the line-68 label.
- Either add the two bibliography entries, marked as cited through GMN if their bodies
  are not read, or attribute explicitly through GMN §1.3.

Retain the existing JLW credit, the verified √d/64 deduction, and the conclusion that any
novelty of the bi-Lipschitz corollary is confined to negative-type metrics under the
bounded-search qualification. The conclusion is unchanged, because the classical bound
is also stronger than the manuscript's bi-Lipschitz corollary.

I did not read the Bourgain or Tomczak-Jaegermann bodies. The repair relies on GMN's
explicit statement in the cited section, not on an unread primary.

## Optional editorial (not required)

- **O1.** Three literal commas appear before differentials where a thin space was
  intended. The meaning is unambiguous.
  - Line 336 (PDF p.5, display (5.1), ",dσ").
  - Line 342 (PDF p.5, the definition of c_*, ",dt").
  - Line 459 (PDF p.7, display (5.9), ",dℓ").
  - The parent preflight's line numbers 322/328/433 do not match the frozen TeX. The
    correct lines are 336/342/459.
  - Fix: replace "," by "\,".
- **O2.** §9 or Appendix A could point to the packet build command and the Lean rebuild
  entry point. Reproducibility instructions currently live in the packet README and the
  release REPRODUCTION.md. This meets NEW-TEN line 15 at the package level and matches
  the accepted R034 precedent.
- **O3.** NPS, CEE and GMN are cited as preprint versions. Published versions could be
  added; I did not verify their bibliographic details.
- **O4.** R2 optional E1 (expander/Fréchet remark) and E3 (NPS S_1→S_q nonreduction)
  remain optional and are not needed.

## Build and page inspection

The packet was copied to /var/tmp and rebuilt with Tectonic 0.17.0 (binary SHA256
a98aa59a…) at SOURCE_DATE_EPOCH 1792281600.

- The PDF is byte-identical (634aeabf…), 16 pages.
- The log is clean: there are no undefined references and no "??".
- pdftotext output is identical to the packet's validation/main.txt (b1d847bd…).
- All 23 fonts are embedded and subset.

All 16 pages were rendered at 80 dpi and viewed. There are no layout defects other than
O1.

## Limits

See reading-limits.md. The diagnostics are identity and build checks only. They are not
mathematical evidence and were not used as such.

## Package

Members:

- review.md;
- reading-limits.md;
- evidence.json;
- verify_review.py;
- review_controls.py;
- controls-result.json;
- MANIFEST.json, which seals the others.

Verify with `python3 -B verify_review.py verify <dir> --anchor <SHA256 of MANIFEST.json>`,
taking the anchor from outside the package. Optionally add `--repo <repo root>` to
re-check the frozen manuscript and prior-gate anchors recorded in evidence.json.

controls-result.json records review_controls.py run on /var/tmp copies. Each copy was
sealed before the final seal, and the final seal adds only that file. Final positive and
wrong-anchor checks are reported outside the package.
