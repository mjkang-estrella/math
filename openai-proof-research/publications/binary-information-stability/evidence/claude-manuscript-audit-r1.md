# Manuscript audit R1: Dimension-free stability of binary-information contraction

Reviewer: Claude Opus 5.5 (review sub-agent, assigned by T3 Code). Date: 2026-10-13.
This is an AI audit, not human peer review. It checks the new deductions in the
manuscript against the pinned upstream statements; upstream truth is stipulated
(`openai-proof-research/AGENTS.md`).

## 0. Verdict

**REPAIR.** No mathematical error, missing hypothesis, or broken limit step was
found. The proofs of Theorems 1.1, 1.2 and 1.3 go through as written, given
Assumption 2.1. The manuscript must still fix two literature and attribution
gaps before publication (P1, P2). Items P3 to P5 are recommended but not
blocking. No BLOCK item was found.

## 1. Audited objects

Package: `openai-proof-research/publications/binary-information-stability/`
(worktree branch `publication/prime-predecessor-paper`; the package is untracked).
Hashes were recorded at the start and rechecked before this report was written,
and they are unchanged.

| File | SHA256 |
|---|---|
| `main.tex` | `59a390b9e7e94276003b131cf08a743a51d70a233f51d9c00dccb8f650fa6051` |
| `compact.tex` | `c75492e8d02d4993ae0f6fac77c3e5d172fd36bf4f07ab81a20d9eec8c3b091b` |
| `gaussian.tex` | `4bf53a5466f6102d7445ab145510f23e53fb2d57d7d70b3ea01e1a7e37eb5fa4` |
| `endpoint.tex` | `307b4077620d33777e9b1bf96a8803f2105f5d273c500de3d0a772bdc2066260` |
| `production.tex` | `f358eb92683dea80ac2f67887fc93f6b3f3d7427fb534ca3f9739e7ba8000707` |
| `tmp/main.pdf` (15 pp.) | `e7f987f001a653686393c0fe2ce357c5d31cdf790a9a2905425ebbad2e5dfdae` |

Pins: upstream `openai/math` at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`;
research `mjkang-estrella/math` at `d513e308d86a38004d78bab9b9e88532e92bf56c`
(from `evidence/sources.json`). The staged upstream copies in `tmp/upstream/`
pass `sha256sum -c SHA256SUMS`: main `ad04285e…`, scalar `03b64ba1…`,
canonical `fc449aa1…`, capacity `f0a33b2c…`, reserve `2b4c8b10…`,
thinning `c52291a2…`, upgrade `2c0d5677…`, flow `9065dd3b…`.

Nothing in the package was modified. The audit wrote only this file and
`tmp/audit-build/`, `tmp/claude-r1/`.

## 2. Assumption 2.1 versus upstream statements

Each item was matched against the upstream TeX statement (not a catalogue
summary).

| Item | Upstream label | Result |
|---|---|---|
| (1) | `main:soft`, `upgrade:production` | Matches. The manuscript's `D(u)` equals upstream `E[V(g) N g]` for interior `g`. |
| (2) | `scalar:entropy-bounds`, `scalar:profile-convexity`, `scalar:curvature-growth`, `scalar:scaled-curvature` | Matches: `t^2/2 ≤ ψ ≤ L t^2`, `F''≥4/3`, `e^{-2J}F''` increasing, `1/2 ≤ (L−J)^2 F'' ≤ 4L^2/3`, and `S` convex, nondecreasing and C¹ after zero extension. |
| (3) | `capacity:onebit` | Matches, including the range `|m|+|d|<1` and `J<αL`. |
| (4) | `canonical:priced`, `canonical:coverage` | Matches: the optimizer is unique, has exact entropy, and its core is interior with log variables `z,w`. |
| (5) | `reserve:joining`, `upgrade:joining` | Matches, including `e_a,e_b>0` and both `P=B` and `P=Φ`. |
| (6) | `reserve:geometry`, `thinning:window` | Matches, including `x_c≥0`, `d_c>0`, `λ∈(0,1]`, and `b_*=log(1+x)`. |

Section 2 re-derives every proof-internal fact that the earlier source audit
flagged (`claude-source-audit.md` R1(a)–(h)). This includes the two retained
losses (2.2) and (2.3), η, Ξ(L/2), the entropy ratio (2.6), and the canonical
two-geometry classification. The manuscript also uses the stated `F''≥4/3`.
R2 (full proofs of L131/M290/transfer/Borell) and R3 (explicit `c`, existential
`C`) are addressed in the text. R4 (notation) is mostly addressed; see P5.

## 3. Proof audit

Every line of the five TeX files was read against Assumption 2.1.

- **Section 2 (inputs, margins).** `δ0=2−4L²≈0.0782>0`. In (2.2), `κ≥λ²d_c²/8`
  holds because `p≤2` in the geometry input. The path derivatives
  `λI'=I−A_*` and `λν'=ν−A_*−κ` are correct. Integrating `(T/λ)'` gives the
  stated bound. The Euler identity behind (2.3) holds, and the `C¹` seam
  remark is needed and sufficient. For (2.4), the tangent inequality and
  `c_m≤m²k_0` give `B_m−F≥m²Ξ`. η>0: the chain
  `2h²F'≥(4−1/L)h²+h≥L²+L/4>M≥h²F''` is correct for `h≥L/2`
  (0.6537 > 0.6406). (2.6): the derivative identity with
  `G(v)=cosh²v−v²` is correct.
- **`compact.tex`.** The local coercivity lemma, the joining-law compactness
  lemma (lower semicontinuity of the extended cost, with the endpoint pairs
  excluded), cube sorting with (compression), and the marked-coordinate
  argument were checked. The quantifier order is correct: constants are fixed
  before the contradiction sequence. Hypercontractivity is cited to
  Bonami and Beckner.
- **`gaussian.tex`.** Translation strictness (Lemma `gaussstrict`) requires a
  nonconstant kernel with `0<I<L`, and the uses satisfy both. The scalar
  strictness `k>r²(1−b)/(1−r²b)` holds. Borell convex order (Cor.
  `gaussgap`): the layer-cake and stop-loss argument with upper rays is valid,
  since [MN, Thm 1.1] is stated for lower half-spaces and the two forms agree
  by symmetry. The MOO transfer was checked: the fourth-moment constant
  `9^{d−1}` is correct for derivative polynomials of degree ≤ d−1, and the
  two-point inequality `E(A+XB/√3)^4≤(A²+B²)²` holds for both Rademacher and
  Gaussian `X`. The mollification order (`j→∞`, then `τ↓0`) and the order of
  choices (gap, then `d`, then `j`) are correct. The sharpness expansion
  `c(ε)=a−ε²/(2(1−a²)V(a))+O(ε⁴)` and the `ε²` coefficient of `Δ_r` were
  re-derived by hand and agree.
- **`endpoint.tex`.** The endpoint spike Bregman payment and the distance test
  were checked. The bounds retain the endpoint entropy and do not assume an
  interior margin, which matches the abstract's claim of "no pointwise
  interior margin".
- **`production.tex`.** For eq. (c), `c=½min{1/6, B1/C1, η, Ξ(L/2)/L²}`
  ≈ 1.650×10⁻³, and `B1/C1` is the binding term. The Hessian determinant
  `2cJ²(F''−6cm²)` is correct and nonnegative because `6c≤1/2<4/3`. The
  one-corner payment (corebias) follows from the perspective of the convex
  function `F−μJ²/2`, which vanishes at 0. The flag chain rule is correct.
  In the original-child joining, `d=0` is handled by convexity; for `d>0`,
  the actual law is feasible for `K`, and joint convexity applies at the
  individual child budgets. The base case `P_m(0)=0` holds because
  `H(m)≥L(1−m²)`. The boundary-valued limit and the uniform-bias estimate
  (uniformbias) are correct. The one-bit sharpness expansions
  `b(a)²=ha²−(2/3)m²a⁴` and `Δ=r²(1−r²)m²a⁴/(3h)` are correct.
- **Abstract and introduction.** Every claim is supported. The abstract's
  "uniformly over finite cube dimensions", "exponent four necessary",
  "arbitrary [−1,1]-valued kernels" and "no mean restriction" correspond to
  Thms 1.1 and 1.2 and their proofs. The production claim is supported, and
  is in fact stronger than stated; see P3.

## 4. Independent checks

Script `tmp/claude-r1/checks.py` (sha256 `c477a23d…`), run with sympy 1.14.0.
Output in `tmp/claude-r1/checks.out` (sha256 `c1f2497e…`). **26/26 PASS.**

- **Identities.** Checked symbolically or to 30 digits: the reserve Euler
  identity, the thinning path derivatives, the quartic bracket identity and its
  lower bound `(m²+1−κ)/12`, the constant Walsh coefficient `a²q`, the `φ'`
  formula, and `det Hess G`.
- **Series.** Checked: the one-bit information series, `b(a)²`, the one-bit
  deficit, `ψ(ra)−r²ψ(a)`, `k`, and `Q11` (including `2r²(1−r²)/3` at `m=0`).
- **Signs.** The sign of `K0'` was checked, and `K0>0` on a grid
  (min 1.67e−7). Scalar strictness was checked on a 200×200 grid
  (normalized min 4.17e−6).
- **Constants.** `δ0=0.0781879`, `η≈0.229451`, `Ξ(L/2)≈0.0167907`,
  `c≈0.00165007`, and `L²+L/4=0.65374 > M=0.640604`.
- **Random tests.**
  - The `E_λ` bound (20000 samples): min slack 2.6e−5.
  - (eq:added) (20000 samples): min relative slack 0.75.
  - (eq:newcorner) (3000 samples): min slack 9.3e−11.
  - Theorem 1.3 on 400 random fields with `n≤4`: min slack 7e−16. The
    near-zero slack is expected, because mean-zero dictators give equality in
    `D≥F(I)` and the `m²` term vanishes there.

Numerical checks are sanity evidence, not proof.

**Rebuild.** I ran `tectonic -X compile main.tex --outdir tmp/audit-build --keep-logs`.
The log shows no warnings, no undefined references, and no overfull boxes. The
rebuilt PDF hash differs only because of the embedded timestamp. The
`pdftotext` output is identical to the shipped `tmp/main.pdf` and contains no
`??`.

## 5. Literature checks

- **Ky–Tran arXiv:2609.31797v1.** This is Boolean stability relative to the
  dictator. The manuscript's statement (line 117) is accurate.
- **Mossel–Neeman arXiv:1210.4126v3, Thm 1.1.** This is Borell's inequality
  with lower half-spaces, which is equivalent to the upper-ray use by symmetry.
  The citation is correct.
- **DLMF 4.36.3.** The coth partial fraction matches its use in `gaussian.tex`.
- **Staged research records (i336 literature, i334 profile comparison).**
  These credit:
  - Chen–Gohari–Nair, arXiv:2502.10019v2;
  - Chen–Gohari–Javanmard–Lin–Mirrokni–Nair–Woodruff, arXiv:2609.24931v2 §9,
    for production for arbitrary arrays with a mean-dependent hybrid profile;
  - Heilman–Tarter, arXiv:2011.05583v2 (Lemma 5.1, eqs. 9–11), as the
    translation and second-variation predecessor;
  - Kramer–Saglam, Yu, and Friedgut–Kalai–Naor.

  I confirmed that the three arXiv identifiers exist with these titles:
  - 2502.10019: "A Differential Equation Approach to the Most-Informative
    Boolean Function Conjecture" (Chen, Gohari, Nair);
  - 2609.24931: "A Proof of the Most Informative Boolean Function Conjecture";
  - 2011.05583: "Three Candidate Plurality is Stablest for Small Correlations"
    (Heilman, Tarter; Forum Math. Sigma 9 (2021), e65).

  **None of these three is cited in the manuscript.**

## 6. Repairs

### P1 (required): credit the production and induction predecessors

The abstract says "We also strengthen the entropy-production inequality".
Theorem 1.3 is proved by induction through the exact production split
(`production.tex` 118–119). The project's own literature record credits
arbitrary-array production with a mean-dependent profile to arXiv:2609.24931 §9,
and the differential-equation and induction approach to arXiv:2502.10019. The
manuscript cites neither paper. A reader therefore cannot tell what the new
`(E u)²I(u)²` term adds beyond them. The i334 comparison, re-derived in the
source audit, shows that the displayed hybrid profile of 2609.24931 equals
`F(I)` on a small-information interval at some fixed means. This is exactly
where the new term is positive.

Replace `main.tex` lines 119–122:

```tex
The joining method and sharp comparison curve are credited to
\cite{OpenAI}. We use classical hypercontractivity, Borell's two-set
inequality, and the low-influence replacement method of
\cite{MOO}. No priority assertion is needed for these conditional results.
```

with

```tex
The joining method and sharp comparison curve are credited to
\cite{OpenAI}. A differential-equation approach to the most-informative
Boolean function conjecture appears in \cite{CGN}, and an entropy-production
inequality for arbitrary arrays with a mean-dependent profile is proved in
\cite[Section~9]{CGJLMNW}. That profile reduces to $F(\cI)$ on an interval of
small information for some fixed nonzero means. Theorem~\ref{thm:production}
adds a positive multiple of $(\E u)^2\cI(u)^2$ uniformly in that regime.
The second-variation computation along translations in
Section~\ref{sec:gauss} follows the pattern of \cite[Lemma~5.1]{HT}.
We use classical hypercontractivity, Borell's two-set
inequality, and the low-influence replacement method of
\cite{MOO}. No priority assertion is needed for these conditional results.
```

Add to the bibliography (alphabetical placement is the author's choice):

```tex
\bibitem{CGN} Z.~Chen, A.~Gohari, and C.~Nair,
\emph{A differential equation approach to the most-informative Boolean
function conjecture},
\href{https://arxiv.org/abs/2502.10019v2}{arXiv:2502.10019v2}.
\bibitem{CGJLMNW} Z.~Chen, A.~Gohari, A.~Javanmard, Lin, V.~Mirrokni,
C.~Nair, and D.~P.~Woodruff,
\emph{A proof of the most informative Boolean function conjecture},
\href{https://arxiv.org/abs/2609.24931v2}{arXiv:2609.24931v2}, 2026, Section~9.
\bibitem{HT} S.~Heilman and A.~Tarter,
\emph{Three candidate plurality is stablest for small correlations},
Forum of Mathematics, Sigma \textbf{9} (2021), e65;
\href{https://arxiv.org/abs/2011.05583v2}{arXiv:2011.05583v2}.
```

Before publication, the author must confirm three things against the full
papers, which I did not read:

- the first-name initials, especially Lin's, which I could not confirm from
  the abstract pages;
- that 2502.10019 is the right credit for the local-to-global induction;
- that the "some fixed nonzero means" sentence matches §9 of 2609.24931 as
  stated.

If any of these does not hold, weaken the sentence to "compare
\cite[Section~9]{CGJLMNW}". Do not drop the citation.

### P2 (required, mechanical): keep the metadata in sync

`metadata.json` `references` mirrors the bibliography. After P1, add the same
three references there. The abstract text in `metadata.json` and
`mathdb-entry.json` does not need to change. This file is outside the audit's
write scope and is listed here for the parent.

### P3 (recommended): state what Theorem 1.3 actually proves

`production.tex` line 119 proves `D(u) ≥ P_m(I) = max{B_m(I), F(I)+c m² I²}`.
This dominates the upstream `Φ_m = max{F, B_m}` everywhere, and dominates it
strictly for `m≠0` at small `I`, where `B_m(I)=2I<F(I)`. The theorem as stated
gives only the second term, so the abstract's "strengthen" is true but
undersold, and it is ambiguous about which inequality it strengthens. Suggested
replacement for `main.tex` line 106:

```tex
 D(u)\ge\max\{\cB_{\E u}(\cI(u)),\,F(\cI(u))+c(\E u)^2\cI(u)^2\}
```

`\cB` would then need defining before Theorem 1.3, or this could be placed in a
remark after the proof instead. Alternatively, keep the theorem and change the
abstract to "We also strengthen the inequality $D(u)\ge F(\cI(u))$ by…".

### P4 (optional): precise MOO and Kramer–Saglam pointers

- `gaussian.tex` line 194: `\cite{MOO}` could read
  `\cite[Theorem~3.18 and Hypothesis~4]{MOO}`, as the source audit's R2
  suggested. The argument is re-proved inline, so this is not required.
- The upstream source credits Kramer–Saglam for the one-bit variance and
  capacity comparison that underlies `capacity:onebit`. Since the manuscript
  takes that lemma from \cite{OpenAI}, an extra citation is optional.

### P5 (optional): residual notation reuse

None of these causes ambiguity in a proof, but each could be renamed:

- `c` is used for the cost `c(x,y)`, for the constant in (eq:c), for
  `c_m=H(m)−(1−m²)L`, and for the core cost `c_c` (production line 29).
  Suggest `c_*` for the production constant.
- `b_*` (Assumption 2.1(6)) sits alongside `b`, `b(a)` and `b_j`.
- `K=max F'` (production line 126) sits alongside `\cK` (cost infimum).
  These are distinct glyphs, so the reuse is acceptable.
- `μ=4/3` in (eq:c) is the stated convexity bound. It replaces the research
  value `μ=1/(2L²)` from I334, and the change is benign because a larger
  `μ` only helps.

## 7. Not inspected

- Upstream proof truth, which is stipulated by `AGENTS.md`.
- The full texts of Chen et al. 2609.24931, Chen–Gohari–Nair 2502.10019,
  Heilman–Tarter, MOO, and Ky–Tran. Only abstracts and title pages, the cited
  theorem in Mossel–Neeman, and DLMF 4.36.3 were checked. The P1 comparison
  sentence relies on the staged i334/i336 records and the source audit's
  re-derivation.
- Research records not staged in this package, such as the i336 analysis body.
  The main checkout and thread 6e2685ef were deliberately not accessed.
- Any formal or Lean verification.
- A worldwide literature search beyond the sources listed. No novelty-to-literature
  claim is certified. The manuscript makes no priority claim (line 122), which
  is appropriate.
