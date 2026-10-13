# R019 manuscript audit, round 1 (Claude Opus 5.5)

**Verdict: REPAIR.** Every mathematical assertion in Theorem 1.1 and its proof is correct; I checked each one with exact symbolic computation. No step needs a new argument. A small number of required fixes remain before publication: one wrong sign, one literally inaccurate family-membership claim (abstract and introduction), one ambiguous typeset quantity, and missing literature positioning, including ACV v4 Theorem 5.3/Theorem 1.6 and the basic Crouzeix-conjecture citations. Recommended presentation improvements are listed separately.

This is an AI audit, not human peer review. No manuscript, index or record was edited. No commit was made and nothing was submitted externally.

## Reviewed artifacts

| Artifact | SHA-256 |
|---|---|
| `publications/entangled-crouzeix-equality/main.tex` (262 lines, 10004 B) | `165abbb12e54b5787ad726e38695b3557be955d164c9fc3e952a2441a5221f6e` |
| `publications/entangled-crouzeix-equality/tmp/main.pdf` (4 pp., 77387 B, XeTeX/xdvipdfmx) | `66295c558a609c656f1f295ee3c0780bf33acd3e94f09b808ae96071e513ce0d` |

The PDF was rendered at 90 dpi, and all four pages were inspected visually. Its text matches the reviewed `.tex`. The log timestamp matches the tex mtime, and the log has no undefined references and no rerun request. I could not recompile, because there is no TeX engine on PATH in this environment. Agreement between the PDF and source was checked by reading, not by rebuilding.

Staged records were authenticated against `/tmp/publication-r017-r022/manifest.json` (research pin `d513e308d86a38004d78bab9b9e88532e92bf56c`). All 13 R019/i287/i291/i292 files match. They include finding R019, the i287 analysis `8f8eb9a5…0bcd0b`, the i291/i292 analyses, reviews, dispositions and literature indices. I read these records as evidence and did not rely on their PASS. The main theorem does not use any pinned OpenAI upstream theorem (`fd4aeeb2…`), so no upstream hypothesis needed checking. Upstream appears only as context; see F4.

## 1. Mathematical verification (exact; `/tmp/r019-audit-claude/check.py`, `blocks.py`, SymPy 1.14)

| Manuscript claim (location) | Result |
|---|---|
| (1.1) entries of N; every nonzero N_ij has h_i−h_j=1 with h=(3,2,1,2,1,0) | ✔ |
| (2.1) U_θNU_θ* = e^{iθ}N (symbolic in θ) | ✔ |
| Re N in basis (e1,e3,e5,e2,e4,e6) is [[0,C],[C*,0]] with the displayed C | ✔ |
| CC* = I−aa*, ‖a‖² = 57/64 | ✔ |
| spec Re N = {1,1,−1,−1,±√7/8}; charpoly of Re(e^{−iθ}N) = (λ−1)²(λ+1)²(64λ²−7)/64 for **all** θ | ✔ |
| W(N) = closed unit disk | ✔ (support function ≡ 1, plus Toeplitz–Hausdorff) |
| ‖ℓ‖=1, Nℓ=0 | ✔ |
| N³N*³ = (7/4)e1e1*; N*e1, N*²e1, N*³e1 as displayed | ✔ |
| NN*²e1 = (12/5)e2 + (7√14/80)e4; ⟨ℓ, NN*²e1⟩ = 3√7/8 ≠ 0; ⟨ℓ, N*e1⟩ = 0 | ✔ |
| N*ℓ = (√7/2)e3 − (3√2/4)e5 | ✔ |
| "coefficient determinant of this vector and N*²e1 … is −2√2" (l. 140–141) | ✘ **sign**: det[N*ℓ, N*²e1] in (e3,e5) coordinates is **+2√2** (−2√2 only in the reverse order). Nonzero, so the argument is unaffected. See F1. |
| cyclic subspace of e1 under {N,N*} = ℂ⁶ | ✔ (rank 6) |
| commutant of {N,N*} = scalars (independent cross-check) | ✔ (dimension 1) |
| P(e^{it})*P(e^{it}) = I; max_{|z|≤1}‖P‖=1 | ✔ |
| factorization P = z·diag(z,1)·R·diag(1,z) | ✔ |
| P[N]x = 2y | ✔ |
| grading: P[N] raises h_i+g_j by 2; grade dimensions 1,3,4,3,1 with the stated bases | ✔ |
| grade-0 block: e6f1 ↦ (15√2/16)e4f1 + (√14/4)e5f2, squared norm 337/128 | ✔ |
| grade-2 block: sole output e1f2, row (3√7/10, 7√2/20, −9/8, −3√14/16) on (e2f1,e4f1,e3f2,e5f2), squared norm 337/128 | ✔ |
| middle block B (all 9 entries) | ✔ |
| B*B(1,0,1)ᵀ = 4(1,0,1)ᵀ; restriction matrix, trace 569/256, det 49/64 | ✔ |
| (3.2) squared singular values {4, 337/128 (×2), (569±33√113)/512}, plus seven zeros | ✔ (full 12×12 eigen-decomposition of P[N]*P[N]) |
| (569+33√113)/512 ≈ 1.797 < 337/128 ≈ 2.633; top value 4 is simple, so top lines are ℂx and ℂy | ✔ |
| §4: \|⟨x,ζ⊗u⟩\|² ≤ 1/2; bound 4t + (337/128)(1−t) ≤ 849/256 for t ≤ 1/2 | ✔ (the bound increases in t because 4 > 337/128) |
| (v*Pu)(N) = (I⊗v*)P[N](I⊗u) for the base-first convention | ✔ |
| √849/16 ≈ 1.8211 < 2 | ✔ |

**Compactness and limiting steps:** there are none. The maximum principle is applied to scalar polynomials on a closed disk, and the supremum over unit ζ is a maximum on a compact sphere. Nothing is open.

**Sharpness (informational, not a defect):** a numerical probe (`sharp.py`, Nelder–Mead with 400 random starts) gives max_{u,v}‖(v*Pu)(N)‖ ≈ 1.6736. So √849/16 is a valid bound but not sharp. The manuscript does not claim sharpness, and it should not.

## 2. Literature and contribution boundary

**LSS / Lawrence §4** (arXiv:1809.02779v2 HTML, SHA-256 `fc158711…ae269`, identical to the i291/i292 record). Lawrence's display is A(x,y,c,ξ,η), with nonzero entries A12=x, A14=cy, A23=y, A43=−cx, A45=√(1−c²)ξ, A56=η. The constraints are x,y,ξ,η,c>0, x²+y²=ξ²+η²=1 and c<1/2. Matching gives

  **N = 2A** with x=3/5, y=4/5, c=√14/8 (≈0.468<1/2), ξ=η=1/√2.

All constraints hold. With Lawrence's normalisation 2A=H+iK, Re N = H. So N is twice a member of the family, **not** a member: for example N12 = 6/5 > 1 ≥ x. This leads to F2. The manuscript's disclaimer of any novelty for the disk or the repeated-support pencil is appropriate. The disk follows from the same grading for every member of the family. The original LSS article was not obtained; Crossref confirms the bibliographic data (F6).

**ACV, arXiv:2608.27346 v4** (21 Sep 2026; it is still the latest version, since the unversioned abs page says "this version, v4"; HTML SHA-256 `4b707363…19aa`). The prior records used v3, but the manuscript correctly cites v4. Findings on v4:
- *Theorem 12.2* is a scalar polynomial equality classification in every finite dimension: p(z)=c(z−a)^m and A≃aI+r(C_m⊕B). The citation in Remark 4.1 is accurate.
- *Proposition 12.1* (needs only W(A)⊂D̄, not Jin) together with exact facts about N gives a stronger optional corollary; see O1.
- *Lemma 5.1/Theorem 5.3*: abstract minimal rectangular extremals have norming vectors of Schmidt ranks r,s with mutually orthogonal Schmidt families. The introduction also notes that excess over 2 "is already detected at an s×r matrix level with r,s≥2". The possibility of non-scalar norming vectors is therefore anticipated abstractly. The manuscript's increment is an **explicit attained instance with a polynomial witness and a uniform obstruction to all constant compressions**, not the abstract possibility. The manuscript currently does not cite Theorem 5.3, which leads to F4. The example is consistent with Theorem 5.3: the Schmidt vectors are {e3,e6} for x and {e1,ℓ} for y, which are mutually orthogonal, and r+s=4≤6. Proposition 5.4 (simplicity when r+s≥d−1=5) does not apply, and the manuscript proves simplicity directly.
- *Theorem 1.6* gives ψ_cb=2 ⇔ ψ=2 for d≤3. The example does **not** decide whether ψ(N)<ψ_cb(N)=2. The manuscript's sentence "nor determines the supremum over all scalar polynomials normalized on the disk" is correct but oblique; see F4.

**Kang R016** (`publications/complete-crouzeix-equality/main.tex`, SHA-256 `646e0c44…fefee9`; Zenodo API: title matches, DOI 10.5281/zenodo.23332163, published 2026-10-12). Theorem 1.1 assumes the complete Crouzeix bound and the Faber estimate (Assumption 1.1). For n≤4 it gives unit u,v with ‖p(A)‖=2M and max_{W(A)}|p|=M. It uses the same base-first convention P[A]=ΣA^k⊗C_k. The manuscript's description ("conditional result … affirmatively when n≤4") is accurate. Since n=6, there is no conflict.

**No overstatement found** relative to LSS, Lawrence §4 or ACV v4 beyond F2. The manuscript explicitly disclaims smallest dimension, nondisk counterexamples and the scalar supremum.

## 3. Required fixes (with exact replacements)

**F1 (correctness; l. 140–141).** The sign is wrong. Replace
`The coefficient determinant of this vector and $N^{*2}e_1$ in the $e_3,e_5$ plane is $-2\sqrt2$,`
with
`In the coordinates $(e_3,e_5)$, the vectors $N^*\ell$ and $N^{*2}e_1$ have determinant $\det\begin{pmatrix}\sqrt7/2&3/2\\-3\sqrt2/4&\sqrt{14}/4\end{pmatrix}=2\sqrt2\neq0$,`

**F2 (accuracy of the family claim; abstract l. 31, intro l. 57–58).** N is twice an LSS member. Replace the abstract sentence
`The matrix belongs to the classical Li--Spitkovsky--Shukla family.`
with
`The matrix is twice a member of the classical Li--Spitkovsky--Shukla family.`
and replace the introduction sentence at l. 57–58 with:
`The base matrix is $N=2A$, where $A$ is the Li--Spitkovsky--Shukla matrix \cite{LSS}, in the form reproduced in Lawrence \cite[Section~4]{Lawrence}, with parameters $x=3/5$, $y=4/5$, $c=\sqrt{14}/8$ and $\xi=\eta=1/\sqrt2$; these satisfy the constraints $x^2+y^2=\xi^2+\eta^2=1$ and $0<c<1/2$ stated there.`

**F3 (PDF ambiguity; l. 179).** `\sqrt2\,7/20` renders as "√2 7/20", which can be misread as √27/20. Replace it with `7\sqrt2/20`.

**F4 (literature positioning and standalone context; Introduction).** The paper never cites Crouzeix's conjecture, its complete form, the known general bound, or the ACV result most closely related to its theme. Insert after the definition of attained complete Crouzeix equality (after l. 51):

```
Crouzeix conjectured that $\|p(A)\|\le2\max_{W(A)}|p|$ for scalar
polynomials \cite{Crouzeix2004} and formulated the matrix-valued
(complete) version \cite{Crouzeix2007}; the constant $1+\sqrt2$ is
known in general \cite{CrouzeixPalencia}. The complete inequality with
constant two is proved in dimension at most three in \cite{ACV} and in
general in the preprints \cite{Direct,Structural}. The theorem below
uses none of these bounds. By \cite[Lemma~5.1 and Theorem~5.3]{ACV},
complete extremals can be compressed to a rectangular level whose
norming vectors have mutually orthogonal Schmidt families of possibly
larger rank. The question here is whether, for a given attained
witness $P$, that rank can always be reduced to one by constant
coefficient vectors.
```

Replace l. 91–93 ("It neither identifies … normalized on the disk.") with:
`It does not identify the smallest possible base dimension. Nor does it decide whether the scalar constant $\psi(N)=\sup\{\|f(N)\|:\max_{\overline\D}|f|\le1\}$ is smaller than two; in dimension at most three, $\psi$ and its complete analogue reach two simultaneously \cite[Theorem~1.6]{ACV}.`

Add these bibliography entries (verified via Crossref; Direct/Structural copied from R016's bibliography):
- `M.~Crouzeix, \emph{Bounds for analytical functions of matrices}, Integral Equations Operator Theory \textbf{48} (2004), 461--477. doi:10.1007/s00020-002-1188-6.`
- `M.~Crouzeix, \emph{Numerical range and functional calculus in Hilbert space}, J. Funct. Anal. \textbf{244} (2007), 668--690. doi:10.1016/j.jfa.2006.10.013.`
- `M.~Crouzeix and C.~Palencia, \emph{The numerical range is a $(1+\sqrt2)$-spectral set}, SIAM J. Matrix Anal. Appl. \textbf{38} (2017), 649--655. doi:10.1137/17M1116672.`
- the `Direct` and `Structural` OpenAI entries exactly as in `complete-crouzeix-equality/main.tex` (revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`).

**F5 (Kang citation precision; l. 53–54).** Replace
`The conditional result of \cite{Kang} answers this question affirmatively when $n\le4$.`
with
`Assuming the complete Crouzeix bound and a Faber coefficient estimate from \cite{Direct}, the author showed in \cite{Kang} that the answer is affirmative when $n\le4$.`

**F6 (bibliography).** Lawrence's paper is published. Use:
`B.~Lawrence, \emph{Examples for the quantum Kippenhahn theorem}, Oper. Matrices \textbf{13} (2019), no.~4, 1091--1124. doi:10.7153/oam-2019-13-74; arXiv:1809.02779v2 (section numbers refer to the arXiv version).`
Crossref gives volume = null for this DOI; the "13" is inferred from the DOI suffix `oam-2019-13-74`. Confirm it on the journal page before use. LSS metadata (Li, Spitkovsky, Shukla; LAA 270 (1998) 323–349; DOI as cited) are confirmed by Crossref; the third author's full name is Sudheer Shukla. The ACV and Kang entries are correct.

## 4. Recommended (non-blocking) improvements

- **l. 117–118:** add the missing step: "Hence the singular values of $C$ are $1,1,\sqrt{1-57/64}=\sqrt7/8$, and the eigenvalues of $\Reop N$ are $\pm$ these." At l. 119 also say "Since $e^{-i\theta}N=U_{-\theta}NU_{-\theta}^*$, every $\Reop(e^{-i\theta}N)$ has the same spectrum, so the support function of $W(N)$ is identically one."
- **l. 133:** "The $e_2,e_4$ component of $NN^{*2}e_1$" is odd, because the whole vector lies in span{e2,e4}. Write `$NN^{*2}e_1=\frac{12}{5}e_2+\frac{7\sqrt{14}}{80}e_4$ has inner product $3\sqrt7/8$ with $\ell$`.
- **Theorem 1.1:** add the explicit consequence `Consequently $\|P[N]\|=2\max_{z\in W(N)}\|P(z)\|$.` This ties (1.2) to the definition at l. 50.
- **l. 164:** for standalone verification, show P[N]x=2y via Ne3=(8/5)e2−(3√14/20)e4, N²e3=(3/2)e1, N²e6=(5√2/4)e4, N³e6=(√7/2)e1. These give P[N](e3f1+e6f2) = 2e1f1 + 2ℓf2.
- **l. 168–169:** state that P[N] annihilates grades 3 and 4. **l. 171:** "For example" → "Explicitly", since the grade-0 domain is one-dimensional. Introduce the juxtaposition notation e_if_j before its first use.
- **§4:** add one sentence: write w=αx+w′ with w′⊥x. Since P[N]*y=2x, P[N]w′⊥y, so ‖P[N]w‖² = 4|α|² + ‖P[N]w′‖². The resulting bound increases in |α|², which justifies substituting 1/2.
- **Remark 4.1:** the last sentence reads like internal audit language. Suggested rewrite: `In particular, the theorem concerns compressions of the fixed witness $P$; it does not by itself bound $\psi(N)$.`
- **Abstract l. 32:** "The polynomial and its simple top singular vectors" → "The simple top singular pair of $P[N]$". **Intro l. 60–61:** define "coefficient rank" as the Schmidt rank in $\C^6\otimes\C^2$, or use "Schmidt rank".
- **Professional metadata:** add `\subjclass[2020]{47A12, 47A60, 15A60}`, `\keywords{...}`, and optionally `\email`. Fix the underfull `\hbox` in the Kang bibitem (log l. 502, badness 7099; visibly stretched in the PDF on p. 4), e.g. with `\raggedright` inside the bibliography. The LSS DOI breaks after its final hyphen ("00251-⏎6"); prefer `\url`/`\nolinkurl` line breaking or reflow.
- Optionally note that √849/16 is not claimed sharp (numerically, max ≈ 1.674).

**O1 (optional strengthening, conditional on ACV v4 Prop. 12.1).** N⁴=0, ‖N‖²=(71+3√105)/32, ‖N²‖²=25/8 and ‖N³‖²=7/4, so ‖N^m‖<2 for every m≥1 (exact). Prop. 12.1 needs only W(N)⊂D̄. It forces any scalar polynomial attaining ‖p(N)‖=2max_{D̄}|p| to be cz^m with ‖N^m‖=2. Hence **no scalar polynomial attains equality at N**, while the 2×2 witness P does. This is the cleaner "complete versus scalar attainment" contrast. It depends on an external preprint, so state it as a credited remark, not as part of Theorem 1.1. It still does not decide ψ(N) (non-polynomial or limiting extremals).

## 5. Not inspected / limits

- Original LSS article: not obtained (same limit as i292). Family membership was verified only against Lawrence's reproduction.
- ACV v4: Sections 5 (Lemma 5.1–Prop. 5.4), the introduction around Theorem 1.6, and §12 (Prop. 12.1–Cor. 12.5) were read in full. Other sections were searched by keyword only. ACV proofs were not audited.
- Pinned OpenAI preprints: not fetched; the theorem does not depend on them. R016 was read at its abstract, introduction, Theorem 1.1 and bibliography only.
- Published Operators and Matrices version of Lawrence: metadata only.
- PDF: not rebuilt locally (no TeX engine); checked visually and against the log.
- Worldwide priority: not assessed beyond the sources above.

## 6. Sources and retrieval hashes (`/tmp/r019-audit-claude/dl/`, fetched 2026-10-13)

- arXiv:1809.02779v2 HTML `fc158711eee63ea9ffcf90d501799b92b3452d7fc7ade2e30d7b02834b2ae269`; abs `2b1139c4…2f36`
- arXiv:2608.27346v4 HTML `4b707363b87b71b42cfff746a520da2247f4aa796bc43fb28bb4eebefb0819aa`; abs v4 `3a4def8b…f8d4`; abs (latest) `95f0cd10…1262`
- Crossref LSS `ba5c5014…981d`; Lawrence OaM `50cf2f69…e3f2`; Crouzeix 2007 `3447a079…8ecf`; Zenodo 23332163 `d0b7f666…1cec`
- Scripts: `check.py` `0276317e…29fe`, `blocks.py` `4f596fe3…da69`, `sharp.py` `2716b29d…737f`, `h2t.py` `bd92e900…5a91`
