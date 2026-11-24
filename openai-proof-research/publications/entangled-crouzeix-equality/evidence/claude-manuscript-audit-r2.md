# R019 manuscript audit, round 2 (Claude Opus 5.5)

**Verdict: REPAIR for the reviewed revision `ea460ee7…4565` (minor, attribution only); PASS for the concurrent revision `4293acbd…d24d`, which applies the fix (see Addendum).** The mathematics passes. Every computational and logical step of Theorem 1.1 was re-verified exactly against the current text, and all six round-1 required fixes (F1–F6) are correctly resolved with no mathematical regression. One required fix remains, and it is new in this round: the introduction's history of the constant two omits the 2026 scalar proofs. Those proofs are cited by ACV v4 and by the pinned `Direct` preprint that the manuscript itself cites (R1 below). My round-1 replacement text had the same omission, so this is partly my own earlier oversight. If the text in R1 is inserted verbatim and nothing else changes, I would regard the manuscript as PASS. The mathematics needs no re-audit; only a re-check of the build/PDF would be needed.

This is an AI audit, not human peer review. No manuscript, index or record was edited. No commit was made and nothing was submitted externally.

## Reviewed artifacts

| Artifact | SHA-256 |
|---|---|
| `publications/entangled-crouzeix-equality/main.tex` (301 lines; mtime 2026-10-13 12:06:09) | `ea460ee75b543c00dc4b80313d1dc921a5e712b749276ba46ab844058db74565` |
| `publications/entangled-crouzeix-equality/tmp/main.pdf` (4 pp., 85527 B, xdvipdfmx; mtime 12:06:10) | `796bb2452a1450e608a00edb441e6e3638ef58a223b57b8a588507b29a1dde16` |
| Prior report `evidence/claude-manuscript-audit-r1.md` | read in full; its objections are tracked below |

**PDF/build.** I rebuilt from a copy of `main.tex` with the bundled Tectonic (`rooted-matching-entropy/tmp/tools/tectonic`) in `/tmp/r019-audit-claude-r2/build/`. The run had two TeX passes and finished with no undefined references and no Overfull/Underfull/rerun warnings. `pdftotext -layout` output of the rebuilt PDF and of the shipped `tmp/main.pdf` is **byte-identical**. The PDF hashes differ only because of build metadata; the rebuilt PDF is `1c2d4237…4cbd`. The shipped `tmp/main.log` likewise has no warnings. All four pages were rendered at 90 dpi and inspected visually. PDF Title and Author metadata are correct. The bibliography is now ragged-right: the Kang entry is no longer stretched, and the LSS DOI is on one line. The `7\sqrt2/20` entry renders unambiguously.

## 1. Disposition of round-1 required fixes

| Item | Status | Check |
|---|---|---|
| F1 determinant sign (l. 156–157) | **Resolved** | The text now reads "determinant of this vector [N\*ℓ] and N\*²e₁ … is 2√2". Exact: det[(√7/2, −3√2/4), (3/2, √14/4)] = +2√2 in this order. |
| F2 family membership (abstract l. 31; intro l. 68–72) | **Resolved** | The text says "twice a member" and gives N = 2A with x=3/5, y=4/5, c=√14/8, ξ=η=1/√2. I re-derived this exactly from Lawrence's displayed A (arXiv:1809.02779v2 §4: A₁₂=x, A₁₄=cy, A₂₃=y, A₄₃=−cx, A₄₅=√(1−c²)ξ, A₅₆=η), with constraints x,y,ξ,η,c>0, x²+y²=ξ²+η²=1, c<1/2. N − 2A = 0 holds exactly. |
| F3 ambiguous `\sqrt2\,7/20` (l. 195) | **Resolved** | The text is now `7\sqrt2/20` and renders as 7√2/20. |
| F4 literature positioning (l. 52–60, 105–109) | **Resolved, with residual R1** | Crouzeix 2004/2007, CP 2017, Direct/Structural, ACV Lemma 5.1/Thm 5.3 and ACV Thm 1.6 are cited. Each citation was checked against the source (see §3). The scalar-constant limitation is stated plainly. Residual: the scalar proofs are missing (R1). |
| F5 Kang precision (l. 63–65) | **Resolved** | The text says "Assuming the complete Crouzeix bound and a Faber coefficient estimate from [Direct]…". This matches R016 `main.tex` (`646e0c44…fefee9`), Assumption 1.1(1)–(2) and Theorem 1.1, which give unit u,v with ‖(v\*Pu)(A)‖=2M for 1≤n≤4. Optional precision: R016 also uses Lemma 4.1 of [Direct] (analytic outer approximation); see O3. |
| F6 Lawrence publication data (l. 283–287) | **Resolved** | Confirmed on the journal: the abstract PDF `files.ele-math.com/abstracts/oam-13-74-abs.pdf` (`02eb44ac…5d49`) reads "Operators and Matrices, Volume 13, Number 4 (2019), 1091–1124, doi:10.7153/oam-2019-13-74". The article page `oam.ele-math.com/13-74/…` (`6fef0476…6f64`) gives author Ben Lawrence, Volume 13, Issue 4, and the DOI. Crossref agrees on issue and pages. The note "Section numbers refer to arXiv:1809.02779v2" is appropriate. |

The optional strengthened corollary (round-1 O1) was deliberately not added, and that choice is acceptable. The unconditional explicit core does not need it. The manuscript makes no claim that depends on it.

## 2. Full re-verification of the current mathematics

The new, independent script is `/tmp/r019-audit-claude-r2/check_r2.py` (`588a8951…1d1f`), run with SymPy 1.14.0 in a private venv. All values were transcribed from the **current** `main.tex`. Result: **45/45 exact checks PASS** (output `check_r2.out`, `82274839…975c`). The script covers:

- N = 2A(Lawrence parameters), and the parameter constraints.
- Every nonzero N_ij has h_i − h_j = 1. U_θ N U_θ\* = e^{iθ}N, checked symbolically in θ.
- Re N in the ordered basis (e₁,e₃,e₅,e₂,e₄,e₆) is [[0,C],[C\*,0]]. CC\* = I − aa\*, ‖a‖² = 57/64, and char Re N = (λ−1)²(λ+1)²(λ²−7/64).
- ‖ℓ‖=1 and Nℓ=0. N³N\*³ = (7/4)e₁e₁\*. The values N\*e₁, N\*²e₁ and N\*³e₁ match the text. NN\*²e₁ ∈ span(e₂,e₄), ⟨ℓ,NN\*²e₁⟩ = 3√7/8 and ⟨ℓ,N\*e₁⟩ = 0. N\*ℓ matches the text, the determinant is +2√2, and the {N,N\*}-cyclic span of e₁ is ℂ⁶.
- The factorization P = z·diag(z,1)·R·diag(1,z), with R unitary, so P(e^{is}) is unitary. The coefficients C₁,C₂,C₃ reproduce P.
- P[N]x = 2y and P[N]\*y = 2x. Every entry of P[N] raises the grade by exactly 2, and the grade dimensions are 1,3,4,3,1.
- The grade-0 image of e₆f₁ and its squared norm 337/128. The grade-2 row (3√7/10, 7√2/20, −9/8, −3√14/16), with output only in e₁f₂ and squared norm 337/128.
- B equals the displayed matrix, and grade-1 inputs map only into grade 3. B\*B(1,0,1)ᵀ = 4(1,0,1)ᵀ. The restriction matrix is as displayed, with trace 569/256 and determinant 49/64, and the complement is invariant.
- **Full** characteristic polynomial of P[N]\*P[N] = λ⁷(λ−4)(λ−337/128)²(λ² − (569/256)λ + 49/64). Discriminant (569/256)² − 4·(49/64) = 33²·113/256², which gives (569 ± 33√113)/512 < 337/128 < 4.
- 2 + 337/256 = 849/256 and 849 < 1024. (v\*Pu)(N) = (I₆⊗v\*)P[N](I₆⊗u) holds symbolically for general u,v.

**Logical steps re-read in the current text (all valid):**
1. *Disk (l. 133–136).* The eigenvalues of [[0,C],[C\*,0]] are ± the singular values of C, i.e. ±1, ±1, ±√7/8. Equation (2.1) gives Re(e^{−iθ}N) = U_{−θ}(Re N)U_{−θ}\*, so the support function is ≡ 1. W(N) is compact and convex, hence W(N) = D̄.
2. *Irreducibility (l. 138–161).* N\*e₁ ⊥ ℓ is nonzero, and NN\*²e₁ has a nonzero ℓ-component. Both lie in span(e₂,e₄), so that span lies in the cyclic space K. Then ℓ ∈ K, so N\*ℓ ∈ K. Together with N\*²e₁ and det ≠ 0 this gives e₃,e₅ ∈ K, and N\*³e₁ gives e₆ ∈ K. A projection Q commuting with N,N\* commutes with e₁e₁\*, so Qe₁ = (e₁\*Qe₁)e₁ ∈ {0,e₁}. Cyclicity then forces Q ∈ {0,I}. The argument is complete.
3. *Attainment.* P is unitary on 𝕋, and the maximum principle applied to v\*P(z)u gives max_{D̄}‖P‖ = 1, attained on the circle. Combined with W(N) = D̄ and ‖P[N]‖ = 2, this is attained complete equality in the sense of l. 48–50.
4. *Spectrum.* The graded blocks have orthogonal domains and orthogonal ranges, so the singular values of P[N] are the union over blocks. Since 4 is a simple squared singular value, the top input line is ℂx and the top output line is ℂy.
5. *Compression bound (§4).* Write w = αx + w′ with w′ ⊥ x. Because x is an eigenvector of P[N]\*P[N], we get ‖P[N]w‖² = 4|α|² + ⟨w′, P[N]\*P[N]w′⟩ ≤ 4|α|² + (337/128)(1 − |α|²). This bound increases in |α|², and |α|² ≤ 1/2 by Cauchy–Schwarz (|ζ₃|² + |ζ₆|² ≤ 1). Then ‖(v\*Pu)(N)ζ‖ ≤ ‖P[N](ζ⊗u)‖ ≤ √849/16 < 2, and the supremum over unit ζ is attained on a compact sphere.

**Compactness/limits:** none beyond the closed disk and unit sphere maxima, which are fine. **Upstream dependence:** none. No pinned OpenAI theorem (`fd4aeeb2…`) is used in any deduction. `Direct`/`Structural` appear only as context, and the text says so explicitly at l. 56 and l. 77–78. **Self-containedness:** a reader can verify every claim by finite exact arithmetic from the displayed data. Two places assert results of direct computation without showing the intermediate products: "Direct substitution gives P[N]x=2y" and the full B. This is acceptable for a short note, and the round-1 recommendation to show Ne₃, N²e₃, N²e₆, N³e₆ remains optional.

## 3. Literature and attribution checks (current text)

- **Crouzeix 2004/2007 (l. 52–53).** ACV v4 §1 states that Crouzeix conjectured constant 2 in 2004 [IEOT 48] and that in 2007 [JFA 244] "he introduced the completely bounded version … and proved the corresponding inequality with 2 replaced by 11.08". The manuscript's attribution is accurate, and the bibliographic data match ACV's references [13], [14].
- **CP (l. 53–54).** "a general bound with constant 1+√2" is accurate (ACV ref. [19]: SIAM J. Matrix Anal. Appl. 38(2):649–655, 2017).
- **ACV Lemma 5.1 / Theorem 5.3 (l. 57–59).** "already permits higher-rank Schmidt families in abstract norming vectors" is accurate per my round-1 reading of v4 §5. The unversioned arXiv abs page still hashes to `95f0cd10…1262`, identical to round 1, so v4 remains current.
- **ACV Theorem 1.6 (l. 108–109).** The statement checked in v4 is: "Let A ∈ M_d(ℂ) with d ≤ 3. Then ψ_cb(A) = 2 ⇔ ψ(A) = 2". ACV define ψ over f ∈ 𝒜(K_A), whereas the manuscript writes a polynomial supremum. For W(N) = D̄ these agree by density of polynomials in the disk algebra, and the l. 108 sentence is about d ≤ 3 in ACV's own terms. Accurate.
- **ACV Theorem 12.2 (Remark 4.1).** Accurate as in round 1.
- **LSS/Lawrence (l. 68–75).** Accurate. The disclaimer of novelty for the disk matrix and the pencil is appropriate.
- **Direct/Structural (l. 55, bib).** Both raw URLs at `fd4aeeb2…` return HTTP 200. The titles and dates match the bibliography: Direct `main.tex` `54a429fe…333f`, "A direct proof of the complete Crouzeix inequality", September 26, 2026; Structural `main.tex` `8a5de532…270e621c`, "The complete Crouzeix theorem: optimal similarity and a common positive boundary representation", September 23, 2026.
- **Novelty claim.** The claim is bounded correctly: an explicit attained instance with a uniform obstruction to constant rank-one compression. The manuscript expressly does not claim minimal dimension, a nondisk example, a scalar-supremum decision, or the abstract possibility of higher Schmidt rank. I found no overstatement.

## 4. Required fix

**R1 (attribution; intro l. 52–56).** The paragraph traces the constant two only to the OpenAI preprints. Two 2026 preprints prove the *scalar* conjecture: Jin, and Lorist–Schwenninger. ACV v4 states that "Jin [27] and Lorist and Schwenninger [30] independently proved the scalar conjecture" (§1), and the pinned `Direct` preprint cites them along with Luo ("Recent scalar proofs include work of Jin, Lorist and Schwenninger, and Luo", l. 90–92). Leaving them out could lead a reader to think the scalar conjecture is open, or that it is settled only through the cited OpenAI work. That matters in a paper whose subject is the scalar/complete contrast. Replace l. 52–56:

```
Crouzeix's scalar conjecture and its complete formulation
appear in \cite{Crouzeix2004,Crouzeix2007}. Crouzeix and Palencia
\cite{CP} prove a general bound with constant $1+\sqrt2$.
The preprints \cite{Direct,Structural} address the constant two;
the explicit theorem below uses none of these general bounds.
```

with

```
Crouzeix's scalar conjecture and its complete formulation
appear in \cite{Crouzeix2004,Crouzeix2007}. Crouzeix and Palencia
\cite{CP} prove a general bound with constant $1+\sqrt2$.
The scalar conjecture is proved in the preprints
\cite{Jin,LoristSchwenninger}, and the preprints
\cite{Direct,Structural} address the complete inequality with
constant two. The explicit theorem below uses none of these
general bounds.
```

Add these entries, with metadata from `Direct/build/references.tex` at `fd4aeeb2…` (`6402be83…b2b6`) and confirmed against arXiv and Crossref:

```
\bibitem{Jin} S.~Jin, \emph{The numerical range is a $2$-spectral set},
preprint, \href{https://doi.org/10.20944/preprints202607.1919.v4}{Preprints.org 202607.1919, version 4}, 2026.
\bibitem{LoristSchwenninger} E.~Lorist and F.~L.~Schwenninger,
\emph{A solution to Crouzeix's conjecture},
\href{https://arxiv.org/abs/2608.03841v2}{arXiv:2608.03841v2}, 2026.
```

The sources were checked. The arXiv abs page for 2608.03841v2 (`a63cf08f…77b4`) gives title "A solution to Crouzeix's conjecture", authors Emiel Lorist and Felix Schwenninger, v1 4 Aug 2026 and v2 17 Aug 2026. Crossref for `10.20944/preprints202607.1919.v4` (`c479d113…fd814`) gives "The Numerical Range Is a 2-Spectral Set", Shanmu Jin, posted 2026-08-07. Luo (Preprints.org 202608.1661 v2) may be added on the same footing as in `Direct`; that is optional.

This adds no mathematical claim. After insertion, one rebuild check is needed: no undefined citations and no overfull lines. `thebibliography` is hand-ordered, so the placement of the new entries is the author's choice; alphabetical order by author would put `Jin` between `CP` and `Kang`, and `LoristSchwenninger` after `LSS`.

## 5. Optional (non-blocking)

- **O1.** l. 149 "The e₂,e₄ component of NN\*²e₁" → "The vector NN\*²e₁ = (12/5)e₂ + (7√14/80)e₄ has inner product 3√7/8 with ℓ". The vector already lies in span(e₂,e₄), so the current wording is harmless but odd.
- **O2.** §4: add the one-line decomposition from §2 item 5 above, to make "the spectral decomposition therefore implies" fully explicit.
- **O3.** l. 63–64: "Assuming the complete Crouzeix bound and a Faber coefficient estimate from [Direct]" → append ", and using its analytic outer approximation lemma". R016 states at l. 98–99 that it also uses Lemma 4.1 of [Direct]. This is a precision improvement only, since R016 presents that lemma as an elementary geometric fact rather than an assumption.
- **O4.** Remark 4.1, last sentence: this still reads like internal audit language. See the round-1 suggested rewrite.
- **O5.** `\subjclass[2020]{47A12, 47A60, 15A60}` and `\keywords{…}` are still absent.
- **O6.** The bound √849/16 ≈ 1.821 is not sharp (numerical max ≈ 1.674, round-1 `sharp.py`). The manuscript makes no sharpness claim, which is correct.

## 6. Not inspected / limits

- Original LSS 1998 article: not obtained. Membership was verified against Lawrence's reproduction only, as in round 1.
- ACV proofs, the Jin, Lorist–Schwenninger and Luo proofs, and the OpenAI preprints' proofs were not audited. They are cited context only, and the theorem does not depend on them.
- ACV v4 was re-read only at §1 (Theorem 1.6, the definitions of ψ and ψ_cb, and the history paragraph) and the bibliography. Sections 5 and 12 rely on the round-1 reading of the same unchanged v4.
- R016 was read at its abstract, Assumption 1.1 and Theorem 1.1 (`646e0c44…`) only.
- Worldwide priority beyond the sources listed was not assessed.

## 7. Sources and hashes (fetched 2026-10-13; `/tmp/r019-audit-claude-r2/dl/`)

- `oam.ele-math.com/13-74/Examples-for-the-quantum-Kippenhahn-theorem` `6fef04762b7e57c48cba9a9cf9dd126496453ed951d9e75b71969aec5c2a6f64`; abstract PDF `02eb44acce29937c15e2b4a5e64090a91b7e93284bb52f823c0dcc23db2f5d49`
- arXiv 2608.27346 (latest = v4) abs `95f0cd10f1f32a2313440ff1fbdbb4686dc182bf9e21a9c333fa137a30651262`; v4 text from round 1 (`/tmp/r019-audit-claude/acv4.txt`, from HTML `4b707363…19aa`)
- arXiv 2608.03841v2 abs `a63cf08fe1643d95e9687c4c6d80b99da394efac879e6a8dbae6be457a9377b4`
- Crossref 10.20944/preprints202607.1919.v4 `c479d11359d166ab8501f57d5c564fba6e776387cb936cb51e1d6d5fb50fd814`
- openai/math@`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`: Direct `build/main.tex` `54a429fe7129b4760b3015fabf2269d4de5fa38aba9539b18542c1df7e58333f`, `build/references.tex` `6402be83926f774063d5e4e65a0075a68682419f388eb9c7c500231fb350b2b6`; Structural `build/main.tex` `8a5de532bd3bd4c0b84cc8114c22175968813a6e984ced0d1bf48011270e621c`
- Lawrence arXiv v2 §4 text: round-1 `/tmp/r019-audit-claude/lawrence.txt` (from HTML `fc158711…ae269`)
- Scripts and outputs: `check_r2.py` `588a89519fac2a5fa8253bf2c229282e9cc498d6ff81af47c56a7e3824821d1f`; `check_r2.out` `82274839b2418cb292d5413b6e3b056a79bf0e1a8ddc2f0a88c6fa449fe5975c`; rebuilt PDF `1c2d42371a255db95158bac6fbe2efab560900153660a6435331e5372b874cbd`; extracted text `c45550fab3d6623a01faf584a399c13cddc4e66f5af201bb5b72c2768d04484b`

## Addendum: concurrent revision `4293acbd…` (R1 applied), verdict **PASS**

While this report was being written, `main.tex` changed on disk (mtime 12:21:44). `tmp/main.pdf`/`main.log` were rebuilt at 12:21:57. The new hashes are:

| Artifact | SHA-256 |
|---|---|
| `main.tex` | `4293acbdcdec76884196a5744909a564f373ff69c60b68ad778278b62d62d24d` |
| `tmp/main.pdf` (4 pp.) | `fd7f6dd30ba01c3c2c0b3d3120545da5350ee5f3180c86e95bc03e6d9ec697ce` |

I diffed this against the reviewed revision `ea460ee7…4565`. The **only** changes are these:
1. l. 55–58: "Proofs of the scalar conjecture are given in the preprints \cite{Jin,LoristSchwenninger}. The preprints \cite{Direct,Structural} address the complete inequality with constant two. The explicit theorem below uses none of these general bounds."
2. Two bibitems, `Jin` and `LoristSchwenninger`, inserted after `CP`. Their metadata matches the sources in §4/§7: title, author, Preprints.org 202607.1919 v4 with DOI 10.20944/preprints202607.1919.v4, and arXiv:2608.03841v2.

The change is substantively the R1 replacement. No mathematical text, display, theorem statement or other citation changed, so §1–§3 apply unchanged to `4293acbd…`.

**Build:** I rebuilt independently with Tectonic in `/tmp/r019-audit-claude-r2/build2/` (rebuilt PDF `d819fdce4373393afabab18843b51d44cbc7c82bb73ed29116be77c73664c6c9`). Both the rebuild log and the shipped log show 0 Underfull/Overfull/undefined/rerun messages. `pdftotext -layout` output of the rebuild and of the shipped `tmp/main.pdf` is identical. Pages 1 and 4 were inspected visually. The citations render as [5, 6] and [10, 11], the reference list [1]–[11] is correct, and nothing overflows.

**Verdict for `main.tex` `4293acbd…` / `tmp/main.pdf` `fd7f6dd3…`: PASS.** No required fixes remain. The §5 optional items stand, and none of them blocks publication. This is an AI audit, not human peer review. It does not cover the other evidence files that appeared in `evidence/` during this round (`claude-manuscript-audit-r3.md`, metadata JSONs, `publication-review.md`), which I did not read or edit.
