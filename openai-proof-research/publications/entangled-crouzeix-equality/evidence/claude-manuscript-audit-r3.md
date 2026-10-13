# R019 manuscript audit, round 3 (Claude Opus 5.5)

**Verdict: REPAIR (one literature sentence and two bibliography entries).** The mathematics passes. I re-derived every assertion of Theorem 1.1 and its proof with exact symbolic computation (49 checks, all pass). All six round-1 repairs (F1 to F6) are correctly applied. One required fix remains, which round 1 also missed. The introduction presents Crouzeix's scalar conjecture as stated but unresolved, and gives $1+\sqrt2$ as the general bound. It does not mention that the scalar conjecture has since been proved in the 2026 preprints of Jin and of Lorist and Schwenninger. ACV v4, which the manuscript cites, says this explicitly, and the author's companion paper R016 cites Jin. The fix is a single sentence (N1 below). After N1 is applied, I would return PASS without another mathematical round.

This is an AI audit, not human peer review. I edited no manuscript, index or record. I made no commit and no external submission. Round 2 produced no verdict because of a provider rate limit.

## Reviewed artifacts

| Artifact | SHA-256 |
|---|---|
| `main.tex` (301 lines, 12534 B, mtime 2026-10-13 12:06:09) | `ea460ee75b543c00dc4b80313d1dc921a5e712b749276ba46ab844058db74565` |
| `tmp/main.pdf` (4 pp., 85527 B, xdvipdfmx) | `796bb2452a1450e608a00edb441e6e3638ef58a223b57b8a588507b29a1dde16` |
| `tmp/main.log` | `94c5e45bc264a2a7e4a34ee9690808d92b562594201479e8cfe5d525cc302056` |

I hashed both files again after the audit, and they were unchanged.

**Rebuild:** I compiled a copy of `main.tex` with Tectonic 0.17.0 (`rooted-matching-entropy/tmp/tools/tectonic`, `-X compile`) in `/tmp/r019-audit-claude-r3/build/`.
- The rebuilt `main.log` is byte-identical to `tmp/main.log`.
- The rebuilt PDF has the same size (85527 B), and its extracted text is identical (`pdftotext -layout`).
- The PDF bytes differ only in the document `/ID` and the random font-subset tags. The rebuilt PDF hash is `7e45228b…08d6`.
- The log has no warnings, no undefined references, no rerun request, and no overfull or underfull boxes. The round-1 underfull Kang bibitem is fixed by `\raggedright`.
- I rendered all four pages at 90 dpi and inspected them visually. The typesetting is clean. The coefficient now renders as $7\sqrt2/20$, and the DOIs break acceptably.

**Staged research records:** I checked all 13 R019/i287/i291/i292 files under `/tmp/publication-r017-r022/` against `manifest.json` (SHA-256 `2854605a…ce7d`; research pin `d513e308d86a38004d78bab9b9e88532e92bf56c`). All 13 match. The manuscript's theorem and proof agree with `frontier/findings/R019-entangled-complete-crouzeix-equality.md`. I treated the prior PASS verdicts as evidence only.

**Pinned upstream** (`openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, per `sources/upstream.json`): Theorem 1.1 and its proof use **no** upstream theorem, so no upstream hypothesis enters the deduction. I fetched both cited preprints from their pinned raw URLs to check the bibliography:
- `preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026/build/main.tex`: `54a429fe…333f`. Title and date ("September 26, 2026") match `[Direct]`. Its Proposition `prop:coefficients` is the Faber coefficient estimate that the introduction attributes to it via R016.
- `preprints/The-complete-Crouzeix-theorem-September-23-2026/build/main.tex`: `8a5de532…b2d5`. Title and date match `[Structural]`.

## 1. Round-1 repairs

| Item | Location in current `main.tex` | Status |
|---|---|---|
| F1 determinant sign | l. 156–157: "coefficient determinant of this vector and $N^{*2}e_1$ … is $2\sqrt2$" | **Fixed.** Exact value: $\det[N^*\ell,\ N^{*2}e_1]$ in $(e_3,e_5)$ coordinates is $+2\sqrt2$. |
| F2 twice an LSS member | Abstract l. 31; intro l. 68–72 | **Fixed.** $N=2A(3/5,4/5,\sqrt{14}/8,1/\sqrt2,1/\sqrt2)$ exactly, all of Lawrence's constraints hold, and $c=\sqrt{14}/8\approx0.468<1/2$. I re-read the family against Lawrence arXiv:1809.02779v2 §4 (display at the start of §4, constraints "$x,y,\xi,\eta,c>0$, $x^2+y^2=\xi^2+\eta^2=1$, $c<1/2$"). |
| F3 coefficient typesetting | l. 195: `7\sqrt2/20` | **Fixed;** it renders unambiguously. |
| F4 classical, pinned and ACV attribution; scalar-constant scope | l. 52–60, 105–109 | **Fixed as worded**, with all citations accurate (§3). One factual omission remains in the same paragraph; see N1. |
| F5 named prior assumptions | l. 63–65 | **Fixed.** This matches R016 (`complete-crouzeix-equality/main.tex`, `646e0c44…fefee9`). R016's Assumption 1.1 consists of Theorem 1.1 and Proposition 2.2 of `[Direct]`, and its Theorem 1.1 requires $n\le4$. |
| F6 Lawrence journal | bibitem `Lawrence`, l. 283–287 | **Fixed and now confirmed.** The journal page `oam.ele-math.com/13-74/` gives volume 13 (its page metadata has `"volume":13`). Crossref gives issue 4, pages 1091–1124, and the DOI resolves. |

## 2. Full mathematical verification

The script is `/tmp/r019-audit-claude-r3/check_r3.py` (SHA-256 `daff3633…b005`), with output in `check_r3.out` (`0b8d84cc…c2c3`). It uses SymPy 1.14.0 in a fresh venv. All checks are exact symbolic computations, apart from two 50-digit sign evaluations of explicit algebraic numbers.

**§2, disk (l. 112–136).**
- The support of $N$ is graded by $h$, and $U_\theta NU_\theta^*=e^{i\theta}N$ holds symbolically in $\theta$.
- The block form of $\Reop N$ with the displayed $C$ is correct. $CC^*=I-aa^*$ and $\|a\|^2=57/64$.
- The spectrum of $\Reop N$ is $\{1,1,-1,-1,\pm\sqrt7/8\}$.
- The characteristic polynomial of $\Reop(e^{-i\theta}N)$ is $(\lambda-1)^2(\lambda+1)^2(64\lambda^2-7)/64$ for every $\theta$.
- Logic: the support function is identically 1, and $W(N)$ is compact and convex (Toeplitz–Hausdorff), so $W(N)=\overline\D$. ✔
- The "therefore" at l. 133 skips the step "the singular values of $C$ are $1,1,\sqrt{7}/8$". The step is immediate and the claim is correct.

**§2, irreducibility (l. 138–161).**
- $\|\ell\|=1$ and $N\ell=0$.
- $N^3N^{*3}=\tfrac74e_1e_1^*$, and the three vectors $N^{*k}e_1$ are as displayed.
- $NN^{*2}e_1=\tfrac{12}5e_2+\tfrac{7\sqrt{14}}{80}e_4$, with $\langle\ell,NN^{*2}e_1\rangle=3\sqrt7/8\ne0$ and $\langle\ell,N^*e_1\rangle=0$. So $N^*e_1$ and $NN^{*2}e_1$ span $\mathrm{span}\{e_2,e_4\}$.
- $N^*\ell$ is as displayed, and the $(e_3,e_5)$ determinant is $2\sqrt2$.
- The six explicit vectors have rank 6.
- The projection argument is valid: $Q$ commutes with $e_1e_1^*$, so $Qe_1=\langle Qe_1,e_1\rangle e_1$, and cyclicity forces $Q\in\{0,I\}$.
- Independent cross-check: the commutant of $\{N,N^*\}$ has dimension 1. ✔

**§3, attainment (l. 164–223).**
- (1.1) matches $P=zC_1+z^2C_2+z^3C_3$, and $P(e^{it})$ is unitary. The maximum principle applied to $v^*Pu$ gives the norm 1 on the disk.
- The factorization is correct, and the middle factor is unitary.
- $P[N]x=2y$ and $P[N]^*y=2x$.
- Every term raises the grade by 2. The grade dimensions are $1,3,4,3,1$, and grades 3 and 4 are annihilated.
- Grade-0 block: the image is as displayed, with squared norm $337/128$.
- Grade-2 block: its only output is $e_1f_2$, the row is $(3\sqrt7/10,7\sqrt2/20,-9/8,-3\sqrt{14}/16)$, and the squared norm is $337/128$.
- All nine entries of $B$ match.
- $B^*B(1,0,1)^T=4(1,0,1)^T$. The complement basis spans a $B^*B$-invariant subspace, and the restriction matrix, trace $569/256$ and determinant $49/64$ are as displayed.
- **The full $12\times12$ characteristic polynomial of $P[N]^*P[N]$ equals $\lambda^7(\lambda-4)(\lambda-\tfrac{337}{128})^2(\lambda-\tfrac{569+33\sqrt{113}}{512})(\lambda-\tfrac{569-33\sqrt{113}}{512})$.** This is (3.2) with seven zeros.
- $(569+33\sqrt{113})/512\approx1.797<337/128\approx2.633$, and $(569-33\sqrt{113})/512>0$. So the eigenvalue 4 is simple, the top singular lines are $\C x$ and $\C y$, and $\|P[N]\|=2$. ✔

**§4, compression bound (l. 225–246).**
- $\langle x,\zeta\otimes u\rangle=(\bar\zeta_3\bar u_1+\bar\zeta_6\bar u_2)/\sqrt2$ up to the inner-product convention, and Cauchy–Schwarz gives $|\cdot|^2\le\tfrac12$.
- The inequality $\|P[N]w\|^2\le4|\langle x,w\rangle|^2+\tfrac{337}{128}(1-|\langle x,w\rangle|^2)$ holds for every unit $w$. Write $w=\alpha x+w'$ with $w'\perp x$. Then $\C x$ and $x^\perp$ are both $P[N]^*P[N]$-invariant, and the largest eigenvalue on $x^\perp$ is $337/128$.
- The bound increases in $|\alpha|^2$ because $4>337/128$, so substituting $\tfrac12$ gives $849/256$.
- The identity $(v^*Pu)(N)=(I_6\otimes v^*)P[N](I_6\otimes u)$ holds symbolically for general $u,v$.
- $\|I_6\otimes v^*\|=1$, and the supremum is a maximum over the compact unit sphere.
- $\sqrt{849}/16\approx1.8211<2$. ✔

**Compactness and limiting steps:** there are none, apart from the maximum principle for polynomials on the closed disk and a maximum over a compact sphere. Both are valid.

**Scope remark (l. 105–109):** The manuscript defines the scalar constant with polynomials. ACV define $\psi$ over $\mathcal A(K_A)$. For this $N$ the two constants agree. $N^4=0$, so $f(N)$ depends only on the first four Taylor coefficients, which are sup-norm continuous by the Cauchy estimates, and polynomials are dense in $\mathcal A(\overline\D)$. The appeal to ACV Theorem 1.6 is therefore consistent. The manuscript correctly leaves $\psi(N)<2$ undecided. The bound $\sqrt{849}/16$ is not claimed sharp. The round-1 probe estimated the true maximum over $u,v$ at about 1.674.

**Abstract and introduction claims:**
- "Irreducible" means unitarily irreducible, which the paper proves.
- "Norming vectors have Schmidt rank two" is correct. $x$ has Schmidt families $\{e_3,e_6\}/\{f_1,f_2\}$, and $y$ has $\{e_1,\ell\}/\{f_1,f_2\}$, with $\ell\perp e_1$.
- "Conclusion fails in general" matches R016's conclusion $\|p(A)\|=2M$: here every $p=v^*Pu$ gives $\|p(N)\|<2=2M$.

## 3. Literature and contribution boundary

- **ACV, arXiv:2608.27346.** v4 is still the latest version: the unversioned abs page says "this version, v4", and its hash `95f0cd10…1262` is identical to round 1. I re-read the following:
  - Theorem 1.6 ("$d\le3$: $\psi_{\mathrm{cb}}(A)=2\iff\psi(A)=2$"). It is cited accurately at l. 108–109.
  - Lemma 5.1 and Theorem 5.3. Theorem 5.3 says that minimal rectangular extremals have norming vectors of Schmidt ranks $r,s$ with mutually orthogonal Schmidt families. "Already permits higher-rank Schmidt families in abstract norming vectors" (l. 57–59) is accurate and appropriately modest.
  - The description of Theorem 12.2 in the introduction (a scalar polynomial equality classification in every finite dimension). It is cited accurately in Remark 4.1.
- **ACV introduction (§1) on the scalar conjecture.** It says verbatim: "Recently, Jin [27] and Lorist and Schwenninger [30] independently proved the scalar conjecture … For (1.2), $1+\sqrt2$ therefore remains the best universal bound." This leads to N1.
- **Crouzeix 2004 and 2007.** ACV §1 confirms that Crouzeix conjectured (1.1) in 2004 and introduced and conjectured the completely bounded version (1.2) in the 2007 paper. The manuscript's sentence at l. 52–53 is therefore accurate.
- **Bibliographic metadata** was confirmed by Crossref: Crouzeix 2004 (IEOT 48(4), 461–477), Crouzeix 2007 (JFA 244(2), 668–690), Crouzeix–Palencia (SIMAX 38(2), 649–655) and LSS (LAA 270, 323–349; authors Chi-Kwong Li, Ilya Spitkovsky, Sudheer Shukla). The Kang entry (Zenodo 10.5281/zenodo.23332163) and the title match R016.
- **Current literature search.** Web searches on 2026-10-13 for complete Crouzeix equality, extremal witnesses, Schmidt rank and scalar compression found nothing beyond ACV and the scalar-conjecture papers. The search was not exhaustive, and this is not a worldwide priority assessment. The contribution claim is modest: an explicit attained instance with a uniform obstruction to every constant compression, with the disk and the pencil disclaimed as known. That claim is consistent with everything I found.

## 4. Required fix

**N1 (literature accuracy; l. 52–56).** The paragraph tells the reader that the scalar conjecture is stated in [2], and that the general bound is $1+\sqrt2$. It omits that the scalar conjecture with constant 2 has been proved. That fact matters here because the paper then discusses whether the scalar constant $\psi(N)$ is below two (l. 105–109). Replace

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
The scalar conjecture has since been proved in the preprints
\cite{Jin,LoristSchwenninger}, and the preprints
\cite{Direct,Structural} address the complete inequality with
constant two. The explicit theorem below uses none of these
general bounds.
```

Add these two bibliography entries:

```
\bibitem{Jin} S.~Jin, \emph{The numerical range is a $2$-spectral set},
Preprints.org, manuscript 202607.1919, version~4, 2026.
\href{https://doi.org/10.20944/preprints202607.1919.v4}{doi:10.20944/preprints202607.1919.v4}.
\bibitem{LoristSchwenninger} E.~Lorist and F.~L.~Schwenninger,
\emph{A solution to Crouzeix's conjecture},
\href{https://arxiv.org/abs/2608.03841v2}{arXiv:2608.03841v2}, 2026.
```

Version evidence for these entries:
- The Crossref record for the v4 DOI exists (title "The Numerical Range Is a 2-Spectral Set", posted 2026-08-07), and `doi.org/…1919.v5` returns 404. So v4 appears current, but preprints.org itself returned HTTP 403 to automated fetches.
- On arXiv, 2608.03841 is at v2 ("this version, v2").

**Optional, with no change to the theorem.** After l. 109, add: "Jin's rigidity theorem \cite[Theorem~1]{JinRigidity} requires $W(A)$ to be a disk when $\psi(A)=2$, so it does not decide the question for $N$." Copy the `JinRigidity` entry from R016's `Jin` bibitem.

## 5. Optional presentation items carried over from round 1 (not required)

These remain unaddressed and are acceptable as written:
- l. 133: add the step through the singular values of $C$.
- l. 149: "The $e_2,e_4$ component of $NN^{*2}e_1$" (the whole vector already lies in that span).
- l. 187: "For example" could be "Explicitly" (the grade-0 domain is one-dimensional).
- §4: add the one-line $w=\alpha x+w'$ justification.
- Add `\subjclass`/`\keywords`.
- Optional O1 (ACV Proposition 12.1): no scalar polynomial attains equality at $N$.

## 6. Not inspected / limits

- Jin's and Lorist–Schwenninger's papers: I did not read them. Their status comes from ACV v4 §1, the arXiv abs page and Crossref. I did not audit their proofs.
- The original LSS article: not obtained. Family membership was checked against Lawrence's reproduction only.
- Proofs in the pinned OpenAI preprints: not audited, as the manuscript does not use them. I checked titles, dates and the existence of the Faber estimate only.
- ACV: I read §1, Lemma 5.1, Lemma 5.2 and Theorem 5.3 in full, and Theorem 1.6 and Theorem 12.2 as stated in §1 (Theorem 12.2's statement was read in round 1). I did not audit ACV's proofs.
- Worldwide priority: not assessed beyond the sources and searches above.

## 7. Sources and retrieval hashes (fetched 2026-10-13; `/tmp/r019-audit-claude-r3/dl/` unless noted)

- Pinned upstream raw files: `direct.tex` `54a429fe7129b4760b3015fabf2269d4de5fa38aba9539b18542c1df7e58333f`; `structural.tex` `8a5de532bd3bd4c0b84cc8114c22175968813a6e984ced0d1bf48011270e621c`.
- arXiv abs pages:
  - 2608.27346 (latest = v4): `95f0cd10f1f32a2313440ff1fbdbb4686dc182bf9e21a9c333fa137a30651262`
  - 2608.03841 (latest = v2): `d31daf096cbadcb5a0f145df443acd28551e31531883f8923b41b301def051f2`
  - 1809.02779 (latest = v2): `f1a4d9d33d87c64fad965f47f64d153a33105d9ae595a8ac08ba2ce03358b2d5`
- ACV v4 HTML (round-1 copy, `/tmp/r019-audit-claude/dl/`): `4b707363b87b71b42cfff746a520da2247f4aa796bc43fb28bb4eebefb0819aa`. Lawrence v2 HTML: `fc158711eee63ea9ffcf90d501799b92b3452d7fc7ade2e30d7b02834b2ae269`.
- Lawrence journal page `oam.html`: `6fef04762b7e57c48cba9a9cf9dd126496453ed951d9e75b71969aec5c2a6f64`.
- Crossref records:
  - Lawrence `50cf2f69…e3f2`
  - LSS `ba5c5014…981d`
  - Crouzeix 2004 `c0676da4…230b`
  - Crouzeix 2007 `3447a079…8ecf`
  - Crouzeix–Palencia `bb62c711…1c371`
  - Jin v4 `c479d113…d814`
- Audit scripts and outputs: `check_r3.py` `daff36333029e55413500be6919d00c6e3e2bc7858be092ba2e2febf3fc5b005`; `check_r3.out` `0b8d84ccaf60e68a8f381513ee716460c68eb35758a294c9fd77db7cbaeff2c3`; rebuilt PDF `7e45228baa6a5b6d9294d1de7f3782dd4d6a48163d64e277d09dce580f5808d6`.
