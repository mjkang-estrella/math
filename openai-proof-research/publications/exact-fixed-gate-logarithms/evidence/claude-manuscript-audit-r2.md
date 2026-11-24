# R021 manuscript audit, round 2 — *Exact discrete logarithms from a flagged polygonal transform*

2026-10-13. Auditor: Claude Opus 5.5 (`claude-opus-5-5`), review sub-agent at the user's explicit request, routed through the configured Factory provider. This is an AI audit, not human peer review.

The pinned OpenAI corpus `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` is stipulated true **only in its theorem statements**. The research pin is `mjkang-estrella/math@d513e308d86a38004d78bab9b9e88532e92bf56c`. I re-read the whole revised manuscript line by line and re-derived every deduction from the manuscript text. I did not rely on the round-1 audit's conclusions; where round 1 was wrong, this report says so.

## Audited artifacts

| Artifact | SHA256 |
| --- | --- |
| `main.tex` (415 lines, mtime 2026-10-13 12:10:42) | `447695b3d1949623c10784d6be1a28ba165bc683d790280b155a0eda62d49b7f` |
| `tmp/main.pdf` (6 pp., CreationDate 12:10:42) | `23c167a1841c67fb36ae1fc7c909491ce1254bdbf35511bb6991f702811a5589` |
| pinned upstream PDF, fetched from raw GitHub at the pin (`tmp/upstream-pdf-r2/main.pdf`) | `35e89279253b6c8ae5ae7c941283b4b9de517243564f87e9b323ffeae4a85699` |
| round-1 source copy (`tmp/audit-rebuild/main.tex`) | `3d84d154bf87d14ae40177a5ca2536f1ef3928ac80087c1caba697bb7270ef6e` |

**Rebuild.** I rebuilt `main.tex` with Tectonic 0.17.0 (`rooted-matching-entropy/tmp/tools/tectonic`, SHA256 `a98aa59a…6da`, `--only-cached`) in `tmp/audit-r2/build/`.
- The rebuilt PDF (`8c3c4872…04ea`) differs from `tmp/main.pdf` only in embedded timestamps and IDs. The `pdftotext -layout` outputs of the two are byte-identical (`dd1446d2…aab`).
- The rebuild log (`tmp/audit-r2/logbuild/main.log`) has no warnings, undefined references, or overfull or underfull boxes.
- I inspected all six rendered pages (`tmp/audit-r2/pg-*.png`, 90 dpi). All displays typeset correctly.

**Revision scope.** `diff` against the round-1 source shows exactly these changes: Assumption 1.1 wording and attribution, the new Proposition 2.1, the parameter sentence at lines 123–124, the sine step at lines 187–190, E6, the citation labels, M1, E4, the closing sentence of §5, and bibliography [1]. All other text is unchanged, and I re-audited it anyway.

## Verdict

**REPAIR. One required citation fix and one required wording fix. No BLOCK.**

- The mathematics is correct. All three round-1 required fixes (M1–M3) and E1–E4 and E6 are correctly made.
- **New defect, R2-M1:** the quarter correction cites "[5, Lemma 6.3]". The pinned upstream has no Lemma 6.3. The intended lemma is **Lemma 5.3**. This error originated in my round-1 audit, which numbered upstream sections by file name (`06-exactness.tex`). Upstream `04-dyadic-order.tex` opens with `\subsection`, not `\section`, so the exactness section is §5. I confirmed this against the pinned compiled PDF.
- **R2-M2:** Theorem 1.2 asserts a *polynomial-time* uniform family, but Assumption 1.1 says only "uniform", and the manuscript never defines that word. Two-word fix below.

## Verification of the round-1 repairs

**M1 — final range test (lines 320–326). Repaired correctly.**
- The guess is a uniform $L$-bit $a'$ with $L=b$, and the branch requires $a'<q$ and $g^{a'}=h$. Since $\operatorname{ord}g=q$, this forces $a'=a$. Since $a<q\le2^b$, exactly one of the $2^L$ guesses passes.
- From $C>1/(2P)-2^{-J_*}$ we get $e<P2^{-L-3}$, so $2^{L+1}e<P/4\le1/4$, a valid dyadic retention.
- Mass: $PC/2+\tfrac12\cdot2^{-L}\cdot2^{L+1}e=PC/2+e=1/4$.
- Exact check, with and without the range test: see "Supporting checks" (q = 5 without it gives 0.256739).

**M2 — bibliography [1] (lines 391–397). Repaired.** The editors, volume title "New Perspectives in Algebraic Combinatorics", MSRI Publications 38, and pp. 91–147 match the MSRI contents page (`tmp/ext-msri/b38.html`, `a0b9c5ae…9a6149`, lines 76 and 103–105). The URL `files/barvinok.pdf` is linked there.

**M3 — Assumption 1.1(1) attribution (lines 70–86). Repaired, apart from R2-M2.**
- I compared it with the pinned PDF, Lemma 3.2 (p. 5): "There is a circuit of size polynomial in $b$ on a $b$-qubit data register and ancillary registers initially in the all-zero state, with a designated ancillary success outcome, such that its unnormalized matrix on that outcome is $A_{k,x}=Q^{-1/2}g(kx/Q)$, $0\le x,k<Q$." The setup line reads $Q=B^{16}=2^b$, $b=16n$.
- So the size is polynomial in $n$, $Q=2^{16n}$, and the manuscript's operator agrees with the lemma.
- The two extra properties are now attributed to the proof, not to the statement. I checked that proof:
  - It prepares $\lvert\chi\rangle$ with Hadamards plus $Z$/$S$ phases.
  - It applies $O(b^2)=O(n^2)$ controlled modular shifts, "with its scratch bits uncomputed".
  - It then undoes the preparation and designates "the all-zero phase-register outcome as success".
  - Therefore, on success every ancilla is $\lvert0\cdots0\rangle$, independent of $x$. Generating this explicit circuit from $n$ is clearly polynomial-time.
- The new wording ("every ancillary register of this circuit") no longer conflicts with the $x$-dependent group register in §2.
- This property is what makes $p_j=\lVert v_{k,l}\rVert^2$ exact: no ancilla stays entangled with $x$.
- "Hadamard preparation" slightly undersells the $Z$/$S$ phases. That is harmless.

**E1 (lines 123–124).**
- $n\ge\lfloor\log_2p\rfloor+1$ gives $p<2^n$.
- $q\mid p-1$ gives $q\le p-1$.
- Hence $Q/q>2^{15n}\ge2^{1920}$, which gives $Q\ge216q$, $M=Q/(2q)\ge2$, and $q<Q$. Correct.

**E2 (lines 185–191).**
- Nonalias means $q\nmid m-1$. Since $q$ is prime and $1\le t<q$, $q\nmid(m-1)t$, so $\operatorname{dist}((m-1)t/q,\mathbb Z)\ge1/q$.
- $|m\eta/Q|\le M/(2Q)=1/(4q)$, so the distance is $\ge3/(4q)$.
- $|\sin\pi v|\ge2\operatorname{dist}(v,\mathbb Z)$ gives $|\sin\pi v|\ge3/(2q)$.
- $|D_Q(v)|=|1-e^{-2\pi iQv}|/|1-e^{-2\pi iv}|\le1/|\sin\pi v|\le2q/3$.
- Weighted by $\sum c_m\le1$, the total is $\le2q/3$. Correct.

**E3 (lines 109–113, 357).**
- Proposition 2.1 states the supplied-prime-order result under item (1) only, and §5 ends "This proves Proposition 2.1".
- Theorem 1.2 now follows in §6 from Proposition 2.1 and item (2).
- The proof has no `proof` environment and runs across §§2–5. That is acceptable; see optional O2.

**E4 (lines 345–347).** "the reflection $2\lvert\psi\rangle\langle\psi\rvert-I$ equals $V(2\lvert0\rangle\langle0\rvert-I)V^{-1}$" is correct. The application order, $I-2\Pi$ then $2\lvert\psi\rangle\langle\psi\rvert-I$, matches the upstream proof of Theorem 1.1, p. 18.

**E5 (citation labels).** I checked each against the pinned compiled PDF (`tmp/upstream-pdf-r2/main.txt`):

| Manuscript | Upstream content | Status |
| --- | --- | --- |
| [5, Lemma 3.2] (line 82) | Lemma 3.2, flagged transform, p. 5 | correct |
| [5, Theorem 1.1] (line 86) | Theorem 1.1, exact factoring | correct |
| [5, Lemma 2.2] (line 337) | Lemma 2.2, "Retained classical records" | correct |
| [5, Lemma 6.3] (line 313) | **does not exist**; the quarter lemma is **Lemma 5.3** ("Quarter-success preparation", p. 18) | **wrong → R2-M1** |
| [1, Theorem 4.4 and Algorithm 5.2] | BP lines 936 and 1056 of `bp.txt` | correct |

Upstream environment structure: §1 has Thm 1.1. §2 has Lem 2.1 and 2.2. §3 has Prop 3.1, Lem 3.2, 3.3 and 3.4 (the `04-dyadic-order` file is subsections of §3). §4 has Prop 4.1. §5 has Lem 5.1, Prop 5.2 and Lem 5.3. The round-1 text "[5, Section 6]" was already wrong, and my round-1 E5 suggestion of "Lemma 6.3" propagated the error. I retract that suggestion.

The optional Imran–Ivanyos citation was not added. That is acceptable, because the manuscript makes no priority claim (see "Contribution boundary").

**E6 (line 305).** $b=\lceil\log_2q\rceil$, and an odd prime $q$ is not a power of 2, so $2^{b-1}<q$. With $B/2$ an integer, this gives $q-1\ge B/2$. Correct.

## Full re-audit of the unchanged deductions (summary)

All of the following were re-derived; none needs change.

- **Phase function and gate set.**
  - (1.1) equals upstream (2): $(1-t)(-i)^s+t(-i)^{s+1}=(-i)^s[1+(-i-1)t]$.
  - The gate set equals that of upstream Theorem 1.1.
- **Assumption 1.1(2) against upstream Theorem 1.1.** Upstream: "polynomial-time uniform family of polynomial-size quantum circuits that outputs the complete prime factorization of every input integer $N\ge2$ with probability one", with gates and qubits polynomially bounded.
  - It is used for $N=p-1\ge2$.
  - The case $p=2$ forces $g=1$, which returns 0 before factoring.
- **Decoder and event (2.2).**
  - $|k_q(j)q/Q-j|\le q/(2Q)<1/2$, so the rounded $j$ is unique.
  - Ties cannot pass the exact formula test.
  - Verification with $a'\in[0,q)$ forces $a'=a$, so $j'=aj\bmod q\ne0$.
- **§3 lower bound.**
  - Fourier coefficients: $c_m=8/(\pi^2m^2)$ for $m\equiv1\ (4)$, with $\sum c_m=1$.
  - Expansion: $mk/Q-t/q=(m-1)t/q+m\eta/Q$.
  - Main term: $16Q/\pi^3\approx0.516Q$.
  - Aliases: $m=1+4qz$, with coefficient sum $8/(27q^2)\le8/243<1/24$.
  - Tail: $\le(4/M)Q=8q$.
  - Total: $Q/2-Q/24-9q\ge5Q/12$ when $Q\ge216q$.
  - Overlap: $|\langle\chi_j,v\rangle|^2\ge(1/3)^4/q$.
- **§4 exact evaluation.**
  - Collision constraint: $|z|\le Q-1$.
  - Cells (4.2): the revised bound $n_v\le Q$ is looser than the true $n_v\le Q-1$ but still valid. Each tuple still has exactly one cell, and the polytope stays bounded.
  - Weight: product of four affine factors with numerators in $\mathbb Z[i]$ over $Q$, so $p_j\in Q^{-8}\mathbb Z[i]\cap\mathbb R$.
  - Stirling chains: $\le4$ extra variables, so dimension $\le13$.
  - The count is a bounded number of BP counts.
  - Symmetry $(x,y,z)\leftrightarrow(x',y',-z)$ gives a real result.
- **§5 completion.**
  - $\tau=2^{-b-8}\le1/(256q)<1/(162q)\le p_j/2$.
  - $0\le e_j<p_j2^{-J-1}$, so $2^{2b+1}e_j<p_j/16$.
  - Per-label mass: $p_jC_j/2+e_j=\tau$.
  - $P_0=(q-1)\tau\ge1/512$.
  - $(1-1/512)^{1024}\le1/4$.
  - The retained-record paragraph matches upstream Lemma 2.2.
  - Reflection identity: $\langle\psi,\psi-2\Pi\psi\rangle=1/2$.
- **§6 arbitrary order.**
  - Order stripping keeps $\operatorname{ord}g\mid m$.
  - Digit step: $(h_\ell g_\ell^{-x_k})^{\ell^{e-1-k}}=\gamma^{(a-x_k)/\ell^k}$, so each target lies in $\langle\gamma\rangle$ and $\operatorname{ord}\gamma=\ell$ meets Proposition 2.1's promise.
  - There are $\le\log_2m$ calls, followed by CRT.
  - $\ell=2$ and target $1$ go to direct testing.
- **Abstract.** Every sentence is supported by the body.

## Required fixes

**R2-M1 — wrong upstream lemma number (`main.tex:313`).** Replace

> We include the final correction, following \cite[Lemma 6.3]{OpenAI}.

with

> We include the final correction, following \cite[Lemma 5.3]{OpenAI}.

**R2-M2 — polynomial-time uniformity in the hypotheses (`main.tex:70`, `:78`).** Theorem 1.2 (line 92) concludes a *polynomial-time* uniform family. Upstream Theorem 1.1 supplies exactly that, and the explicit circuit behind Lemma 3.2 is evidently polynomial-time generable. Assumption 1.1 says only "uniform", which is undefined in the manuscript. Replace
- line 70: "a uniform circuit of size polynomial in $n$" → "a polynomial-time uniform circuit of size polynomial in $n$";
- line 78–79: "by uniform $\mathcal G$ circuits" → "by polynomial-time uniform $\mathcal G$ circuits";
- line 83: "Uniform generation" → "Polynomial-time uniform generation" (optional, for consistency).

## Optional edits (non-blocking)

- **O1 (line 86).** "The prime-order theorem below uses only the first item" → "Proposition~\ref{prop:prime} uses only the first item". The prime-order result is now a proposition.
- **O2 (after line 113).** Add "Its proof occupies Sections 2–5." so the reader knows where the proof ends.
- **O3.** Upstream uses $B=2^n$ and $b=16n$, while the manuscript uses $b=\lceil\log_2q\rceil$ and $B=2^b$. The manuscript never quotes upstream's $b$, so this is not an error. A reader cross-checking Lemma 3.2 may still benefit from the parenthetical "(in [5], the data register has $16n$ qubits)".
- **O4 (line 238).** $0\le n_v\le Q-1$ is the sharp bound. The current $\le Q$ is correct.

## Contribution boundary

- The manuscript says exact DLog algorithms predate it (Mosca–Zalka), credits [5] for the transform, completion and amplification, and claims no novelty for the prime-power reduction. It makes no priority claim.
- The Cai–Young sentence is accurate; round 1 checked it against `tmp/ext-caiyoung/cy.pdf` (`50566598…c370`).
- The staged I324 literature record (`/tmp/publication-r017-r022/…/sources/i324_exact_discrete_logarithm_contribution/literature.md`, `eb4cfad4…c368`) says three things:
  - The Imran–Ivanyos fixed-basis consequence covers only constant-bounded prime factors.
  - Imran 2205.04240 invokes Mosca–Zalka transforms.
  - van Dam uses exact transforms with expected-time retries.
- None of these conflicts with the manuscript's stated scope. I did not re-read those papers.

## Supporting checks (package `tmp/` only)

`tmp/checks/manuscript_r2_checks.py` (`8a60e7b2738eb860c54b5b78c57bd7c46e9043149422273bc37168e0dde7c9b5`) was run with `python3 -I -B`, exit 0. Its output is `tmp/checks/manuscript_r2_outputs.txt` (`6b83fa702a6abd506aa4ef1239f702eeda9a64d46d98958ddf27ddaeb46edf8f`). It reruns all round-1 exact checks and adds the following.

Reruns of the round-1 checks:
- $g_0$ equals upstream $g$.
- The decoder is exact for $q\le13$.
- For $q=3,5,7$ and all $a,j$:
  - $p_j\ge1/(81q)$, with $\min 81q\,p_j$ = 16.34, 11.47 and 9.61;
  - $p_jQ^8\in\mathbb Z$;
  - the completion sums exactly to $(q-1)\tau$;
  - $P\ge3/4$;
  - the quarter identity holds exactly with the M1 range test, and fails (0.256739) without it.

New in round 2:
- (4.2) with $0\le n_v\le Q$: a unique cell and the correct $g_0$ value for every $c,v<Q$, for $Q=16,32,64$.
- The Stirling identity for $d\le4$, $v<60$.
- Float-grid checks of $|\sin\pi v|\ge2\operatorname{dist}$ and $|D_Q(\eta/Q)|\ge2Q/\pi$, plus $16/\pi^3>1/2$ and $8/243<1/24$.
- $1/\lfloor M\rfloor\le2/M$.
- $q-1\ge B/2$ for all odd primes $<2\cdot10^5$, and $(1-1/512)^{1024}\le1/4$ in exact arithmetic.
- The §6 algorithm exactly as written, with a brute-force prime-order oracle standing in for Proposition 2.1. It returned the correct logarithm on all 2,081,756 instances $(p,g,a)$ with $p<400$, using at most $\log_2\operatorname{ord}g$ calls.

These checks use small $Q\ge216q$. The written proofs need only $Q\ge216q$, $M\ge2$ and $4\mid Q$. Numerical checks corroborate the proofs; they are not proofs.

Other files written: `tmp/upstream-pdf-r2/` (listing JSON, pinned PDF and its text), and `tmp/audit-r2/` (rebuild, log build, text extractions, page renders). A stray `tectonic -o /tmp/r021r2log` invocation failed before writing anything; I confirmed that path does not exist.

## Not inspected

- The truth of any upstream theorem (stipulated).
- Upstream §§3.3–4 and the appendix beyond environment numbering.
- The BHMT and Mosca–Zalka bodies.
- The proofs in Cai–Young, Imran–Ivanyos, Imran and van Dam.
- The Barvinok 1994 original.
- Anything beyond the bounded duplicate and literature scans of round 1; there is no priority guarantee.

I made no manuscript edits, commits or index edits, spawned no agents, made no external submissions, and did not touch the main thread or the original checkout.
