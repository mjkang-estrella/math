# H029 independent review — source identities and access

2026-10-08. Evidence handling only: file reads/copies, HTML mathematical-text
extraction, PDF page rendering, and SHA-256 verification. No mathematical
candidate, finite test, replay, benchmark, or sweep was executed.

The independent review froze 40 input files under `H029-review-sources/`.
`H029-review-inputs.sha256` lists each frozen project-relative path and digest.
The copies retain both H029 manifests and all 21 entries of its input manifest,
including the proposer's source notes. Both delivery entries matched as well.
The frozen submitted draft has 300 lines and the expected digest
`dbf3036111778eb9837aba21195265765b9af576d4925eca49b45aba744d7a0e`.
Original inputs and proposer artifacts were not modified.

## Primary sources actually inspected

The following source files are under
`H029-review-sources/research/findings/H029-cover-sources/` unless noted.
The hashes identify the exact bytes read; they do not assert that a moving URL
continues to serve identical HTML.

- **Chris Umans and Siki Wang**, *A number-theoretic conjecture implying faster
  algorithms for polynomial factorization and integer factorization*,
  arXiv:2511.10851v1, 13 November 2025.
  Primary URL: https://arxiv.org/html/2511.10851v1 .
  `Umans-Wang-2511.10851v1.html`, SHA-256
  `8d8834ec4aca25b15a1e7f61b56ee433c91ee3858de7a56fb1c2985398b7a6b5`.
  Read §§3,5–7 and Appendix A.2 for the actual conjecture quantifiers,
  prefactoring premise, modulus domains, CRT characterization, and addition
  sequences. The primary versioned page was also opened successfully during
  this review. This was not an audit of every proof in the paper.
- **Markus Hittmeir**, *A time-space tradeoff for Lehman's deterministic integer
  factorization method*, Mathematics of Computation 90 (2021), 1999–2010;
  DOI https://doi.org/10.1090/mcom/3623 .
  Primary author offprint:
  https://publications.sba-research.org/publications/042021_Hittmeir_A%20time-space%20tradeoff%20for%20Lehman%27s%20deterministic%20integer%20factorization%20method.pdf .
  `Hittmeir-Lehman-time-space.pdf`, SHA-256
  `e1d92d6eb7b40212fc7be9959f62bd6ca0b0df8fb517b5e2a6f7e79e18c0cd30`.
  Read Theorem 2.1 and its adjoining attribution on printed p. 2001, including
  the exact integer eta range, strict lower bound on p, non-strict error bound,
  and positive a,b representation. The page was read in the actual rendered
  PDF, not inferred from OCR. The primary PDF was also opened successfully
  through the web tool. No independent proof audit of Lehman's theorem is
  asserted; it is a cited input to the independently checked H029 derivation.
- **J. Barkley Rosser and Lowell Schoenfeld**, *Approximate formulas for some
  functions of prime numbers*, Illinois Journal of Mathematics 6 (1962), 64–94;
  DOI https://doi.org/10.1215/ijm/1255631807 .
  Retained primary PDF path within that source directory:
  `research/findings/H026-review-Rosser-Schoenfeld-1962.pdf`, SHA-256
  `8e37b06f82e09421bceb2502578c47b61469141f0287e6acedb70e01765ab556`.
  Read printed p. 69 visually: Corollary 1 (3.5)–(3.6) and Corollary 3 (3.8),
  including the real x thresholds 17, 1 and 20.5. The PDF was already present;
  it was not downloaded anew or treated as an H026 reviewer's paraphrase.
- **David Harvey**, *An exponent one-fifth algorithm for deterministic integer
  factorisation*, arXiv:2010.05450, retained HTML identifying version 1.
  Versioned primary URL opened during this review:
  https://arxiv.org/html/2010.05450v1 .
  `Harvey-2010.05450.html`, SHA-256
  `bcd347a997cb82fbc918cac33763762537bc01c797fce3a29f0bc3e0c2c6d0cb`.
  Read §2's integer and polynomial arithmetic, Lemmas 2.1–2.3, Proposition 2.5,
  and §3 through Remark 3.4. In particular, the broad 1/6 ambition is already
  explicit in that remark. The review uses general monic remainder trees;
  it does not assume the unit-dependent geometric evaluator in Lemma 2.4
  applies to arbitrary evaluation points.
- **David Harvey and Markus Hittmeir**, *A log-log speedup for exponent one-fifth
  deterministic integer factorisation*, arXiv:2105.11105.
  Versioned primary URL opened during this review:
  https://arxiv.org/html/2105.11105v1 .
  `Harvey-Hittmeir-2105.11105.html`, SHA-256
  `ae7e7ebc34e4295f971c91cc8276aab785fc60fbc05e24291e79d60c3ed8575e`.
  Read Theorem 1.1, its bit-machine model, and the adjoining all-input reduction
  discussion. This establishes the matched benchmark, not a claim to have
  audited every later development in deterministic factoring.

## Original Lehman access limit

The proposer retained a failed retrieval of
https://www.ams.org/journals/mcom/1974-28-126/S0025-5718-1974-0340163-2/S0025-5718-1974-0340163-2.pdf .
Both its browsing tool and curl returned HTTP 403; the original PDF was not
saved. The original DOI is 10.2307/2005940 as identified in the checked source.
This review neither claims a new successful retrieval nor claims to have read
the original proof or equation (4.6) directly. The exact theorem and the account
of that representation were inspected in Hittmeir's primary paper. Third-party
transcriptions were not used as authority.

## Reviewer-generated reading aids

- `H029-review-Umans-Wang-2511.10851v1.txt`
- `H029-review-Harvey-2010.05450.txt`
- `H029-review-Harvey-Hittmeir-2105.11105.txt`

These use a standard-library HTML parser to retain MathML `alttext` formulae
and readable prose from the frozen HTML. They are derived text, not independent
sources. The original markup remains frozen for resolving any extraction issue.

- `H029-review-Hittmeir-p2001.png`
- `H029-review-Rosser-Schoenfeld-p69.png`

These are local Poppler renderings of PDF pages 3 and 6 respectively, inspected
visually. The user-authorized H029-review-* paths override the PDF skill's
generic temporary/output directory convention. No PDF was edited or re-exported.

`H029-review-delivery.sha256` identifies the completed review, these notes,
the review input manifest, and the five derived reading aids. It excludes
itself. Each reviewed input retains its separate entry in the input manifest.
The coordinator may edit an acceptance version elsewhere without changing
these frozen source identities.
