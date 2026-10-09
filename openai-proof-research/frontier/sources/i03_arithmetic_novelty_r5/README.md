# Evidence for arithmetic novelty review r5

Retrieval/review date: 2026-10-08. Parent report: [i03-arithmetic-novelty-r5.md](../../reviews/i03-arithmetic-novelty-r5.md). This directory is an internal source record, not a publication or a claim that public preprints have been verified.

## Scope and reproducibility

`manifest.json` records the immutable pin, 60 inherited primary manuscript files independently verified against SHA-256 and the complete pinned preprint tree, six additional pinned manuscript files, external primary downloads, and required input hashes. `collect.py` reconstructs the collection using pinned raw GitHub URLs and hash-checked inherited files; existing downloads are reused. `collection-result.json` records its successful run. No upstream truth audit is attempted.

The 66 pinned files comprise the D/S/P/T/E collection and bibliography, the two QRH papers, the joint Dickman introduction, the ordinary two-point introduction, and the polynomial-factorization introduction and analytic section. The last paper imports the same 10^-6 Hecke strip: it is not a hidden GRH input. Reading focused on exact theorem statements and contracts relevant to duplication, not on every line of every file. The full catalogue and complete path listing were screened, not all 719 full manuscripts read.

External primary texts:

- Ford–Konyagin–Luca: §6, Conjecture 5, marginal shifted-prime PD and EH.
- Bharadwaj–Rodgers v4 and publisher PDF: Proposition 2; Theorem 7; Lemma 8; Remarks 9 and 10; Theorem 11. Publisher numbering and hypotheses were checked against v4.
- Moree AP v1: Theorems 1–4; GRH is explicit in Theorem 1.
- Goldmakher–Martin–Péringuey v1: §8, particularly Theorems 8.1 and 8.8; upper bounds on small-index events, not positive lower density.
- Murty–Naik v1: Theorem 1 and Remark 1.1; large-sieve-conditional thin count.
- Nongkynrih (2001): publisher scan, Theorem 1, printed p. 47. The publisher download is the entire journal issue; the desired article is pp. 46–52. `nongkynrih-theorem-p47.png` renders PDF page 16 and confirms the factor 1/2 missing in some indexed survey summaries. `downloads-initial.json` records the original download URL/hash. The initial web click timed out; direct publisher download succeeded.
- Carella v14: actual Theorem 1.1, Lemma 6.1/proof and §7; its stronger public claim is explicitly separated from established results. HTML and the arXiv version page are preserved.
- Pollack v1: Theorem 1.1 explicitly assumes GRH. Its presence prevents mistakenly overlooking newer fixed-base uniformity results.

`primary8.json` and `primary9.json` retain web-rendered mathematical statements; the HTML text extraction files may duplicate TeX/MathML representations. Source formulas should be checked in the HTML or PDF, not inferred from garbled plain text. The first HTML text-extraction attempt lacked BeautifulSoup; the collector was repaired to use the standard library, and the final manifest has no failed downloads.

## Search bounds

Search-result files retain the actual returned results, including irrelevant hits and unsuccessful leads. They are discovery records, not primary mathematical evidence. Queries included:

- `"primitive root" "positive proportion" primes fixed integer`
- `"Poisson-Dirichlet" "arithmetic progression" primes`
- `"two" "residue" "dilation graphs" primes`
- `Artin primitive root conjecture positive density unconditional Carella 2026`
- `Nongkynrih Artin conjecture primitive roots quasi Riemann hypothesis positive proportion`
- `"Nongkynrih" "12" "Artin"`
- `"Poisson-Dirichlet" "shifted primes" progression`
- `"Artin" "quasi-Riemann" primitive roots`
- `"Nongkynrih" "Artin" "A ="`
- `"Poisson-Dirichlet" "progressions" primes`
- `"large prime factors" "fixed" "progression" shifted primes`
- `"Simple Proof of the Primitive Root Conjecture" Carella arxiv`
- `"Artin" "Nongkynrih" "0."`
- `"primitive root" "positive proportion" "zero-free"`
- `"dilation graphs" "progression"`
- `site.arxiv.org Carella "Simple Proof" "Primitive"`
- `site.mathreports.ca Nongkynrih pdf`
- `"Nongkynrih" "0.59"`
- `"prime predecessors" "residue"`
- `"Poisson Dirichlet" "primes" "progression"`
- `"primitive root" "zero-free" "positive proportion" -site:scribd.com -site:researchgate.net`

The final repeat (`search-final.json`) used `"Poisson–Dirichlet" "arithmetic progressions" "primes"`, `"primitive roots" "positive lower density"`, and `"dilation" "shared" "residue" "prime" "Poisson"`. Search results alone do not prove nonexistence of prior art. Close leads were followed into primary papers, including the older weaker-than-GRH route and the overlapping Carella claim. No claim is made to exhaust all languages, unpublished work, journals, thesis archives, or consequences of every corpus theorem.

## MathDB attribution

`primary3.json` is the fresh complete rendered view of /p/370026. Its lines 17–22 support the infinitude formulation and “famous”; lines 36–55 are the August-dated progress summary. Lines 90–121 are a separate Solutions area with AI-assisted remarks posted by Shaowu Zhang, including an OpenAI x/log²x claim and a companion claim. Those remarks link revision adc7f124..., not the project pin. No observed score, celebrated badge, or acceptance status is inferred from them.

The parent's required preliminary note reports a retrieved representation without that OpenAI summary. The r4 `primary-and-mathdb.json` does contain the Solutions remark, as does this fresh view. We preserve both observations and do not invent a reason for the retrieval discrepancy. The r5 review recommends relying on pinned P for the mathematical baseline regardless of the page representation. `mathdb-links.json` records the direct link traversal to the Carella manuscript; the date/version are checked at arXiv rather than inherited from MathDB's “undated” description.

## Decision supported

The source comparison supports a substantial plausible new contribution under the accepted corpus, not a worldwide-priority certificate. It leaves the full proof verdict to the stipulated r4 audit. No new theorem is inferred from numerical checks or search absence. The only new computation in this review is the illustrative numerical evaluation of Nongkynrih's threshold; the exact formula and its mismatch with 10^-6 carry the argument.
