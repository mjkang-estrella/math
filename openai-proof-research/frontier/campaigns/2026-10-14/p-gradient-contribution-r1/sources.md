# I345 contribution review: sources and access

2026-10-14. Companion to `review.md`. Hashes of local files are in `input-hashes.json`. Pinned mathematical truth is stipulated at commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` and is not audited.

## Candidate and internal record

| Item | What was read | Role |
|---|---|---|
| `frontier/experiments/i345_lifted_p_gradient_research/analysis.md`, SHA `f88c4ad3…aa25` | complete, 11 sections | statement (T) and the bridge |
| `frontier/iterations/i345-lifted-p-gradient-research.md` | complete | same statement and the repair summary |
| `frontier/experiments/i345_lifted_p_gradient_research/reading-and-failures.md` | complete | author's reading limits and failed shortcuts |
| `frontier/experiments/i345_lifted_p_gradient_research/input-authentication.json` | complete | author's input hashes; analysis hash matches |
| `frontier/sources/i345_lifted_p_gradient_research/literature.md` | complete | author's interface list |
| `frontier/iterations/i344-affine-lift-p-gradient-route.md`, SHA `ba36168c…` | used as the carried unequal-parameter objection; the repair is in analysis §8 | not a premise |
| `campaigns/2026-10-14/p-gradient-parent/contribution-screen.md` | complete | parent screen, not an independent PASS |
| `campaigns/2026-10-14/p-gradient-parent/ellipticity.md` | complete | explicit constants (b_0²/3) and 2 for the zero-jet form |
| `campaigns/2026-10-14/p-gradient-proof/review.md` and `source-map.md` | complete | conditional proof PASS; not a novelty input |
| `frontier/NEW-TEN-2026-10-14.md`, `AGENTS.md`, `sources/upstream.json` | complete | campaign rules and pin |
| I236 `analytic-attempt.md`, opening statement through the FIT affinity theorem | theorem, contact theorem, and FIT quantifiers | interface only this round |
| I239 parent disposition | hash and recorded PASS, not a new audit | corroboration of the proof gate |
| I240 contribution review | complete | I236 judged TECHNICAL |
| I230 and I241 parent dispositions, I241 high-viscosity note, I230 and I241 literature notes | the disposition texts complete; literature notes used for locators | restricted predecessors |

I236's full contact, flux, and envelope proof was not re-audited in this round. The proof gate records a complete read of SHA `a30077ca…` and a conditional reliance on I239. I240's technical verdict is the contribution status used here.

## Pinned infinity manuscript

Prefix `preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections/` at the pinned commit. Local corpus copy under `frontier/sources/i14_spectral_width_novelty_r3/corpus/`.

- `01-introduction.tex`: read complete for `thm:main`, the 1/3 obstruction, and the proof strategy. The strategy uses a linear lift that preserves the infinity equation and a three-point estimate. The file states no p-uniform theorem.
- A search of the manuscript section files found no p-harmonic or p-Laplace argument.
- Interfaces relied on as stipulated, with the proof review's line locators: `thm:main`, `lem:linear-lift`, `thm:liouville`, `lem:bad-scales`, `lem:cylinder-comparison` (equal parameter), geometric part of `prop:nonaffine-limit`, gradient extraction. `prop:three-point` is not a p-input.

## Primary literature read in this review

### Peng–Zhang–Zhou

Fa Peng, Yi Ru-Ya Zhang, and Yuan Zhou, arXiv:2310.08093v4, and the local text extract `peng-zhang-zhou-pages-1-8.txt` (pages 1–8 of that preprint). Read the introduction through Theorem 1.1, Corollary 1.2, and Questions 1.1A–1.3A. Theorem 1.1 is C¹ convergence of p-potentials to the infinity-harmonic potential on a convex ring, with nonvanishing limit gradient. The introduction distinguishes that statement from C¹ estimates for general p-harmonic functions uniform in all large p.

Pages 14–23 of the same local extract were not re-read line by line in this round. I230's literature note records that those pages contain Lemmas 3.1–3.5, 4.1–4.4, and 5.1–5.2, including Lewis's nonvanishing and quasiconcavity for the potentials. The published article is Proc. London Math. Soc. 130 (2025), e70062. Its abstract was seen through the arXiv/Wiley records. The published PDF was not opened. No claim is made about theorems that might appear only in the unread published text.

The parent screen cites v3. The extract used here is the v4 text retained by I230. Theorem 1.1 and Questions 1.1A–1.3A are in that extract.

### Bungert

Leon Bungert, arXiv:2302.08462v2, HTML and the theorem block of the PDF. Theorem 1 is a value rate under a uniform value-Hölder bound H and boundary data, with an improvement when ess inf |Du_∞| > 0. Remarks 2.4–2.5 concern that hypothesis. This is not a gradient estimate for arbitrary interior weak solutions.

### Lee–Lee

Se-Chan Lee and Taehun Lee, arXiv:2609.09966v1, HTML, read through Theorem A and the compactness lemmas that feed the near-2 statement. Theorem 1.2 is the inhomogeneous C^{p'} conjecture for p in (2, 2+ε_d). Theorem 1.3 is a homogeneous exponent 1/(p−1) + c(p−2) in a possibly smaller neighborhood of 2, with c < 1/2. Theorem A, attributed to Araújo–Teixeira–Urbano, IMRN 2018, Theorem 2, is the reduction: a homogeneous C^{1, α_0} estimate with α_0 > 1/(p−1) implies the sharp inhomogeneous estimate, with constant depending on d, p, α_0, and C_0. The 2018 publisher PDF was not opened. Lee–Lee's quotation is the interface.

### Sobral–Teixeira–Urbano

Aelson Sobral, Eduardo V. Teixeira, and José Miguel Urbano, arXiv:2610.13137v1 (9 October 2026), HTML. Read the introduction, Theorems 1.1 and 1.3, Corollary 1.2, and Section 2 through the iteration in the proof of Theorem 1.1, including Lemmas 2.1–2.3 and the shifted operator (2.1). Theorem 1.1 has C = C(n, p, γ, β). The large-shift limit at fixed p is linear with matrix I + (p−2) e ⊗ e. Theorem 1.3 is a planar infinity-harmonic estimate for every β < 1/3, from Xu's qualitative theorem, and is not a finite-p estimate.

The Iwaniec–Manfredi formula is quoted from that paper as (1.1). Numerical checks in this review: α_IM(3) ≈ 0.729, α_IM(100) ≈ 0.346, and the limit is 1/3; the quantitative exponent they attribute to Baernstein–Kovalev is about 0.574 at p = 3 and about 0.014 at p = 100.

### MathDB 405360

<https://mathdb.com/p/405360/the-c-p-regularity-conjecture>. The HTML shell is client-rendered. The statement, status, importance, and progress summary were read from the remix data payload. Statement: for every n ≥ 2 and every p > 2, locally bounded forcing implies local C^{1, 1/(p−1)}. Status `claimed_progress`, importance `named`, no solutions. Edited 2026-10-13. The progress summary, checked 2026-09-10 by the site's model note, leaves the full conjecture open. This review does not rely on that progress summary for the mathematical comparison; Lee–Lee and the planar Araújo–Teixeira–Urbano theorem are the primary interfaces.

### Kotschwar–Ni, Savin, Uhlenbeck, weak/viscosity

These are classical inputs of the proof, not re-proved here.

- Kotschwar–Ni, arXiv:0711.2291v1, Theorem 1.1: the proof review quotes the statement and constants. This review uses that quotation and analysis §2.1. The flow and entropy sections were not read.
- Savin, CPDE 32 (2007) 557–578, Theorem 1.3 and Proposition 4.1: used through the proof review and the existing page extracts recorded there (pages 1–4 and 14–18). Pages 5–13 were not read in this chain. Family uniformity is the sequence argument in Proposition 4.1 under a common bound on D²F_k, as described by the proof review. This review does not add a reading of those middle pages.
- Uhlenbeck, Acta Math. 138 (1977): analysis §2.2 and the I345 literature note describe (5.4) and (6.1). This review did not re-read the PDF. The non-uniformity in p of the classical theory is taken from Peng–Zhang–Zhou's introduction, not from a new extraction of Uhlenbeck's dependence on p.
- Julin–Juutinen, arXiv:1104.2197, and Juutinen–Lindqvist–Manfredi: weak/viscosity equivalence for the homogeneous p-Laplace equation, p ≥ 2. Not re-read in this round. Used only as the identification already required by the proof gate (U4).

### Koch–Zhang–Zhou

arXiv:1806.01982 is a planar infinity-harmonic Sobolev estimate for |Du|^α. It is the "[KZZ]" item in the older Lindgren–Lindqvist citations. It is not an interior C^{1, α} estimate for finite-p functions uniform in p. The paper was identified from its abstract and was not used as a premise.

## Access limits

- MathDB HTML did not include the statement; the remix data payload did.
- Peng–Zhang–Zhou published PDF: not opened.
- Araújo–Teixeira–Urbano 2018 IMRN PDF: not opened. Theorem A is Lee–Lee's quotation.
- Savin pages 5–13: not read.
- Uhlenbeck proof: not re-read in this round. I345 itself left PDF pages 5–8 unread.
- Tolksdorf: not used. I345 records an HTTP 403 and does not take it as a premise.
- I236 full proof and I239 full audit: not repeated here.
- No claim that every paper on p-harmonic regularity was examined. The negative searches were for a theorem with one Hölder exponent and one constant for all p at least 3, all dimensions at least 2, and no critical-point restriction.

## Hash note

`frontier/NEW-TEN-2026-10-14.md` has changed since the proof review recorded SHA `7cac04ef…`. The file read here is SHA `40f7ae25…`. The candidate analysis hash is unchanged and matches the prescribed value.
