# T024W independent contribution and eligibility review (r1)

Myeongjin Kang; no affiliation. Original review prose CC BY 4.0. Original verifier code MIT. No third-party body is copied here; Ford and source passages are cited by retained file and line range only.

**VERDICT: TECHNICAL** for the exact, unchanged T024W52 target, conditional on the separate proof review finding the r53 deduction correct. This review does not assess correctness and draws no conclusion from any proof verdict. It is not DUPLICATE, not INELIGIBLE and not BLOCKED. It is not SUBSTANTIAL under the campaign threshold. No acceptance, nomination or count change is made; the campaign count stays with the parent (16/20 per brief).

## 1. Exact object reviewed

Frozen author packet `frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r53/`, treated as immutable. External SHA256 anchors were checked before the manifest was interpreted; all seven matched:

| file | SHA256 |
| --- | --- |
| manifest.json | 62c538ada22690db7a5da723b46f37dd0f66d39ee31cbae1fc012c64dc6d5256 |
| scope-status.md | 066820343d15154d5ce3e737095287c1c90ba8c68c944acd3069b4ef6b84e012 |
| candidate-proof.md | 3b84f98728697371b4ca34c23b09f01d2442bc72a169395dcdd29e469883681a |
| local-sieves.md | 499f3b67c2a4aeb51eec5b6c9fb1669dc29c99c1c48cf4923515362a9798b8e2 |
| local-coverage.md | 0da74c6445f0b3ac4cded4bf5797309c189665d1f8f79a1446c65a7f9b652bcd |
| contribution-comparison.md | 1417af6c11bf4ea4339c558bf3464ff8192ec34ccd46fa92fe44ef8ed2031c6f |
| reading-limits.md | 9a6e398e273f053437c0628f19865d8e9e4af1d5a991429602afb94558ce3b85 |

Target (scope-status.md, byte-identical to r52): with V(t) the number of distinct positive totient values at most t, for the real variable x tending to infinity,

    V(x + x/log x) - V(x) ~ V(x)/log x,

for every sufficiently large real x, with no exceptional endpoints, subsequence, averaging, two-sided order replacement, growing-H assumption or narrower nominee. This review keeps that scope unchanged. r52 is the same question's earlier unresolved attempt, not a separate result.

## 2. Integrity checks (identity only, never proof)

1. The r53 verifier was read in full before running. It only reads files and prints; it never writes or reseals. Run in place with the external manifest anchor, it returned `PASS_EXACT_INVENTORY`: 44 files, 9 directories, 13223 tree entries, 30 family entries, 22 source blobs, 5 primary bodies. This matches the parent's 44 payloads and 9 directories.
2. Independent of the r53 verifier and its packet-internal tree copy, I loaded the repository's own `sources/preprints-tree.json` (SHA256 eeecc1da…dc5e09b, 13223 entries, `truncated: false`; the packet copy is byte-identical). The two families have 14 + 16 = 30 entries. Their non-PDF blobs are exactly 10 (source024) + 12 (weighted-fiber companion) = 22. For each of the 22 receipts I recomputed the Git blob SHA-1 of the retained bytes, the size and the SHA256, and matched all three against the tree entry and the receipt. All 22 passed. `sources/upstream.json` matches the packet copy and pins fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
3. The 5 primary bodies match primary-identities.json (checked by the r53 verifier). I did not re-retrieve them from their URLs.

## 3. What the antecedents already pay

* **Source024 (stipulated).** Theorem `thm:main` gives V(x) ~ (x/log x) G_m A(1;θ) and V(cx)/V(x) → c for every fixed c > 0. Its mechanism (limits.tex `prop:mass` and `cor:fixed-scaling`, lines 56–136) is the one r53 reuses. Fix the data (d, p_1, …, p_R), count the largest prime p_0 in its endpoint interval by the prime number theorem, sum the reciprocal weights into the common mass M_1(x;H), and compare two endpoints formed from one parameter set. The finite-map lemma (`lem:finite-map`), the extraction/discard machinery and the layered collision comparison (`prop:comparison`) are also source results.
* **Ford, The distribution of totients (retained ford.txt).** Theorem 4 (lines 133–141) gives two-sided order V(x+y) − V(x) ≍ y V(x+y)/(x+y) for y ≥ x^θ with θ admissible. Ford introduces it as obtainable by a simple modification of the proofs of Theorems 1 and 2 (line 133). Lemmas 2.6 and 2.8 (lines 427–541), Lemmas 4.1 and 4.2 with the proof of (4.1) (lines 955–1179), Theorem 16 (lines 1667–1712) and Lemma 6.2 (6.16) with the Theorem 10 proof (lines 1822–1976) supply the labeled exceptional-set estimates.
* **Classical results.** The quantitative PNT, Brun–Titchmarsh, Ford's 2023 coefficient-uniform upper sieves (sieve2023 Theorems 2.4 and 2.5; their statements are taken from r53's credits, and I did not read those bodies), Mertens' theorem, and the Dirichlet hyperbola split.

r52 attempts.md §2 gives a valid counting-set example showing that global regular variation, small total-variation error and uniform short-interval order bounds together do not imply the every-window asymptotic. So some local control of the labeled exceptional families is logically necessary. Simply restating source024 and Ford Theorem 4 does not yield the target.

## 4. Module-by-module comparison of operations

| r53 module | Paid antecedent | Only changed operation | Classification |
| --- | --- | --- | --- |
| Main term (18), (20): \|T_J\| and V(x) through M_1 | source024 `prop:mass` | endpoints (x, x+h] in place of {x/c, x}; PNT with error z·exp(−c√log z) in intervals of relative length 1/log Y | paid fixed-dilation model plus standard PNT |
| (17): tuples versus values | source024 `lem:finite-map` | applied to E_J, D_J, K_J | positive-sum bookkeeping |
| (16): ordered collisions | source024 `prop:comparison`, Ford's three-form sieve | top-layer Q interval translated (determinant and roots unchanged); p_0 counted in a window for i ≥ 1 | uniform interval translation of a paid sieve (already in r52 §3, labelled there as classical) |
| (2): local bad-prime count | Ford Lemma 2.6 | the q-count for fixed b runs over an interval of length l/b instead of [1, x/b]; the reciprocal bad-b sums are unchanged | translated two-form sieve |
| (5): local S-niceness | Ford Lemma 2.8, whose proof bounds Σ_p V(x/(p−1)) | split at p = √Y: small p uses Ford Theorem 4 on the cofactor window; large p reverses the order and uses (2), then Σ_w 1/w by partial summation | Dirichlet hyperbola decomposition, each half paid |
| (7), (8): local Ford Lemmas 4.1 and 4.2 | Ford Lemma 2.4 / sieve2023 Theorem 2.4; Ford's θ-mesh | y/m replaced by h/m in the rough-number count; the mesh, exponents and factorial sums are unchanged | translated sieve plus range checks |
| (9)–(11): local Ford (4.8) / Theorem 16 | Ford proof of (4.1), lines 1109–1179; Theorem 16, lines 1667–1712 | the count of q_0 (Ford: x/(m log x)) is replaced by h/(φ(r) log Y); the reciprocal R_{j−1}, the suffix sums and the terminal sums are unchanged | free-variable recount in a short interval |
| (12): local Ford Theorem 10 | Lemma 6.2 (6.16)–(6.20), Lemma 6.1 | the same q_0 recount inside (6.16); the geometry is unchanged | same |
| (13): smooth-tail coverage | source024 extraction | p_0 count in the window | same |
| (14): discarded tuples | source024 `prop:discard` | p_0 count in the window; p_0's S_0-normality via (2); the i = 0 square case uses the global bound's exp(−exp(cB/m^20)) saving, which absorbs the log Y loss | bookkeeping |

## 5. Is the pre-good uniform exceptional-preimage localization a load-bearing new tool?

It is **load-bearing for the deduction**: by r52 §2, some local estimate of this kind is needed. It is **not a genuinely modified tool**. It is classical bookkeeping, for three concrete reasons.

1. **The "every preimage / before a good representation" quantifier is inherited, not created.** Ford's Lemma 2.8, Lemma 4.2, Theorem 16 and Lemma 6.2 already count totients having *some* preimage with the defect. Their proofs overcount by summing over all structured preimages n, and so does r53. Restricting φ(n) to J rather than [1, x] leaves that overcount structure intact. No step had to handle values whose preimages are unknown in a new way.
2. **Every Ford exceptional estimate factors as (reciprocal weight) × (count of one free variable), and only the free count is interval-sensitive.** Ford already establishes the size condition that makes a short-interval count possible. In the proof of (4.1), inequality (I_0) gives x_2 < 0.9, hence q_0 > x^{1/3} and m < x^{2/3}, after which q_0 is counted as x/(m log x) against reciprocal weights (ford.txt lines 1127–1136). In Theorem 16, p_0 ≥ x^{1/4} and the PNT counts p_0 given the rest (lines 1685–1700). r53 local-coverage §1 re-derives this same consequence of the first simplex inequality and recounts q_0 in an interval of length h/φ(r) ≥ Y^{0.3}/log Y. Upper bounds only need Brun–Titchmarsh there. The reciprocal suffix bound (11), the simplex volumes, Lemma 6.1 and the terminal sums are all reused unchanged; the author says so explicitly.
3. **The one place where the free variable can be small (Lemma 2.8) is closed by the standard hyperbola split.** Ford's global proof sums V(x/(p−1)) over bad p. Locally, when p ≤ √Y the cofactor window sits at height ≥ √Y with relative length 1/log Y, so Ford Theorem 4 applies (y ≥ x^{0.9} holds since (x/p)^{0.1} ≥ log Y). When p > √Y, reversing the order puts p in an interval of length h/w and the translated Lemma 2.6 applies. Both halves are paid estimates, combined by positive summation.

No new sieve estimate, cancellation, structural construction, geometric inequality or genuinely new parameter regime appears. The Ψ ≤ √m restriction of local Theorem 16, the S < F ≤ T^{1/10} mesh checks and the q_0 = q_1 case are range bookkeeping. They are needed for correctness, but they do not change any estimate. Ford's own remark that short-interval bounds follow from a simple modification of the Theorem 1/2 proofs is consistent with this, but my classification does not rest on it. I did not read a written localization of Lemma 2.8 by Ford (see §9).

## 6. Why the local Ford16/10 "before a good representation" statements are routine

They are new as literal statements: neither Ford nor source024 states them for windows of length x/log x. They follow because both proofs count p_0 last against reciprocal weights that do not depend on where the value lies. Ford Theorem 16 bounds the first-failure terms M_j through (4.8), and the terminal term through PNT for p_0. Lemma 6.2 obtains (6.16) by the same argument and then uses only volume geometry. Recounting p_0 in (x/D, (x+h)/D] multiplies each term by h/x up to 1 + o(1), uniformly, once p_0 ≥ Y^{1/3} is known; Ford's (I_0) argument already supplies that bound. The non-nice preliminaries are handled by (5) with an explicit B^{−32/3} margin. The answer to "why routine" is the factorized form of Ford's proofs, not their difficulty.

## 7. Cheapest paid route and the exact operation needed

1. Take source024 `prop:mass` with endpoints x and x + h for h = x/log x, all parameters formed from Y = 2x and H fixed. The p_0 count needs the PNT with the de la Vallée Poussin error in intervals of length ≍ z/log z. This gives |T_J| = (h/log Y)(M_1 + o(G_m)).
2. Apply `lem:finite-map` on J. It needs |E_J| + |D_J| + K_J ≤ (ε_H + o(1)) h G_m / log Y.
3. Obtain these three bounds by a single operation. In each paid global exceptional estimate (Ford Lemmas 2.6, 2.8, 4.1, 4.2, the (4.8) chain, Theorem 16, Lemma 6.2; source024 smooth-tail, `prop:discard` and `prop:comparison`), keep every reciprocal or volume weight and recount the single free largest variable in the window. Use Brun–Titchmarsh for upper bounds, translated Ford sieves when primality of a linear form is also imposed, and a hyperbola split at √Y in Lemma 2.8, where the free prime may be small. The required largeness of the free prime comes from Ford's own (I_0) consequence q_0 > x^{1/3} (ford.txt line 1127).
4. Divide the formulas from steps 1–3 using source `prop:mass` at x and Ford's lower order bound. Let Y tend to infinity, then H.

r53 follows this route, with the quantitative PNT in some places where Brun–Titchmarsh suffices. It adds nothing beyond it that changes an estimate.

## 8. Why not DUPLICATE, INELIGIBLE, BLOCKED or SUBSTANTIAL

* **Not DUPLICATE.** Source024 states only fixed c (`thm:main`, `cor:fixed-scaling`); its fixed-scaling proof uses an endpoint set {x, x/c}, never a moving window. The source's least-preimage companion section concerns ℓ(v)/v and states no window asymptotic. The weighted-fiber companion proves large fibers and smooth shifted primes; its short-interval material (04-shifted-correlations.tex lines 536–548, 730–740) concerns shifted-prime correlations, not distinct values. The pinned catalogue (sources/CONTENTS.md) lists no other totient-value family. The pinned `lean/docs/024.md` scope lists only the asymptotic, fixed-c regular variation and the least-preimage counts. Ford gives only ≍. The target implies source024's fixed-c corollary: iterate the window about log c · log x times, each step multiplying both x and V by 1 + (1 + o(1))/log x uniformly. Since source024 (stipulated) presents that corollary as answering the open Erdős–Hall question, pre-2026 literature cannot contain the target. Bounded searches found no 2026 statement. In project history, the earlier totient work (fresh-arithmetic-discovery-r1/r2, totient-recovery-r3, arithmetic-r2-parent) concerns least-preimage ratios, not this target. proposals/number_theory.md line 188 records that no moving-scale interval theorem follows automatically from source024. No totient result is accepted in the ledgers. r52 is this question's own unresolved predecessor.
* **Not INELIGIBLE.** It is a genuinely stronger statement than any stipulated source theorem, in a family with no accepted campaign result, and the scope is unchanged from the r52 freeze.
* **Not BLOCKED.** All needed source, companion and primary passages are retained and authenticated; the comparison above did not need unread material to reach its verdict.
* **Not SUBSTANTIAL.** The new content is the localized error budget of §4. Every component is an operation the brief lists as non-substantial: uniform interval translation of paid sieves, the hyperbola decomposition, positive-sum bookkeeping, the paid fixed-dilation model and the standard PNT. Assembling them, or the number of modules, does not change that. I agree with the author's TECHNICAL recommendation for the independent reasons given in §§5–7.

## 9. REQUIRED and OPTIONAL

REQUIRED (on any use of this verdict):

1. This verdict is conditional on an independent proof PASS on exactly the anchors in §1. It must not be read as evidence of correctness.
2. Any recording must say TECHNICAL. It must keep the full every-endpoint target with no narrower nominee, and must not change the acceptance count on this basis.
3. Credit correction for any write-up. The step "first simplex inequality plus Ω cutoff gives a large q_0 with small cofactor" (r53 local-coverage §1 and the closing sentence of its §2) is Ford's: the proof of (4.1), ford.txt lines 1127–1136, and Theorem 16, lines 1685–1700. It must be credited as such, not as an r53 mechanism. The local collision bound (16) must be credited to r52 §3 together with source `prop:comparison` and Ford's sieve.

OPTIONAL:

1. In every upper-bound count of a free prime, Brun–Titchmarsh can replace the quantitative PNT. The PNT is needed only in the main term (18). This makes the routine nature of the localization clearer.
2. A write-up can note that the theorem strictly strengthens source024's fixed-scaling corollary (the iteration in §8).
3. Reading Ford's 1998 Ramanujan J. original, or any written proof of his Theorem 4, could show whether a local Lemma 2.8 is already written there. That could only strengthen TECHNICAL; it cannot move the verdict to SUBSTANTIAL.

## 10. Exact reading and search limits

Machine-readable detail is in coverage.json.

* **r53 public files.** I read all in full: candidate-proof.md, local-sieves.md, local-coverage.md, contribution-comparison.md, reading-limits.md, scope-status.md, chronology.md, checkpoint.md, manifest.json, verify.py, primary-identities.json and primary-reading-ranges.json. The inventory and receipt JSONs were processed by script only.
* **Source024.** limits.tex lines 1–140; statements.tex lines 1–80 of 210; introduction.tex lines 55–109 of 109; companion.tex lines 95–112 and 300–323; README in full. The rest was only searched by keyword across all eight .tex files and the theorem/label index. Not read as bodies: extraction.tex (703 lines), collisions.tex (427), layers.tex (430), statements.tex lines 81–210, limits.tex lines 141–515, main.tex and references.bib. My comparison uses only their statement labels as r53 cites them. Their mathematics is stipulated, and this review does not depend on their internal proofs.
* **Weighted-fiber companion.** I read 07-totient-conclusion.tex in full, the 00-introduction.tex theorem statements (lines 10–16 and 38–44), 04-shifted-correlations.tex lines 536–548 and 730–740, and the README. Sections 01, 02, 03, 05 and 06 and the rest of 00 and 04 were keyword-searched only and not read as bodies, and neither were preamble.tex, paper.tex and references.bib. Its further Poisson–Dirichlet companion (family 011) was not opened beyond its catalogue entry.
* **Ford (ford.txt, pdftotext of the retained PDF).** Lines 1–30, 128–150, 420–579, 955–1179, 1500–1520, 1667–1712 and 1855–1900, plus keyword searches of the whole file. I did not read ford-sieve2023.txt or tao-pnt.html. The full Ford paper, including Theorem 1's lower bound, Sections 5 and 7 and the Theorem 10 proof lines 1966–1976, was not read in full. No written proof of Theorem 4 occurs in the retained text, as far as keyword search for "Theorem 4", "short" and "admissible" shows. The 1998 original was not retrieved.
* **Project history.** I read r52 attempts.md in full (100 lines), the t024w-parent contribution brief and the first 60 lines of intake.json (as an identity record only), totient-recovery-r3/checkpoint.md lines 1–40, and keyword hits in proposals/number_theory.md, frontier/NEW-TEN-2026-10-14.md, TEN-FINDINGS.md and TWENTY-FINDINGS.md. A repository-wide "totient" filename search is listed in coverage.json. No proof-review directory for T024W was opened.
* **Literature.** Three web searches (queries in coverage.json) and one fetch of pinned `lean/docs/024.md`. The search results surfaced only Ford's paper (arXiv 1104.3264, whose Theorem 4 matches the retained text) and unrelated items. No exhaustive priority search was made.
