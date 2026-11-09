# Independent prior-first review: EXCLUDE

Reviewed 2026-10-30. Scope: one family, both classes, every integer r≥1 and n≥0. Recommendation to root: **EXCLUDE from discovery credit and stop investment.** This is exact public subsumption, not an objection based on shortness, numerical agreement, or classical Lagrange inversion alone. Counts remain 9 additional / 39 total / next 40; only root accepts or counts.

## SOURCE

The frozen target is Downing–Hartung–Lucido–Williams, *Pattern Avoidance for Fibonacci Sequences using k-Regular Words*, arXiv:2312.16052v4, p17 Conjecture 1, Eq(24), https://arxiv.org/pdf/2312.16052v4. It asks for the common enumeration of Av_n^r(123,121) and Av_n^r(132,212). Its introduction p1 defines an r-regular word as a word with exactly r occurrences of each member of [n]. Patterns here are classical subsequences with repeated-value order isomorphism; the separate vincular discussion does not change Conjecture 1. The source itself calls these two cases unresolved. That description is not reliable novelty evidence in light of the earlier bodies below.

The precise cited predecessor, from the frozen primary bibliography pp19–20, is Markus Kuba and Alois Panholzer, *Enumeration formulæ for pattern restricted Stirling permutations*, Discrete Mathematics **312**(21) (2012), 3179–3194, DOI https://doi.org/10.1016/j.disc.2012.07.011. Crossref independently confirms identity and November 2012 print issue, with DOI record created 2012-07-28. Metadata was used to locate/identify sources, never as proof-body clearance.

**The previously missing body was obtained.** OpenAlex's frozen record exposes the original institutional source URL in its CiteSeer provenance: http://www.dmg.tuwien.ac.at/kuba/preprintStirpattern.pdf. The corresponding HTTPS institutional author route returned the complete PDF (200), frozen before extraction/reading: https://www.dmg.tuwien.ac.at/kuba/preprintStirpattern.pdf. It has the exact title and authors, and title-page date September 28, 2010. The theorem/page references below are to this author preprint, not an uninspected publisher typesetting. The internal 2010 date is not an independently certified deposit timestamp; the 2012 publication identity and later primary reuse corroborate the chronological priority needed here.

Actual body read: definitions pp1–3; increasing-tree and block constructions pp3–4; Theorem 5 and its complete proof pp6–8; Theorem 8 and its complete decomposition/extraction proof pp9–12; Theorem 9 and its complete insertion/kernel proof pp12–13. These are the nearest proofs, not abstracts or formula-only citations.

Independent primary corroboration: Kuba–Panholzer, *Stirling permutations containing a single pattern of length three*, Australasian Journal of Combinatorics **74**(2) (2019), 216–239, https://ajc.maths.uq.edu.au/pdf/74/ajc_v74_p216.pdf. Read definitions pp216–220, complete §4.1 pp223–225, and §5.1 pp230–232 (including Lemma 1's insertion proof); also the kernel discussion pp233–234. Section 4.1 explicitly re-proves the earlier avoidance result, with Eq(7) F=1+zF/(1-zF)^k and Eq(8) its all-k coefficient formula. Section 5.1 explicitly identifies the 123-avoiding series with that series by the earlier generalized Simion–Schmidt correspondence. Its changed convention for counting *positive* pattern occurrences by distinct value tuples makes no difference to avoidance: zero tuples iff zero classical subsequences.

## Complete prior-to-target bridge

Let Q_{n,r}(α) be the 2012 author's r-Stirling permutations avoiding α. The body pp1–2 proves/defines these as exactly the r-regular words avoiding 212. This uses all equal-letter pairs: everything between two occurrences of i is ≥i. Thus it is exactly the target's multiplicity and alphabet convention, including r=1, not a different notion of higher-dimensional permutation.

Let c replace each letter a by n+1-a, and let R reverse positions. Both preserve multiplicity and are involutions. Complement sends 121 to 212 and 123 to 321; reversal sends 212 to 212 and 321 to 123. Consequently

    R c : Av_n^r(123,121)  ≅  Q_{n,r}(123).
    identity : Av_n^r(132,212) = Q_{n,r}(132).

Theorem 5 gives Q_{n,r}(123) ≅ Q_{n,r}(132), for every r≥1 and n. Its proof fixes the positions and values of weak left-to-right minima, and fills other positions with respectively the largest or smallest remaining value above the current minimum. Between successive weak minima, nonminimum letters occur in complete r-blocks; rearranging those blocks in the specified order preserves 212 avoidance. Thus this is a genuine bijection of the same Stirling classes, not a Catalan permutation analogy. Reversal also gives Q_{n,r}(132) ≅ Q_{n,r}(231).

Theorem 8 enumerates Q_{n,r}(231) by exactly

    sum(j=0..n) binom(n,j)/(n+1-j) * binom(n+(r-1)j-1,n-j).

Its proof splits according to whether the maximum block n^r is an outer block. In the first case σ=A n^r B with A≺B≺n. Otherwise n^r lies in a j-block; the forced decomposition is A j^ℓ n^r R_{r-ℓ} j ... j R_1 j C_0 ... C_t, 1≤ℓ≤r-1, with the R's decreasing strings of complete r-blocks and the C's independently avoiding 231 on the forced consecutive label intervals. This yields, with the empty object included,

    Q=1+zQ²+sum(ℓ=1..r-1) z²Q²/(1-zQ)^(r-ℓ),
    Q=1+zQ/(1-zQ)^r.

The disjoint decomposition fixes label allocations through their order constraints; it is an ordinary generating series in the number n of distinct letters. Its Eq(8) sets W=zQ, giving W=z(1+W/(1-W)^r); Eq(9) performs precisely the target's Lagrange extraction and binomial identity. Theorem 9 independently gives the same formula directly for Q_{n,r}(123).

This covers BOTH target classes for ALL r and ALL n. For n=0 there is one empty word; the formula means binom(-1,0)=1 in its only summand, or, equivalently, define the n=0 value separately as 1. For n>0 the j=0 term is zero. For j≥1 all upper binomial arguments are nonnegative and the denominator is positive. There is no missing boundary, parameter specialization, or finite-to-universal step.

## MATH

The proposed PROOF.md is mathematically sound with the stated empty-case convention. No finite diagnostic is used in this assessment.

Route A: 121 avoidance forces the smallest copies into a contiguous block. Deleting it and standardizing is a unique parent; insertion preserves 121. Any new 123 must start in that block, so legality is exactly a weakly decreasing right suffix. The s+1 legal gaps have suffix lengths t=0,...,s; t=0 gives label s+r, while t>0 gives exactly t because the boundary from the new minimum to the right suffix is strictly increasing. Distinct legal gaps give distinct words and sibling labels.

Route B: 212 forces a contiguous maximum block and a unique deletion parent. New 132 occurrences must have that new maximum in the middle, so the cut criterion is precisely all left letters ≥ all right letters, including vacuous boundaries and equal letters. For k separating cuts indexed 0,...,k-1 and label s=k-1: insertion at 0 creates r cuts before/inside the block plus k after, hence label s+r. At j>0 only the initial cut survives before the block; every other earlier/internal cut has an old smaller letter left and the new maximum right. The k-j old separating cuts at/after the insertion survive after it, hence label k-j. A previously nonseparating cut has a witness a<b across it, which insertion cannot remove; none is repaired. This proves exactly one child of each label 1,...,s,s+r. The root has s=0. Unique parents, unique insertion positions and distinct sibling labels prove exhaustive labeled-tree equality for both families.

Kernel: z-coefficients of F(z,u) are finite polynomials of degree ≤rn, so substitution of U∈1+z Q[[z]] is legitimate despite U's nonzero constant term. The cleared kernel at z=0 is 1-u with derivative -1, giving a unique formal root U(0)=1. Evaluation gives U-1=zUA and then A=1+zU^r A with U=(1-zA)^(-1). Only units are inverted. With W=zA, Lagrange inversion gives (n+1)^(-1)[t^n](1+t/(1-t)^r)^(n+1); expanding and using binom(n+1,j)/(n+1)=binom(n,j)/(n-j+1) is the literal Eq(24), with the boundaries above.

A caution in the predecessor: the author preprint's displayed recurrence (10) prints F_{0,0}=0, inconsistent with its following Eq(11)'s constant 1; the bivariate summation bound also prints m≤n rather than m≤rn. These are visible transcription/typesetting defects, not assumptions silently adopted here. The unique empty object, the actual insertion proof, and the independently derived Theorem 8 establish the intended initial condition F_{0,0}=1 and the correct label range. The subsumption argument does not depend on the defective displayed initial condition.

## SUBSTANTIVE

**EXCLUDE.** There is an exact old all-r theorem, not merely a routine consequence of generic enumeration technology. In addition, Route A is literally Theorem 9's generating tree transported by Rc. Under Rc, its decreasing suffix becomes the nonincreasing prefix of a 123-avoiding Stirling word. Theorem 9 calls its length m (index of the first ascent); inserting the new maximum at the beginning gives m+r, and after position ℓ=1,...,m gives ℓ. This is precisely the proposed rule 1,...,s,s+r and the same kernel. Route B supplies another realization of an already enumerated class; Theorem 5 plus reversal already supplies the complete all-r bridge to that class. A new presentation or direct bijection is not new mathematical outcome credit under the campaign standard.

The increasing-tree correspondence in the predecessor is with (r+1)-ary increasing trees, constructed recursively at the r copies of the minimum. Unrestricted tree counts alone would not settle these restricted classes. Here the actual restricted decomposition, bijection and insertion proofs do; there is no appeal to an unproved insertion-tree analogy. The old A109081 Hanna 2009/Callan 2007 r=2 information is credited as background only and plays no role in exclusion.

## NOVELTY / chronology / access limitations

Historical subsumption is decisive: author preprint internally dated 2010, identified published article 2012, full primary re-derivation 2019, target first arXiv submission 2023-12-26, target v4 2026-01-16. The last two dates are in the frozen arXiv feed and v4 title page; target journal issue is marked 2025 and acceptance 2025-05-15. No chronology claim depends on a current search result being absent. No attempt to certify worldwide priority is made or needed to exclude an already proved result.

No forbidden current registry loop or historical HEAD loop was run. GitHub API/raw/codeload/diff/patch, ScienceDirect, and Google challenge routes remained parked. The inherited author papers.html 404 and info.tuwien.ac.at timeout remain preserved in frozen/FAILURES.md and failures.jsonl; they were not retried. The successful Kuba PDF URL was disclosed in a frozen provenance record, not guessed. OpenAlex/Crossref were discovery/identity aids; the inspected author/publisher PDFs provide the mathematics. The ScienceDirect URL appearing in metadata was not followed, nor were Elsevier API alternatives used to bypass it.

Two Bing discovery responses were irrelevant lexical results, not credible source coverage. Their HTML includes PoW configuration; no script or challenge was executed and no further Bing request was made after inspection. Retain these as unusable retrievals, not negative novelty evidence. The arXiv restricted-title search returned zero records; it is likewise not clearance. Current comprehensive public-registry state remains unknown under the inherited restrictions. That bounded limitation cannot undo an exact pre-2023 primary proof already in hand.

## FORMAL-FEASIBILITY

The finite-word deletion/insertion bijections and polynomial-in-u formal series argument appear formalizable, but a literal Lean certificate would require substantial combinatorial and formal-series infrastructure. No existing Lean endpoint was inspected or certified. No Lean or manuscript work was performed. The decisive old theorem makes further investment for discovery credit inappropriate.

## Provenance and verification

Scientific inputs were frozen before content reading; administrative ledger/context/AGENTS files are snapshots only. freeze.json binds each selected source/scout input to its original and this lane's copy. Retrieved bodies were written to retrieved/ and frozen-new/ with equal SHA256 before extraction/reading; access.jsonl records exact URL, UTC, status, bytes and hash. No historical tree was recursively copied. The initial filesystem inventory was accidentally overbroad and its filename-only output truncated; it did not read scientific bodies. Subsequent reads were bounded and targeted. PROOF.md was read in the initial frozen target/reference inspection before the 2012 retrieval; scientific investigation then prioritized closing the missing predecessor body before substantive investment.

Key frozen hashes:

- Target v4 PDF: 8fe1c6b46af32e4ec69d10f38b351112ddd7f11d72a7eada16271f02756205cf.
- Kuba–Panholzer author preprint: f323744130a9aa5fbfb564de45d22c95c45bb9092cd7e5caf43c337f44df483e.
- Kuba–Panholzer 2019 publisher PDF: 7436b4f58e5d9c335a24c0fd930caa4c491fca6f8f4c41c6d85e8170d157afd0.

manifest.json excludes itself and verification-receipt.json. A separate guarded verification after all other writes checks every manifest member, all original/copy input bindings, and new retrieval/frozen bindings. See verification-receipt.json for the actual result. All helpers run under the specified helper_guard.py with AS/group RSS 512 MiB, CPU 210s, wall 230s and single-thread environment; no caps were raised. No new finite mathematical checks were needed after decisive subsumption. No shared/git/public/browser/MathDB/count edits, children, Lean or manuscript.
