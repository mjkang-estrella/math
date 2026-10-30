# Independent preliminary review: cascade rate

Reviewer: solo GPT-6.1 Sol, high/default. Review date: 2026-10-29 UTC. Assigned root freeze identifier: 88eb1b426c (supplied by root; no git operation used to verify commit identity). This is an ordinary mathematical review, not acceptance. No count change is authorized. All work is confined to this review lane; candidate bytes were copied and checked against all 20 frozen SHA256 values before review.

**Disposition: ordinary mathematics PASS; substantive eligibility PASS for the explicit geometric-rate refutation only; bounded novelty HOLD; supplement coverage HOLD; literal formal certificate HOLD (absent).** Do not start formal work on the strength of this review alone while the literature/supplement hold remains. Bare convergence is untouched.

## Exact gates

| Gate | Verdict | Exact scope |
|---|---|---|
| Frozen integrity | PASS | All 20 review-freeze hashes match before/after; own copy only. Commit identity is supplied metadata. |
| Published source statement | PASS | Bernoulli 27(3), pp.2015–2019, 2023, 2037: definitions, Eq.(5), Proposition3.1/Definition3.2 and Conj4.2. Actual saved typeset text read, not an abstract. |
| Supplement coverage | HOLD | DOI resolves to an Incapsula challenge, HTTP200 HTML, not a PDF. Actual 2021 supplement unread. Route stopped. |
| Context-tree/source hypotheses | PASS | Saturated binary tree, countably many contexts, exactly one infinite branch, non-null probabilities, no infinite rooted shift-stable subtree. No minimality or finite-alpha-LIS premise is imported. |
| Fixed-series suffix bridge | PASS | Every nonempty proper suffix excluded against all spine nodes and all bush anchors, including unbounded later indices; all-order written argument below. |
| Counting, cascades and rate | PASS | Exact selected-family cardinality; weight 2^(1−n); limsup root=1 in literal Eq.(5) grading. Term and tail geometric bounds fail. |
| Summability | PASS | Kraft/cylinder disjointness gives sum≤2 for this one series. This is classical and uncredited. |
| Substantive eligibility | PASS, scoped | A counterexample to an explicit universal asymptotic-rate assertion, rather than a parameter verification or domain repair. The convergence-only question is unresolved. |
| Classical subsumption | PASS, bounded | No complete same-object implication found in the actual bodies listed below. Kraft alone does not impose the shift and suffix structure. This does not clear all literature. |
| Current registry screening | PASS, bounded | Fresh current heads plus complete relevant trees/catalogue/registry screens; metadata/path screening only. No worldwide priority inference. |
| Overall bounded novelty | HOLD | Supplement inaccessible; no exhaustive citation or specialist literature audit; exact current MathDB target record unread. |
| Literal formal proof/replay | HOLD | No Lean endpoint or literal certificate supplied or constructed. Diagnostic PASS is not formal PASS. |
| Paper/packet acceptance | HOLD | No review of a finished publication packet or extracted strict formal replay. |

## Independent mathematical audit

Use the candidate's a_k=(01)^k00, depths N_k=k²(N_(k−1)+k+10), and spine b=(01)^infinity. Anchors are prefix-incomparable: a_j and a_k first disagree at position 2j+2 for j<k. The proposed internal set is prefix closed. Completing each internal vertex with both children yields exactly the stated internal set: a vertex outside it cannot have an internal descendant. Each departure from b enters one fixed finite bush or an immediate leaf. Hence b is the unique infinite branch, and finite words plus this one branch give countably many contexts.

For any infinite rooted subtree S contained in T, finite branching yields an infinite branch, necessarily b. If S is shift stable, shifting its arbitrarily long b prefixes places every prefix of (10)^infinity in S. But 1 is a leaf of T. This contradiction excludes S, even without assuming S saturated. If 'subtree' is re-rooted at a nonempty vertex, an off-spine descendant tree is finite; a spine-rooted descendant tree again has a single alternating branch whose shifted partner is absent. Thus this ambiguity does not rescue an infinite stable subtree. The source definition is the rooted prefix-word one.

Fix k≥3. Let H=N_(k−1)+3 and divide R=N_k−2k−2−H=kB+r. The selected words are a_k followed by B blocks 11u, |u|=k−2, and r+H terminal ones. R≥0, so these are bottom leaves of bush k. Each tuple of free bits has a distinct word; there are exactly 2^((k−2)B) of them.

Here is the all-index suffix exclusion, independent of finite anchor truncation. A nonempty spine-internal suffix would start with 0; any such suffix of length≥3 cannot end in 111, and suffixes of length1,2 are 1,11. An internal suffix in bush j<k has length<N_j≤N_(k−1), so is wholly in the terminal all-ones run and cannot start with a_j. For j≥k, its initial (01)^j contains 2k consecutive alternating letters. In the tail this is impossible: forced 11-pairs begin every k positions, so every 2k-letter window in the block region contains a complete such pair; windows reaching the terminal run either contain the last block's forced pair or two terminal ones. With no blocks the tail is all ones. Starting inside a_k at a 1 is impossible; starting at its even offset2h>0 leaves only 2(k−h) alternating letters before the 00 defect. Starting at its final zero can extend alternation by at most one more letter before the forced 11 or final run. None supplies 2k letters. At offset zero, a_j for j>k is blocked by the same 00 defect, and j=k is the whole word, not a proper suffix. This treats arbitrarily later anchors without reference to their heights.

Therefore the only internal strict suffix is empty, and the alpha-LIS is the final letter1. Uniform fair q gives exactly N_k−1 factors, hence cascade2^(1−N_k). No q/minimality/continuity assumption is missing: the source permits a redundant iid representation and explicitly defines q for infinite contexts too.

Writing F=(k−2)B and D=N_k−1−F, the selected contribution is 2^(−D). Directly using B≥R/k−1 gives

D/N_k ≤ 2/k + N_(k−1)/N_k + (3k+5)/N_k.

The middle term≤1/k² and N_k≥k²(k+10); thus D/N_k→0. Also D≥0. In Eq.(5) alpha-LIS1 has length1, so the source index equals context length N_k, with no index conversion. All contexts with this alpha-LIS end in1, so κ_1(n)≤2^(n−1)2^(1−n)=1. The lower subsequence bound and upper bound give limsup κ_1(n)^(1/n)=1. A bound Cr^n with r<1 contradicts this; a geometric tail bound implies a term bound. A fixed index shift would not affect the conclusion. The paper leaves 'geometrical rates' informal; Eq.(5) and the bamboo comparison support this intended length grading. Arbitrary enumeration of a countable family is not a source-supported rate convention.

Finally finite context leaves are prefix free. Their fair cylinders are disjoint, so finite sums of 2^(−length) are≤1; increasing finite subfamilies yield the countable bound. Thus sum κ_1≤2. This verifies convergence here, not divergence or a resolution of the remaining convergence conjecture.

## Strongest objection, primary-body comparison and falsifier

The strongest objection is that this is merely a classical slow prefix-code tail in a redundant iid representation. I read Duchi, *Lecture Notes on Statistics and Information Theory*, Theorem2.4.2 and its countable proof/converse (PDF printed p39 onward). Its conclusion prescribes code lengths under Kraft, but does not ensure saturation with only one alternating branch, exclusion of all stable subtrees, or allocation of exponentially many deep leaves to one fixed alpha-LIS. Prefix-incomparable anchors and the all-suffix exclusion are additional, essential word-combinatorial bridges. Applying Kraft without them does not give this counterexample. I therefore do not classify the presented construction as a routine corollary of that statement alone.

I additionally read Cénac et al., arXiv1007.2986, definitions2.1–2.6 and Section4.2.1 including Eq.(19) and Proposition4.32. The bamboo rate comes from a repeated q_1(0)<1 factor. Those formulas do not bound the huge bushes here. The independently fetched arXiv body is not asserted identical to the published 2012 book chapter; the previously challenged HAL route was not revisited. The cached 1909.04475v1 Proposition0.4.5 and Theorem0.4.6 require stability and finite S for the equivalence stated there; they do not resolve this nonstable rate question.

I read Ferreira–Gallo–Paccaut, arXiv1907.02442v2, Theorem3/Corollary4 and AppendixA Lemmas3–4 with their constructions. Lemma4 addresses countable sets with large prefix/suffix growth, making the broad growth idea explicitly classical. It does not establish one fixed alpha-LIS cascade, absence of an infinite stable subtree, or this saturated one-branch realization. Its growth/skeleton is not a complete same-object subsumer. No audit of the truth of these upstream lemmas is claimed.

A decisive mathematical falsifier is one selected word with a nonempty proper suffix in the infinite internal set, or an infinite shift-stable rooted subtree contained in T. A decisive eligibility/novelty falsifier is a pre-existing body giving the simultaneous fixed-alpha-LIS/no-stable-subtree slow cascade construction, or a short explicit implication from an existing theorem that supplies those bridges. Merely citing Kraft or iid stationarity does not do so. A source clarification that rate means something unrelated to length grading would also require reassessment.

The rate clause is an explicit, substantive asymptotic claim: convergence with no exponential moment is structurally different from geometric convergence. Refuting it while preserving the hypotheses is not just changing an endpoint or adding a domain qualification. Nevertheless no credit is warranted unless the separate novelty and formal gates are eventually closed.

## Current screening, chronology and limits

Fresh HTTP heads at 2026-10-29 06:53 UTC: OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a (commit2026-10-26T21:18:03Z); Count dbf673741a54c7dc9d88a6aec0e8148a538f4a3a (2026-09-09T15:24:07Z); Omega5517865965160e8d20e4122aafe4e6c468c6c41d (2026-10-29T06:45:40Z). The first two match the dated04:39–04:43 UTC receipts, whose hashes I verified. Their old immutable registry/catalogue/tree bytes remain explicitly dated receipts, with fresh head equality. Omega advanced from67b4fae; I fetched its current root and complete D5/Problems trees (12,445/1,538 entries, both untruncated) and screened all paths. Exact queries and SHA256 values are in registry-evidence.json. No source/cascade/author match was located. This does not inspect every unrelated proof body or every other Omega directory.

Independent live searches used exact DOI/source ID, Conjecture4.2+cascade, geometric cascade convergence, counterexample/refutation and author/correction terms. No matching prior resolution was located. Search results included the primary source retaining the conjecture, rather than a newly verified proof. The current MathDB probability listing was opened; it is paginated and did not expose the exact target record. An indexed open label is not evidence of novelty. No exact MathDB ID or solution-array claim is made. The 2021 supplement request resolved to a1163-byte Incapsula challenge despite HTTP200; I stopped that affected route. Do not infer a supplement-content clearance from its advertised description or the preprint appendix.

Chronology: source arXiv2020, journal2021; 2012/2019 companion and classical Kraft material predate the construction. The current registry heads above are retrieval anchors, not assertions that every public item predates the candidate. No duplicate was found that required candidate-vs-publication timing adjudication. No worldwide priority, comprehensive citation audit, MathSciNet or zbMATH clearance is claimed.

## Independent exact evidence

independent_check.py is independently written, uses stdlib and exact integers only, and enforces hard512MiB address space,25 CPU seconds, and BLAS/OMP/MKL/NumExpr1. It checks every suffix of eight actual-depth words at k3,4 against all possible anchors by their unique first equal-pair prefix;198 exact integer-bound instances through k200; and a finite-state alternating-run closure for every number of11u blocks, all free bits, for k3…64. The closure is stronger than sampling finitely many block tuples, but finite k coverage is still diagnostic. The general argument above supplies the all-k proof.

The first diagnostic implementation scanned anchors quadratically and exited137 at the CPU limit. diagnostic-failure.json records this failure; independent_check.failed-v1.py preserves its implementation. I replaced the membership algorithm using anchor prefix-incomparability, retaining exactly the same limits, and the revised run passed. No failed run was silently discarded and no limits increased. No numerical test is used as proof, and there is no formal PASS.
