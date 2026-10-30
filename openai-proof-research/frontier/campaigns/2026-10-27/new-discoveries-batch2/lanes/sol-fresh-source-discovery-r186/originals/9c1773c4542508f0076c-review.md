# Independent adversarial review: MathDB336466

Date: 2026-10-26. Reviewer: matrix lane, independent of the author. **Mathematics PASS; exact source scope PASS; frozen formal replay PASS50. Recommend acceptance as one source-conjecture resolution under the documented-prior/no-known-prior-resolution standard, with the explicit Toda1934 literature limitation below.** No source files, shared indexes or original candidate artifacts were edited. No git operation or additional agent was used.

## Exact source and claimed scope

I independently retrieved the current abstract record and exact [arXiv:1706.08381v2 PDF](https://arxiv.org/pdf/1706.08381v2), read the relevant definitions and statement, and visually inspected the original PDFpp1 and9. The source is Wojnar–Wojnar–Brin, *Universal Linear Mean Relationships in All Polynomials* (the abstract-record title additionally contains “Peculiar”). The current arXiv record listsv2,23Oct2017, and no journal reference. The source PDF's2022 typesetting timestamp is not an additional author revision. The newly downloaded PDF matches the author's preserved source byte-for-byte, SHA256 `900bfb840c8e0f271ea3f534548d72717c84a386a6d0f2cbe1fb6510a88a0d94`.

Section1 explicitly defines the root families as **multisets**, including repeated roots; their sizes are D and D−ρ. Conjecture2 in §4/PDFp9 states exactly the alternating binomial sum over0<ρ<D for every odd-degree complex polynomial. The formal target uses those same indices, evaluates the original polynomial on the derivative roots, and divides by D−ρ. It does not assume real-rootedness, simple roots, monicity, generic coefficients or a bounded degree. It proves neither the source's other conjecture nor the dimension/classification of all possible mean relations.

The live MathDB post has UUID `94fe4f13-4cb4-435e-b196-3789d929c445`; the independently preserved snapshot remains open with no posted solution/comment/model-attempt/human-solve entries. Such status is context, not novelty evidence by itself.

## Adversarial mathematical checks

I read the complete written proof, SHA256 `819922170713f14aaf2987499f8861fce4b5dfc257ad790559d5521639ebb31d`, and all six modules. The following are the potential failure points I checked explicitly.

1. **Normalized moments beyond the root count.** The monic Newton identity is used for every moment order i≥1, with coefficient c_i=0 above the polynomial degree. For i>m it becomes the homogeneous Newton recurrence, not an unjustified continuation of the inhomogeneous formula with nonzero higher coefficients. `monic_newton_coeff` establishes this using `esymm_of_card_lt` and vanishing binomial coefficients. Consequently `normMoment_eval_roots` really holds when i>m, as needed when evaluating a degreeD polynomial on the roots of a lower-degree derivative.

2. **Polynomial continuation and zero parameter.** The quotient binomial polynomial is defined by a descending Pochhammer product, with no division by the parameter T. Its degree is i−1. All recursive terms for q_i have degree at most i−1. The evaluation q_i(0)=(-1)^i a_i follows from the actual product and the factorT in every other recursive term; q_0=1 agrees with a_0=1. Thus Φ is a genuine polynomial of degree≤D−1. Its value at0 is never interpreted as an average over the roots of a constant polynomial.

3. **The apolar boundary.** In the code's ascending-power indexing, Φ(0)=Σ_j binom(D,j)a_(D−j)(-1)^j a_j. Reflection j↦D−j negates every term when D is odd. The endpoint coefficients, signs, binomial symmetry and a_0 factor are all included. This proves zero independently of the mean identity, so the finite-difference argument is not circular. Switching from the source's signed quasi-binomial parameters to ordinary signed coefficients changes only conventional overall signs and does not change the asserted identity.

4. **Appell derivative/root bridge.** Differentiating F_m gives mF_(m−1). Iterating gives the nonzero descending-factorial scalar times F_(D−ρ) forρ≤D. Scalar multiplication preserves the entire roots multiset. The formal proof uses the actual `Polynomial.roots` multiset overℂ and algebraic closure; it does not replace roots by a set or infer the identity only for distinct roots and then assert continuity.

5. **Root means and endpoints.** The polynomial Φ evaluated at positive integerm equals the average of the original F_D over F_m's m roots. Atm=D it vanishes because every root is a zero of F_D. Atm=0 it vanishes by the separate apolar computation. In the sum reflected byρ=D−m, the excluded indices are exactlyρ=0,D, and both terms are separately proved zero. Every natural subtraction used in the reindexing is guarded by the appropriate interval bound. The final signs and binomial weights are precisely those of Conjecture2. ForD=1 the source sum is empty; no exceptional gap remains.

6. **Arbitrary polynomial normalization.** For every nonzero complex polynomialp the parameters p_(D−i)/(lc(p)·binom(D,i)) give p=lc(p)F_D. The binomial denominator is nonzero for every coefficient used in that reconstruction. Multiplication by the nonzero leading coefficient preserves derivative-root multisets and scales evaluations/means by that coefficient. The final theorem takes only `Odd p.natDegree`; this itself excludesp=0. Monicity and all reconstruction/normalization facts are discharged internally.

No mathematical obstruction or scope mismatch was found.

## Independent fresh formal replay

I copied the six frozen modules into the owned review directory, verified their SHA256 hashes against the supplied frozen manifest, rebuilt fresh oleans against assigned Lean4.34.1/pinned dependency builds with warnings treated as errors, and explicitly checked/printed axioms for **all50 authored declarations**. Result: **PASS**, only {propext, Classical.choice, Quot.sound}. No holes, custom axioms or native_decide occur. The upstream declarations are accepted as instructed; this review does not re-audit mathlib's truth.

Receipt: `build/fresh-audit-919q2rv5/receipt.json`; reproduction: `audit.py`. This independent helper performs no git metadata operation and uses the assigned pinned dependency build. The parent separately owns canonical dependency-pin replay and release packaging.

| Module | SHA256 |
|---|---|
| RootNewton | `c6e1c84477b4d42d2bc35a8e16ed483e8fa39e58e5f8d69a9ed818092a2daa72` |
| MomentPolynomials | `0bf8f0308368099f584a798271c5f00ada44455b7790648b10c0f2b9d5b6ca6b` |
| AppellRoots | `41a60d8638579b91a87aaae97b687fb8d671377a331708f742fb36151b8a23f9` |
| MeanPolynomial | `336e99f9609156ec2546c69f8392b8dea5cfe776766f5aeb5808006d6157b0b9` |
| OddMeanIdentity | `b3b73da1503a0ef1db46af4c83b4959ad5069b2321c384ca64e8ea6762cf04ec` |
| SourceIdentity | `4e76681c19305231ac8c85f28d3a3bfd9afbeee4d4264d2541131b52b16ad72a` |

Main endpoint: `OddRootMeans.source_conjecture_336466 (p : Polynomial ℂ) (hodd : Odd p.natDegree)`. Its conclusion is the exact source mean identity. There is no supplied Newton, moment-continuation, apolarity, finite-difference or generic-root hypothesis in that endpoint.

## Closest prior work: what it does and does not establish

I independently read the original [Toda1936 paper](https://www.jstage.jst.go.jp/article/tmj1911/42/0/42_0_311/_pdf/-char/en), including rendered pp315–316, and the original French [Popoviciu1940 paper](https://ictp.acad.ro/notes-on-higher-order-convex-functions-iii/), visually inspecting §11 on pp85–86. These are close prior work and must remain prominently credited.

Popoviciu defines F_n h(P)=Σ_(i=0..n)(-1)^i binom(n,i)M_h(P^(i)) and credits Toda with its vanishing for test polynomials of degree≤n. The means in this displayed formula remain defined when n<degreeP. That restriction is inherent in the root-average definition, rather than an assertion that an average over a degree-zero derivative has been defined. The source claim here instead uses a same-degree testh=P, ordern=degreeP, and omits the degree-zero-root endpoint. It therefore does **not** follow by directly substituting the candidate parameters into the stated old formula. The new proof supplies the missing continuation and identifies its boundary with self-apolarity. The old presentations use real-rooted polynomials; extending a coefficient-polynomial identity from that setting to complex coefficients is routine and is **not** treated as a separate novelty distinction. The material comparison is the same-degree endpoint.

Toda1936's displayed Waring calculation is close antecedent for polynomial behavior of derivative-root moments. Its TheoremsD/E concern rescaled leading-sign and convexity properties. In the read seven-page paper I did not find the complete same-degree odd self-mean identity or the required zero-parameter apolar boundary. This comparison does not claim its moment machinery is new.

I also independently read Ottaviani's primary exposition, [*Five Lectures on Projective Invariants*, §4.3,pp49–50](https://arxiv.org/pdf/1305.2749). Proposition18 explicitly states odd-degree self-apolarity, and the preceding coefficient formula is the cancellation used here. That ingredient is wholly classical. It does not itself identify averages over successive derivative roots with the artificial zero-parameter value. No new apolarity theorem is claimed.

**Material residual limitation:** Toda, *On Certain Functional Inequalities*, Hiroshima4(1934),27–40, DOI[10.32917/hmj/1558749761](https://doi.org/10.32917/hmj/1558749761), remains unread. I independently obtained its Crossref primary locator; the publisher response was an anti-bot HTML page, not the paper. No bypass was attempted. Later primary accounts establish the neighboring results above but cannot prove that the unread1934 body lacks an additional stronger identity. Its unavailability is a residual prior-art risk, not evidence of either novelty or prior resolution.

Independent live searches included both source titles, identifier, authors with proof/conjecture terms, derivative-root means with binomial/finite-difference/apolarity terminology, and the Toda titles. I found the original source and author-maintained computational OEIS records, classical apolarity material and derivative-root moment results; no explicit published all-odd proof or older theorem already asserting the full same-degree identity was located. Search absence is not a worldwide-priority certificate.

## Recommendation and limits

**ACCEPT under the documented-prior/no-known-prior-resolution standard:** the packet completely proves the exact2017 conjecture for all odd-degree complex polynomials and all derivative-root multiplicities. The older statements actually read do not explicitly subsume this endpoint. Classical ingredients alone are not an exclusion. The most substantive step beyond their stated scope is the normalized moment continuation at the same-degree boundary and its identification with self-apolarity.

Keep Toda1934's unread status and all classical credit visible; do not advertise exhaustive priority. An explicit stronger old theorem containing the full endpoint would require reclassification, but none has been established by this review. This is one outcome, not separate discoveries for each odd degree or each bridge lemma.

## Final manuscript binding

I independently read the full parent-authored `candidates/odd-root-means/main.tex`, SHA256 `c462a84f149c528e7796225a0139df6b1ae85485a3c1f65cd5e9f2fa0a5503fe`. **Manuscript mathematics/source/formal-scope PASS.** It preserves the source multiset mean and exact full theorem, covers Newton moments above the derivative degree, defines the artificial zero endpoint correctly, uses the correct finite-difference sign after reflection, and extends to arbitrary nonzero leading coefficients. It makes no unsupported dimension-classification or distinct-root claim. Classical ingredient credit and the material unreadToda1934 limitation remain explicit. No correction is requested for these paper bytes. This binding concerns TeX mathematics and text; the parent owns PDF rendering and visual layout review. No further Lean replay was required because the mathematical certificate modules did not change.

Final layout-only delta: release TeX SHA256 `76a1e2264974ce62fd5cce7755cc42f11a1ec23e75fb39e5f1471943e4356fab` inserts one `\clearpage` command before the bibliography. I independently verified that removing that command and its newline reconstructs exactly the reviewed `c462a84f149c528e7796225a0139df6b1ae85485a3c1f65cd5e9f2fa0a5503fe` bytes. Mathematical/text content is unchanged and the same PASS covers this final layout hash. Parent owns final visual QA.
