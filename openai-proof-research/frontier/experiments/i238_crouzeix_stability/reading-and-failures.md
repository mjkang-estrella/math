# I238 — reading, exclusions, and failures

## Scope and operating record

Only I238's five assigned files were written. Work was restricted to openai-proof-research. No agents were spawned; no live sibling reports or shared ledgers were read; no staging, commits, publication, research code, tests, numerical experiments, parameter scans, snapshots, or seals were made. Short Python invocations performed retrieval, text extraction, metadata lookup, and hashing only. Mathematical checks were analytic.

Read AGENTS.md and sources/upstream.json in full; catalogue family 325 at CONTENTS.md lines 7929–7947, with a small surrounding range for context. The source revision is fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. All pinned theorems and lower operations were accepted as stipulated; provenance matching was not a source truth audit.

The only old discovery content read was the opening 65 lines of I39 and I130, plus a targeted case-insensitive Crouzeix/numerical-range/spectral-set search in those two files, which returned no matches. I39's opening is about spin-chain gaps and SK dynamics. I130's opening concerns harmonic growth and the earlier kernel audit. No historical replay or inherited ledger counts are used. The user-provided count remains nine.

## Pinned primary reading

Both family-325 companions were retrieved at pinned raw URLs and their Git blobs matched the preprints tree. Exact URLs, SHA-256 values, Git blobs, and bytes are in input-authentication.json. Their full TeX is retained inside literature.md; storing full TeX is not a claim that every collar or bibliography line was mathematically inspected.

1. **A direct proof of the complete Crouzeix inequality.** Read introduction and Theorem `thm:main`; all of Section 2, including `lem:faber` and `prop:coefficients`; all of Section 3, including `lem:resolvent`, `thm:domain`, both multiplication orders, the reciprocal coefficient weights, Parseval identities, and positive-block trace comparison; Section 4's `lem:approx` and final limiting/sharpness proof. The appendix's standalone conformal-collar construction is not a new dependency; its theorem is stipulated. The already-proved statements cover arbitrary finite base dimension, coefficient size, and degree, including point/segment numerical ranges.
2. **The complete Crouzeix theorem: optimal similarity and a common positive boundary representation.** Read Section 1's `thm:structural` and `thm:representation`; all of Sections 2–5, including metric attainment, `prop:density`, `prop:extremal`, `input:analytic`, `prop:projection`, the two density systems, and `lem:comparison`; read `cor:hilbert` and its full finite-compression/holomorphic-approximation proof. The repeated exterior computations were compared at the operation level. The companion supplies the optimal metric and one positive density, but does not assert a quantitative disk-rigidity theorem.

The direct proof's only shortfall terms available without new work are residual coefficient and block inequalities. Their smallness is not, by itself, an inverse estimate for numerical-range geometry. In particular, omitting constant terms or reversing one multiplication order would not produce a valid complete stability theorem.

## External primary reading

- **Åhag–Czyż–Virtanen, arXiv:2608.27346v3 (9 September 2026).** Extracted and fully read Sections 9 and 11, including all proofs. Section 9 gives the scalar square-function equality theory, the explicit 8√ε approximation to a reducing nilpotent block (Corollary 9.9), and optimized scalar/tuple estimates. Section 11 gives scalar polynomial equality classification, complete equality through base dimension three, the inverse-algebra criterion (Lemma 11.6), and the exact algebra-generation geometry theorem (Theorem 11.7). The paper is external literature, not an extra stipulated pinned manuscript. Its stronger scalar stability theorem is cited explicitly in Theorem Q.
- **Li, arXiv:2002.01027v1, Section 2.1.** Fully read the extracted two-by-two portion. It already supplies the elliptic conformal extremizer and its uniqueness. A simple two-by-two eccentricity calculation would be an extension of an explicit old formula, not substantial fresh work. No quantitative claim here uses the initial series formula's parameter convention.
- **Badea–Crouzeix–Delyon, arXiv:math/0501184, Section 5.2.** Retrieved the primary PDF, extracted and fully read Theorem 5.2, its proof, Corollary 5.3 and its proof, and Remark 5.1. This already provides the complete two-dimensional elliptic similarity, including repeated eigenvalues, and the common scalar/complete constant. It confirms that an ellipse-only complete estimate is not a fresh operator-class bridge.
- **Jin, Rigidity at the Extremal Crouzeix Constant, Preprints.org 202609.0079v2.** Read the main theorem/proof and all of Section 9 through its explicit statement that the stability modulus is nonconstructive. The retained web-rendered proof continuation includes Proposition 7's boundary-spectrum reduction and compactness argument and Theorems 2–3. The theorem is scalar; it gives no explicit exponent or uniform-in-base-dimension modulus. I do not attribute complete disk rigidity to it.

Search results also located work on numerical-radius partial smoothness, half-radial matrices, and weighted shifts. Those snippets were used only to avoid obvious claims of novelty; no theorem from them is used. They were not represented as fully read papers.

## Failures and corrected directions

1. **Whole-operator Jordan rigidity.** False without qualifications: an extremal block can be summed with arbitrary blocks inside the same disk. Multiple extremal blocks also remain extremal. This defeats a claim about closeness of the entire A to one 2×2 matrix.
2. **A two-by-two complete improvement as a new finding.** Rejected on prior-art grounds, after reading BCD and Li. The complete elliptic similarity is already explicit. No asymptotic parameter scan was performed.
3. **Scalar output rigidity at arbitrary coefficient size.** False, even for degree one and base/coefficient size two. P(z)=[[0,z],[1,0]] at A=[[0,2],[0,0]] is exactly extremal; P[A] is the irreducible weighted chain with weights (1,2,1). Its maximal singular vector has nonzero second iterate. The square-function quadratic form equals 9/4, rather than at most 2. The full computation is in analytic-attempt.md.
4. **“Complete” diagonalizable strictness by importing the scalar proof.** Not claimed. The inspected external paper gives complete strictness/conditioning consequences through base dimension three, but its scalar square-function route does not justify arbitrary matrix-valued witnesses. The counterexample in item 3 shows why a naive amplification of the intermediate theorem fails.
5. **Unconditioned transfer through A=q(p(A)).** Existence of q alone is not a quantitative hypothesis. The Crabb C_2 family p_δ(z)=(z²+δz)/(1+δ) has inverses whose normalized coefficient bound diverges. Theorem Q pays this conditioning explicitly; no eigenvector conditioning is silently assumed.
6. **Generic compactness as an explicit exponent.** Rejected. It does not yield a numerical power law. An effective algebraic inequality would still require exact complete rigidity at the relevant zero set, which has not been proved here in dimension four.

## Retrieval issues

The first html-extraction attempt used BeautifulSoup, which is not installed. It was replaced by Python's standard HTMLParser; no environment or package was modified. Direct urllib retrieval of the versioned Preprints.org page and of the Rennes BCD PDF returned HTTP 403. Jin was read through the web tool; BCD was successfully fetched from arXiv. The unavailable arXiv HTML request for Li v2 was replaced by the available v1. No primary-source inference relies on an inaccessible page's search snippet. These are retrieval limitations, not mathematical objections to source truth.

## Assessment

One pivot was made: from unrestricted/elliptic and scalar-output rigidity to bounded inverse reconstruction for scalar quadratic witnesses. The latter yields a complete explicit proof but is a restricted quantitative continuation of known scalar operations. It does not resolve Q4(r), the retained complete-geometry problem, and it is not nominated as the tenth substantial finding. The new obstruction and the restricted theorem should be retained as useful mathematics, without changing the count.
