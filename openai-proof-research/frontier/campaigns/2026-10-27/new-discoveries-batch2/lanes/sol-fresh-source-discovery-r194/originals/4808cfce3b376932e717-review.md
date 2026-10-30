# Independent preliminary review: An–Đoković Conjecture 3.6

Review date: 2026-10-28 UTC / 2026-10-27 America/Los_Angeles. Candidate: `root-an-djokovic-r1`, user-specified revision `71b7f0b374`, bound by the 48 entries in `preliminary-review-hashes.json`. Reviewer worked solo, with no children, git operations, shared edits, accounts, uploads, or external messages. All outputs are in the assigned review lane. This is a recommendation to root, not an acceptance or ledger decision.

**Recommendation: preserve the valid all-n written proof, but exclude this candidate from the thirty substantive new outcomes as a routine classical corollary; do not invest in the full Lean endpoint for campaign credit.** The reason is the exact classical-to-source reduction in [corollary-bridge.md](corollary-bridge.md), not an assertion that an earlier public all-n proof was found. If root judges that reduction substantive, the source-publication and full formal gates below still remain open.

| Gate | Finding |
|---|---|
| Frozen artifact integrity | PASS: all 48 files match before and after review. No candidate bytes changed. |
| Exact arXiv source fidelity | PASS: literal pattern, sign, pairing, parameter range match 0807.3580v2. |
| Final journal body comparison | UNRESOLVED: metadata obtained; full journal body not obtained. |
| Ordinary all-n mathematics | PASS, including the self-contained restricted DS appendix. |
| Existing Lean helpers | PASS: 7 definitions and 9 theorems replay; standard three axioms only. |
| Full literal formal endpoint | NOT PRESENT. No full FORMAL PASS. |
| Bounded search for prior public all-n proof | None located in the inspected bodies/registries; not a priority certificate. |
| Substantive eligibility under this campaign | FAIL recommendation: explicit routine classical-corollary bridge below. |

## 1. Exact source and scope

I read the candidate's complete `discovery.md`, complete `provenance.md`, self-review, exact checker and initial formal source. I read the ancestor and batch AGENTS, current ledger, prior-campaign context and the prior `pi-discrete-discovery-r3` normalization warning. The current campaign has no accepted additional outcome, and neither the prior thirty families nor public finite computations receive any credit here. The upstream catalogue was screened for this subject; no upstream theorem is used.

The primary source is An–Đoković, [*Zero patterns and unitary similarity*, arXiv:0807.3580v2](https://arxiv.org/pdf/0807.3580v2). The newly retrieved PDF is byte-identical to the frozen source. I inspected the actual inner-product definition on printed p.9, equation (3.3) and Conjecture 3.6 on p.11, Theorem 2.7, and Theorem 6.2 / Example 6.3 on pp.22–23. Printed p.11 was also rendered and visually read.

For n≥2 and 1≤k<n the three sets are

    {(i,j):1≤i<j−1≤n−1},  {(n,j):1≤j≤k},  {(i,1):k<i<n}.

Their union is disjoint. The first is exactly the translated upper triangular pattern; it omits adjacent edges. Its cardinality is (n−1)(n−2)/2, and the other cardinalities are k and n−1−k, giving n(n−1)/2. Their orientations are exactly those used by the candidate. The source pairs Laurent monomials orthonormally, with no factorial weights. Its conjecture is exactly

    ⟨χ_J,Δ_n⟩ = (−1)^(n−1) binom(n,k) binom(n−2,k−1).

Example 6.3 proves k=1. Theorem 2.7 proves k=2 universality, not the numerical formula. Universality alone does not recover this integer. The old differential-operator checker omitted the factor ∏_(r=0)^(n−1)r! relating differentiation to this pairing; it was not reused. The present proof does not make that error.

The live arXiv record still lists v2, dated 17 December 2009, and the journal reference J. Algebra 324 (2010), 51–80. The journal DOI is [10.1016/j.jalgebra.2009.12.014](https://doi.org/10.1016/j.jalgebra.2009.12.014). ScienceDirect returned 403. Crossref and OpenAlex metadata were accessible. The publisher's advertised XML API returned HTTP 200 but only 1,916 bytes of bibliographic coredata, **not a full-text article**. A public PDF-format API request returned 429; I stopped and did not retry or bypass. The journal body therefore remains unread. Open-archive metadata is not source-body clearance.

## 2. Independent mathematical audit

Put A_n=∏_(i<n)(x_i−x_(i+1)) and P=∏_(j≤k)(x_n−x_j)∏_(k<i<n)(x_i−x_1). Disjointness gives χ_J=(Δ_n/A_n)P. With unnormalized alternation, Alt(χ_J)=Δ_n D_n(P). The staircase coefficient of Δ_n is 1. Since all staircase exponents are distinct, the coefficient of that staircase in Alt(χ_J) is the signed sum of exactly the coefficients paired with Δ_n, each once. Hence the pairing is D_n(P), without an n! factor. For example n=2 gives χ_J=x_2−x_1 and pairing −2 directly.

P has total degree n−1. Every internal variable occurs in exactly one factor, so every supported exponent a_i for 2≤i≤n−1 is at most one. Thus the prefix defects d_j=∑_(i≤j)a_i−j are nonincreasing for 1≤j≤n−1. Their negative set really is a terminal interval. Neither the last increment a_n−1 nor an unsupported global monotonicity claim is used.

For first negative index r (r=n when none), the classical monomial formula gives w_r=(−1)^(n−r)binom(n−1,r−1): a permutation with exactly descents r,...,n−1 peaks at n in position r, and its left set determines it. The coefficient masses C_j and g_r are signed sums, not cardinalities. The identities C_j=∑_(r>j)g_r and g_r=C_(r−1)−C_r are valid, with C_0=P(1)=0 and C_n=0.

The two vanishing factors are correctly indexed: for j<k, x_n−x_(j+1) exists and becomes 0; for j>k, x_(k+1)−x_1 exists and becomes 0. For j=k all n−1 factors become 1−t, with the same sign. Hence C_k=(−1)^k binom(n−2,k−1), all other C_j vanish, and the two surviving masses give the stated sign and Pascal sum. Both k=1 and k=n−1 are included, and yield (−1)^(n−1)n. There is no exceptional n=2 gap.

The restricted DS appendix is also sound:

* Multiplication by Δ converts D_m into an alternating polynomial divided by Δ. Over Q the distinct linear factors are pairwise nonassociate primes, so alternating divisibility proves polynomiality and the low-degree zero statement.
* Deleting edge j and grouping permutations by the j-element variable set leaves a product of block DS expressions. If the left degree differs from j−1, one block has degree below its edge count and vanishes. If degrees match, both block values are constants; there are binom(n,j) subsets. This gives precisely the factorization used, including one-variable blocks.
* For r>1 the boundary has A_(r−1)=r−1 and a_r=0; for r=1, a_1=0. In the forward transfer, the left degree of x^b is A_i−1≥i, so the right block is below degree and the difference vanishes. The left total r−1 prevents transfer into r.
* In the reverse transfer, if a_i>1 after later positions were set to one, A_(i−1)=i−1−a_i≤i−3. With j=i−1 the left degree is ≤j−2, exactly the zero case. The right total n−r prevents transfer into r. All exponents remain nonnegative and the procedure is finite.
* The squarefree canonical recurrence has D_n(M_r)−D_n(M_(r+1))=(−1)^(n−r)binom(n,r). The left block omits its last variable, the right block its first. The symmetric sum e_(n−1) has DS zero. The proposed weights satisfy the recurrence and zero sum; their difference from the actual sequence is constant and n times that constant is zero in Q. The base D_1(1)=1 is present.

There is no mathematical repair required in the frozen proof. The restricted lemma and recurrence are classical content: compare Nadeau–Tewari Corollary 3.5, Example 3.6 and Appendix A. Reproving them self-containedly is valuable exposition but not a separate discovery.

## 3. Subsumption and substantive judgment

The exact bridge, with proof and every specialization, is saved separately. In compact form: for any homogeneous degree n−1 polynomial f multilinear in x_2,...,x_(n−1), put

    T_j(f)=∑_(d=j)^(n−1)[t^d] f(t,...,t,1,...,1).

Postnikov's printed monomial theorem gives

    D_n(f)=(−1)^(n−1)f(1,...,1)
       +∑_(j=1)^(n−1)(−1)^(n−j−1)binom(n,j)T_j(f).                 (B)

To verify (B), take a monomial with first negative prefix r. T_j is 1 for j<r and 0 otherwise. The sum telescopes from w_1 to w_r because w_(j+1)−w_j=(−1)^(n−j−1)binom(n,j). Linearity handles arbitrary signed coefficients. Applying (B) to P leaves only j=k, where T_k is the elementary alternating binomial tail. The alternation identity above transfers this result to the exact source pairing. This is an explicit all-parameter corollary bridge, not an analogy with a known result or a finite computation.

**Strongest case for eligibility.** The all-n endpoint is a real statement beyond the public finite checks. Locating the DS structure and combining internal multiaffinity with two-level evaluation removes a factorial signed enumeration; neither the original source nor the public finite paper contains that proof. A new application of a classical theorem can absolutely be substantive, and a concise proof may reflect a strong insight. This could justify a useful short note, with cautious priority language.

**Strongest case against, and my judgment.** Here the old theorem already gives the complete linear functional, the supported monomials fall into its elementary terminal-descent special case, and (B) packages that case using only linearity and a telescoping difference. The entire source-specific calculation then consists of checking which product factor is zero, followed by one standard binomial tail. There is no additional unresolved combinatorial evaluation after invoking the classical theorem. I classify that exact remaining calculation as routine under this campaign's exclusion of routine corollaries. The appendix adds no new ingredient beyond the classical transfer proof. The decision is about this specific bridge, not the fact that classical tools were used or that the final proof is short.

I do **not** claim that Postnikov prints the An–Đoković conjecture, that (B) itself was located verbatim, that the source's Theorem 6.2 solves all k, or that a previous public all-n proof was discovered. The distinction matters: the recommendation is substantive ineligibility despite valid mathematics and no located prior exact endpoint. Root may disagree with this evaluative boundary, but should do so against the displayed bridge rather than an open label.

The source's Theorem 6.2 alone is not a demonstrated exclusion bridge. Its values are signed products of distinct integers from {2,...,n}; at n=8,k=4 the target magnitude is 1400, which does not divide 8!. Thus simple relabelling into that source family cannot cover all parameters. Likewise, an independent-parameter Y in an Amdeberhan identity cannot silently be replaced by a moving permuted endpoint inside the summation.

## 4. Actual classical statements and bounded public screen

* **Postnikov, IMRN 2009:** the actual typeset PDF, including pp.1033–1037, was obtained from a university-hosted copy; Proposition 3.5 on p.1035 and its definition/proof were read, and its theorem page rendered. The initially fetched MIT `permutohedron.pdf` was the 2004 extended abstract, not the full 2009 body; it was not mistaken for the latter. Proposition 3.5 is the classical monomial evaluation used in (B).
* **Nadeau–Tewari 1908.10934v2:** actual pp.4–8, the principal quasisymmetric statements and decomposition theorem, and Appendix A were compared. Lemma 3.7 is the exact input. Theorem 1.1 concerns quasisymmetric functions, not this numerator directly; Theorem 1.3 requires an actual quotient decomposition and does not remove the need to calculate it. Their Example 3.6 is the appendix's squarefree recurrence.
* **Petrov 1512.07136v2:** the body and proof of Theorem 2 and the later path/sandpile statements were read. On a path the inversive edges are exactly the negative-prefix indices: the left component has total weight A_j−j. This is the same monomial input with matching orientation and no factorial normalization. Its more general tree theorem does not supply a separately printed double-star product value.
* **Amdeberhan 1406.0447v1:** formula bodies were screened throughout, with closer comparison of Lemmas 4–7, 13, 18, 20, 22–23 and the final problems/exercises. Lemma 22 is a two-endpoint rational partial-fraction identity; Lemma 23 evaluates D_(m+1)((x_1−t x_(m+1))^m)=∑_q binom(m,q)^2t^q. That is not the candidate numerator. I did not establish a direct independent Lemma-23-to-P substitution. The exclusion rests on (B), not a false identification with this similar-looking binomial formula.
* **Nearby zero-pattern bodies:** An–Đoković 0802.1915v3 Theorem 4.2 / Proposition 4.3 supply the characteristic-class-to-universality machinery, and Holbrook–Schoch with Košir–Sethuraman Appendix Theorem A.4 gives the known Hessenberg/two-column simultaneous-similarity result. The actual 2007 Đoković *Operators and Matrices* body, Theorem 2.4 and Proposition 3.1, gives a regularity criterion for feasible upper patterns. These are not the numeric all-k identity.
* **Current citations:** OpenAlex's source record returned two citing works. Both PDFs were obtained and their relevant introduction/theorem bodies screened: Müller–Tomilov 2206.14266, Theorems 1.2–1.5, concerns infinite-dimensional matrix patterns; Bhaumik–Mandal 2204.01566, Theorems 2.1/2.4/2.9 and related discussion, concerns universal subspaces and Euler obstructions. Neither inspected body supplies this pairing evaluation. This is not a claim to have verified every argument in either paper or exhaustively enumerated all worldwide citations.
* **Ideosphere:** the complete 13-page public PDF and page were successfully downloaded here by ordinary GET, resolving the candidate's archival-access limitation for this source. Theorems 4.1/4.3/4.5 cover the finite range through n=12; Proposition 5.1 records the Narayana relation; Remarks 5.2–5.3, §9 and §10 explicitly distinguish those results from an all-n proof. That content is public and excluded. Its search assertions are not adopted as this review's independent search coverage, and its native-decide certificates were not replayed. Universality implications are not treated as equivalences merely because of loose abstract wording.
* **MathDB:** the live `https://mathdb.com/api/posts/381028` returned HTTP 200, `status: open`, and empty solution/reply arrays. The initially tried `/problem/381028` page returned 404. The live record is archived, but contributes no novelty inference.

Exact URLs, hashes, version/reading scope and access failures are in `provenance.json`, the access logs, and `search/`. Search terms included exact title/conjecture combinations, name variants, zero-pattern-inner, double-star/product/multiaffine/two-endpoint DS, and Narayana. Several searches were noisy or supplied no relevant new result. I found no earlier all-n proof in this bounded screen. The final journal source, paywalled mathematical indexes, unindexed work, and unpublished work remain outside the verified coverage. No absolute priority assertion is justified.

## 5. Independent computations and formal limits

`independent_check.py` is reviewer-written and imports no candidate checker. It enumerates choices on the literal ordered edges for all 15 pairs 2≤n≤6; separately it uses exact Fraction-valued Hamiltonian-path subset dynamic programming at nonuniform signed integer nodes for all 36 pairs 2≤n≤9. It does not use the descent formula in that path sum. Both agree with the claimed pairing/DS. It audits every admissible internal-0/1 exponent vector for 2≤n≤10 (2,815 vectors), including the precise forward/reverse transfer inequalities; the 111 vectors through n=6 also pass independent numeric monomial DS. Fifty-five edge-splitting tests pass. Wrong sign and n! normalization controls are detected.

`bridge_check.py` tests (B) against the independent rational monomial DS on those 111 vectors. A deliberate violation a=(0,2,0) returns actual D_3=−2 versus invalid bridge value 4, confirming that the internal-degree hypothesis cannot be omitted. These are finite error-detection tests, not the proof and not a claim to new finite verification.

The absolute pinned Lean 4.34.1 binary replayed a byte-identical helper copy and an audit printing all 16 declaration types/axiom sets, using the supplied cached mathlib libraries. Every axiom reported is among `propext`, `Classical.choice`, `Quot.sound`; the compile exits 0. `replay_review.py`, `Audit.lean`, `lean-review.log` and `lean-review.json` retain the exact reproduction route. The cached mathlib revision is the supplied pin; no git operation independently checked its checkout.

The source pairing is defined, but no theorem computes it. Missing formal work includes pattern factorization, homogeneity/internal degrees, alternation/coefficient normalization, DS or its restricted transfer theorem, coefficient regrouping/specialization, and the final sourceInner equality. Neither helper success nor complete written mathematics closes that gap. I recommend stopping campaign-driven investment on substantive grounds, preserving all artifacts unmodified. No paper, packet, count, acceptance or shared decision was created by this review.
