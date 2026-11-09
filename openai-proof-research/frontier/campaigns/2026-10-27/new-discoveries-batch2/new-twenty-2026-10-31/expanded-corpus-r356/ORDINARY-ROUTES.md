# Ordinary routes and separate gates

This is source-led ordinary discovery, not execution. No Lean, enumeration, mathematical search program, solver or CAS was run. All results have zero credit. The three sustained routes are 335872, 336613 and 335387. A short result is not excluded for being short; the explicit exclusions below concern public resolution, source semantics, and incomplete scope.

## 335872: weighted projections of ASMs — public complete resolution

Literal endpoint: every positive integral vector c majorized by (n,...,1) is the row-index-weighted column projection of an n by n ASM. Source 1704.07752 Conjecture 44 agrees except that weights must be matched carefully. O'Brien 2212.11676, versions 1 and 2, Section 2, Lemmas 2.5–2.6 and Theorem 2.7, and Electronic Journal of Combinatorics 31(1) (2024), P1.10, Lemmas 5–6/Theorem 7, explicitly provide this result. Journal proof pages 5–8 were read, including the trapezoid examples; the journal's full construction continues on page 9, which was not fully reviewed here. No independent audit of the entire published proof is claimed.

Exact reduction to that theorem: its weight row is z=(n,...,1). Given c satisfying the literal hypotheses, Theorem 7 supplies B with z B=c. Reverse the rows, A_ij=B_(n+1-i),j. Row reversal preserves each alternating row, and reverses each alternating column; a sequence beginning and ending in +1 still does so upon reversal. Thus A is an ASM. Substitution j=n+1-i gives sum_i i A_ij=sum_t(n+1-t) B_tj=c_j. This is the entire convention bridge, with no new existence lemma. Public resolution predates this campaign.

The source construction was followed beyond its theorem: Gale–Ryser supplies a binary matrix with row sizes 1,...,n and column counts c; its rows specify a row-increasing triangle. The published trapezoid swaps preserve the multiset and strict row order and terminate at a monotone triangle. A single adjacent swap can duplicate a row entry (the printed overlapping inversion example), so naive independent swaps are not an adequate replacement. The monotone triangle corresponds to an ASM through consecutive differences of its binary prefix-row matrices. Telescoping those differences gives the descending weighted projection. This is a public construction, not a new candidate.

Gates: exact ordinary answer is supplied publicly; statement convention bridge complete; novelty FAIL; independent reconstruction/formal endpoint/replay NOT RUN; corrections/citing coverage bounded, no global clearance. No Pi plan is warranted for this excluded public result.

## 336613: X-ray semantics and integrality — literal correction, source problem HOLD

The corpus says entries of d(D) record whether each diagonal has nonzero mass. Nordh 1707.03928 v1, Section 2 instead defines d_k(D)=sum_{i-j=n-k}D_ij, and calls the resulting vector binary only when every sum belongs to {0,1}. Section 4 Conjecture 17 is about these sums, not the indicator of support.

Complete literal refutation under the explicit support interpretation: take n=2 and D=((1/2,1/2),(1/2,1/2)). All entries are nonnegative and each row and column sums to 1. Its support X-ray is (1,1,1). A permutation of two elements either fixes the first element, forcing both diagonal entries to 1, or moves it, forcing both off-diagonal entries to 1. In the first case the support X-ray is (0,1,0), in the second (1,0,1). Neither is (1,1,1). These two alternatives follow from the first row and column constraints; no machine enumeration was used. This completely answers the weakened literal reading, but is a domain/definition correction and receives zero credit. The true sum X-ray of D is (1/2,1,1/2), so D is not an in-scope source counterexample.

Second route: Birkhoff writes D as a positive convex combination of permutation matrices. Zero diagonal sums force all summands to avoid those diagonals. A sum equal to 1 does not force each summand's sum to equal 1, since permutation diagonal sums can exceed 1. Therefore a support matching, including one supplied by Hall's theorem, need not satisfy all prescribed diagonal capacities. A proof would require an integrality theorem for the simultaneous row, column and individual diagonal constraints, not merely a perfect matching in the support.

Current material comparator actually read: Li–Liu–Yao, 2608.01442v2 (August 2026), Theorem 1.7 resolves Nordh Conjecture 15's fractional feasibility statement; Section 5 restates Conjecture 17 as Conjecture 5.1. Its printed order-5 half-integral matrix has sum X-ray (0,0,1,1,1,1,1,0,0), and cannot be rounded inside its existing support. The same section supplies a permutation with that X-ray, so it is not a full counterexample. Its Proposition 5.4's triangular-table obstruction does not have the two required consecutive uniform marginals; transporting it would need a new semantic bridge. Both tempting extrapolations fail. We read the proposition construction and the accompanying limitation, not the entire Section 4 fractional-feasibility proof.

Gates: corpus statement fidelity FAIL; source-scope ordinary proof OPEN IN THIS INVESTIGATION; no claim of worldwide unresolved status; novelty for correction FAIL; full literature/formal/replay gates HOLD. No dormant implementation proposal for a correction.

## 335387: Fuss–Narayana positivity — higher-minor gap remains

Literal endpoint simultaneously asks total nonnegativity of four infinite triangular arrays and strict total positivity of two infinite squares, for every integer m>=1. All minors, with arbitrary increasing row and column selections, are required. It is not just row log-concavity or Hankel positivity of a row-polynomial sequence.

Definitions and proof context were read in Wang–Yang 1702.07822v1: Proposition 2.3's positive row/column scaling, Theorem 2.4's PF-sequence argument, Theorem 2.5's different m-Narayana family, and Theorem 3.7's square argument. The revised author-hosted November 7, 2017 manuscript, pages 8–9, retains the Fuss conjecture as Conjecture 4.1 for m>=2. Journal metadata identifies Discrete Mathematics 341(5), 1264–1269 (2018), DOI 10.1016/j.disc.2018.01.012. The publisher's complete final text was not acquired, so exact final-journal identity/corrections remains a gate.

Complete known m=1 bridge: FNB(n,k)=binom(n,k)^2. For FNA, the identities binom(n+1,n-k)=binom(n+1,k+1) and binom(n+1,k+1)=(n+1)/(k+1) binom(n,k) give FNA(n,k)=binom(n+1,k)binom(n,k)/(k+1). These are exactly the source's ordinary type-B/type-A Narayana arrays. They are symmetric under k -> n-k. Thus its Theorems 2.4 and 3.7 cover all six m=1 assertions, with no new result. Theorem 2.5 uses (m+1)/(n+2) binom(n+2,k+1)binom(n-m,k); that formula is not the literal Fuss family, so its parameter cannot simply be renamed.

Sustained attempt 1, PF scaling: factorial expansion gives
B_m(n,k)=n!(mn)!/[k!(n-k)!^2((m-1)n+k)!].
For m=1 this separates into positive row and column factors times 1/(n-k)!^2. For m>1 the last factorial couples n and k, so the same displayed factorization does not supply a Toeplitz PF kernel. We have not proved that every conceivable alternate scaling is impossible; we have identified the missing lemma in this proposed transfer.

Sustained attempt 2, prove a genuine partial bound rather than infer all minors: for n>=k+1,
 B_m(n,k+1)/B_m(n,k)=(n-k)^2/[(k+1)((m-1)n+k+1)],
 A_m(n,k+1)/A_m(n,k)=(n+1-k)(n-k)/[(k+1)((m-1)n+m+k+1)].
Both ratios increase with n. To verify, put t=n-k>0. Omitting the positive factor 1/(k+1), the first is t^2/(a t+b), where a=m-1>=0 and b=mk+1>0. Its derivative is t(a t+2b)/(a t+b)^2>0. The second is t(t+1)/(a t+d), with d=mk+m+1>0, whose derivative is (a t^2+d(2t+1))/(a t+d)^2>0. Hence adjacent-column 2-minors with increasing rows are positive inside the support. For columns k<l, multiply the adjacent ratios from k to l-1: B(n,l)/B(n,k), respectively A(n,l)/A(n,k), increases with n where both are positive. Thus all 2-minors of these two unreversed triangles are nonnegative; if the smaller row is outside the later column's support, the determinant is a nonnegative product or zero. Order-1 minors are already nonnegative. This is an ordinary proof of TP of order 2, a helper only, not the requested all-order claim. No numerical or symbolic computation was used.

Sustained attempt 3, squares/planar kernels: substituting n+k yields
 B_m(n+k,k)=(n+k)![m(n+k)]!/[k!(n!)^2((m-1)n+mk)!].
For m=1 the positive scaling leaves (n+k)!^2, the source's moment kernel. For m>1 the mixed factorial remains, so the source's Hankel moment argument has not been transferred. A planar path realization would need the exact factorial-ratio kernel with ordered sources/sinks and a disjoint-path interpretation of every selected minor; a path count for individual entries is insufficient.

Material companion/comparator read: Pétréolle–Sokal–Zhu 1807.03271, Theorem 10.1 and neighboring formulas, asserts coefficientwise Hankel positivity for multivariate Fuss–Narayana polynomial sequences. We have not established the required coefficient-array or reindexed-square implication; it is not a license to take arbitrary coefficient minors. A 2026 Zhu JLMS article, DOI 10.1112/jlms.70450, also bears directly on Riordan positivity; only search metadata/abstract was available here, and the inherited Wiley access restriction was respected. Its proof body and an exact family comparison remain material unread gates.

Gates: definitions substantially restored; two useful source transfers explicitly limited; exact full ordinary answer FAIL/OPEN; novelty HOLD, full companion/latest-journal/corrections HOLD; formalization and replay NOT RUN. No CANDIDATE.md and no Pi execution or dispatch. Continuing requires a concrete all-order determinant/network identity or an exact in-scope negative minor found by authorized ordinary reasoning, followed by the full source gates.
