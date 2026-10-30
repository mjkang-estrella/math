# Candidate: An–Đoković Conjecture 3.6 for all n

Status: complete mathematical argument below, pending independent review, novelty/subsumption judgment, and full literal Lean endpoint. **No credit claimed.** Solo lane astra-discrete-r3; 2026-10-28 UTC. The known n≤12 verification and Narayana observation receive no new credit.

## Exact question and source

J. An and D. Ž. Đoković, *Zero patterns and unitary similarity*, arXiv:0807.3580v2, Conjecture 3.6 (printed p. 11). For integers n≥2 and 1≤k<n, let

J_{k,n} = {(i,j):1≤i<j−1≤n−1} ∪ {(n,j):1≤j≤k} ∪ {(i,1):k<i<n}.

Let χ_J=∏_{(i,j)∈J}(x_i−x_j), and Δ_n=∏_{i<j}(x_i−x_j). The source inner product declares Laurent monomials orthonormal (p. 9); it has no factorial weights. The claim is

⟨χ_J,Δ_n⟩ = (−1)^(n−1) C(n,k) C(n−2,k−1).

The source proves k=1 in Example 6.3, and Theorem 2.7 gives universality for k=2, not this numerical evaluation. Its finite check leaves (10,5) uncomputed. A public Ideosphere paper now verifies all n≤12 and explicitly leaves the all-n question. This candidate concerns the full quantified identity only.

## Classical dependency, stated exactly

For homogeneous degree n−1 f, write

D_n(f)=Σ_{σ∈S_n} f(x_{σ(1)},…,x_{σ(n)}) / ∏_{i=1}^{n−1}(x_{σ(i)}−x_{σ(i+1)}).

For a∈N^n with Σa_i=n−1, define S(a)={j∈[n−1]:Σ_{i≤j}a_i<j}. The Postnikov monomial formula is

D_n(x^a)=(−1)^|S(a)| #{σ∈S_n:Des(σ)=S(a)}.

This is Nadeau–Tewari, arXiv:1908.10934, Lemma 3.7, equation (3.6), with a proof in Appendix A; it is also the path case of Petrov, arXiv:1512.07136, Theorem 2. Actual theorem bodies and proofs were read, and PDFs saved. This classical formula is a dependency, not claimed as new.

## Proof

Put A_n=∏_{i=1}^{n−1}(x_i−x_{i+1}) and
P=P_{n,k}=∏_{j=1}^k(x_n−x_j) ∏_{i=k+1}^{n−1}(x_i−x_1).
The three sets defining J are disjoint, so χ_J=(Δ_n/A_n)P. Consequently
Alt(χ_J)=Δ_n D_n(P), where Alt(f)=Σσ sgn(σ)σ(f).
Both sides have degree n(n−1)/2. An alternating polynomial is divisible by Δ_n, so D_n(P) is constant. Comparing the coefficient of x_1^(n−1)x_2^(n−2)⋯x_n^0 gives
⟨χ_J,Δ_n⟩=D_n(P): indeed Δ_n has that coefficient 1 and its other monomials are precisely the signed permutations of this exponent vector. This also checks the absence of any n! factor.

Write P=Σ_a c_a x^a. It is homogeneous of degree n−1. Every internal variable x_i, 2≤i≤n−1, appears in exactly one factor of P, hence a_i≤1 whenever c_a≠0. Set d_j=Σ_{i≤j}a_i−j for 1≤j≤n−1. Then d_{j+1}−d_j=a_{j+1}−1≤0 for 1≤j≤n−2. Thus S(a) is a terminal interval {r(a),…,n−1}, where r(a)=n if it is empty.

A permutation with exactly this descent set increases strictly to position r and then decreases strictly. Its peak is n; choosing the r−1 entries to its left determines the permutation uniquely. Therefore the classical formula simplifies to
D_n(x^a)=w_{r(a)},  w_r=(−1)^(n−r) C(n−1,r−1).

For 1≤j≤n−1 set C_j=Σ_{a:Σ_{i≤j}a_i≥j} c_a. Because d_j is nonincreasing, this is exactly Σ_{a:r(a)>j}c_a. Define also C_0=Σ_a c_a=P(1,…,1)=0, and C_n=0. The total coefficient mass with r(a)=r is then g_r=C_{r−1}−C_r.

To compute C_j, specialize x_1=⋯=x_j=t and x_{j+1}=⋯=x_n=1. The coefficient of t^d is the total c_a with prefix exponent sum d. This specialized P is zero if j<k, because its factor x_n−x_{j+1} becomes zero. It is zero if j>k, because its factor x_{k+1}−x_1 becomes zero. If j=k, every one of the n−1 factors becomes 1−t. Hence
C_j=0 (j≠k),
C_k=Σ_{d=k}^{n−1}(−1)^d C(n−1,d)=(−1)^k C(n−2,k−1).
The last identity follows by substituting Pascal's identity and cancelling the two tails; it holds also k=1 and k=n−1.

Put B=C(n−2,k−1). Only g_k=−C_k=(−1)^(k−1)B and g_{k+1}=C_k=(−1)^kB are nonzero. Linearity now gives
D_n(P)=g_k w_k+g_{k+1} w_{k+1}
=(−1)^(n−1)B [C(n−1,k−1)+C(n−1,k)]
=(−1)^(n−1) C(n,k) C(n−2,k−1).
This proves the exact source conjecture, conditional only on the stated classical theorem (whose independent published proofs are supplied). Every boundary case n=2, k=1 and k=n−1 is covered. ∎

## Strongest objections and outstanding gates

1. **Subsumption / routine-corollary risk:** the monomial evaluation is classical; after the internal-multiaffinity observation, the specialization collapse is short. It may fall under the campaign's prohibition on routine classical corollaries, even though it answers an explicit source conjecture for all n. Root must make that judgment. No assertion of demonstrated new-to-literature status is made.
2. A prior all-n solution may be unindexed. Bounded public search and actual relevant theorem-body comparisons are recorded in provenance.md; absence of a search result is not proof of novelty.
3. The full literal χ_J inner-product theorem is NOT yet formalized. Initial Lean will certify the crucial specialization step, not replace the missing DS/alternation/coefficient bridges.
4. No independent reviewer, paper extraction, or final accepted replay has happened. This lane cannot count itself.
5. The public Narayana observation, finite n≤12 values, k=1 source proof, and k=2 universality are known and excluded from the proposed contribution.

## Self-contained proof of the restricted monomial evaluation

The proof above may use the published Postnikov theorem directly. For a fully explicit route that avoids importing that theorem wholesale, here is a proof of exactly the restricted case needed. This is a specialization of the classical divided-symmetrization method, not another claimed discovery.

First, for m variables, D_m(f) is a symmetric polynomial of degree deg(f)−(m−1), or zero. To see this, multiply by the Vandermonde: the result is the alternation of f times the product of non-path Vandermonde factors. An alternating polynomial is divisible by every x_i−x_j (set x_i=x_j, then interchange i,j); these pairwise nonassociate irreducible factors divide their product. This proves the assertion over Q. In particular D_m(f)=0 if deg(f)<m−1, and D_1(1)=1.

Second, deleting path edge j gives the following elementary factorization. Suppose g uses only x_1,…,x_j and h uses only x_{j+1},…,x_n, and deg(g)+deg(h)=n−2. Group permutations by the j-element set of variables assigned to the first block. Cancellation of x_j−x_{j+1} in the denominator gives a sum of products of the two block divided symmetrizations. If deg(g)≠j−1, one block has degree below its path-edge count, so
D_n((x_j−x_{j+1})gh)=0.
If deg(g)=j−1, both block values are constant and
D_n((x_j−x_{j+1})gh)=C(n,j)D_j(g)D_{n−j}(h).
This is also the content of Nadeau–Tewari Lemma 3.4 and Corollary 3.5; the argument here proves the instance used.

Let a have total degree n−1 and internal exponents at most 1, with first negative prefix defect r as above. Write A_j=Σ_{i≤j}a_i. For r>1, A_{r−1}=r−1 and a_r=0: if r<n, this follows from A_{r−1}≥r−1 and A_r<r; if r=n it follows from A_{n−1}≥n−1 and total degree n−1. For r=1, a_1=0 directly. Before r the prefix sums satisfy A_j≥j; after r they satisfy A_j≤j−1.

Starting at i=1 and moving right up to r−1, make every a_i equal to 1 by transferring any excess one unit at a time from position i to i+1. With earlier positions already equal to 1, A_i≥i ensures a_i≥1. During a transfer the prefix sum before transfer is at least i+1. The difference between the old and new monomials is (x_i−x_{i+1})x^b, where the degree of the left block of x^b is A_i−1≥i. By the zero case of the factorization just proved, the transfer does not change D_n. The total left mass is exactly r−1, so there is no excess to transfer into position r.

Next, starting at i=n and moving left down to r+1, make a_i equal to 1 by transferring any excess from i to i−1. Earlier in this reverse procedure, all positions to the right of i have already become 1. The suffix mass is at least its length since A_{i−1}≤i−2. Thus a_i≥1. During a transfer the prefix sum at j=i−1 is at most j−2. The difference is the negative of (x_j−x_{j+1})x^b, whose left block degree is that prefix sum, strictly below j−1. Again D_n does not change. The right mass is exactly n−r, so nothing is transferred into r. All procedures are finite and keep nonnegative integer exponents.

We have reduced to M_r=∏_{i≠r}x_i. It remains to evaluate these n squarefree monomials. Induct on n, the case n=1 being D_1(1)=1. For 1≤r<n,
M_r−M_{r+1}=−(x_r−x_{r+1})∏_{i≠r,r+1}x_i.
The block factorization and the induction hypothesis give
D_n(M_r)−D_n(M_{r+1})=(−1)^(n−r)C(n,r),
because the left block omits its last variable (value 1), and the right block omits its first variable (value (−1)^(n−r−1)). Also
Σ_r D_n(M_r)=D_n(e_{n−1})=e_{n−1}D_n(1)=0
for n≥2. The proposed w_r=(−1)^(n−r)C(n−1,r−1) satisfy the same consecutive differences by Pascal, and their sum is zero by the binomial theorem. The difference between the two sequences is constant; its n-fold sum is zero over Q, hence that constant is zero. Thus D_n(x^a)=D_n(M_r)=w_r, completing the restricted evaluation and the all-n proof without an unproved mathematical bridge.
