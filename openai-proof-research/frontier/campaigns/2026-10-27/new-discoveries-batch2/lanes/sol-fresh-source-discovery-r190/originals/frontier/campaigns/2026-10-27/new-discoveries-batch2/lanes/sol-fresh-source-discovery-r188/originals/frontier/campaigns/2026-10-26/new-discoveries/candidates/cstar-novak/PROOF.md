# Candidate counterexample to C*-algebraic Novak positivity

Status: **full source refutation; mathematical, strict Lean, independent review and manuscript gates PASS**. One outcome only. Final acceptance is recorded in the campaign ledger after extracted-packet replay. See reviews/ for the unchanged independent review and parent reconciliation.

## Exact source

Krishnanagara Mahesh Krishna, *C*-algebraic Schur product theorem, Pólya–Szegő–Rudin question and Novak's conjecture*, J. Korean Math. Soc.59(4)(2022),789–804, DOI10.4134/JKMS.j210627. Actual publisher PDF retrieved and text read: Definition6 gives cos(A)=(exp(iA)+exp(−iA))/2. Published Conjecture4.2 (p799; preprint Conjecture4.3) asserts the literal matrix of products (1+cos(Xjl−Xkl))/2 minus1/n is positive for any unital C*-algebra and all self-adjoint tuples, n,d≥2. Published Theorem4.3 proves only the commutative case. No extra commutation assumption occurs in the conjecture.

Primary publisher PDF: sources/published2022.pdf, SHA256 5f53313dd1dc57481990ff64939e376c4cb0cf1bb7c707047c5c5d3ff4b8a5d6.
Live MathDB351633 snapshot: SHA256 655dc698bc876ea43dc2784ad17d7369129b6aa4edf5807cfae33336a320ae0d; status open, progress null, no posted solutions. Independent bounded prior-art review found no earlier refutation in its inspected corpus; see reviews/independent-review.md and reviews/parent-addendum.md for the actual sources and limits. No absolute priority claim.

## Explicit witness

Use A=M2(C), with real symmetric Pauli matrices Z=diag(1,−1) and X=[[0,1],[1,0]]. Put

U=2πZ, V=(π/4)(−7Z+sqrt(15)X).

Let n4,d2 and first coordinates (0,U,U+V,V), with every second coordinate0. All inputs are self-adjoint. Their first-coordinate differences satisfy

U²=V²=4π²I, (U+V)²=π²I, (U−V)²=15π²I.

For any self-adjoint M with M²=r²I, r>0, its exponential-defined cosine is cos(r)I. This follows by diagonalization, or directly by intertwining with rI±M and adding the two resulting exponential identities. Therefore the four side differences have cosine I, one diagonal has cosine −I, and the other diagonal has cosine cI, c=cos(πsqrt15)≤1. The zero difference has cosine I. The second-coordinate factor is always I.

Thus the uncentered first kernel is the scalar matrix

[[1,1,0,1], [1,1,1,t], [0,1,1,1], [1,t,1,1]] tensor I2,

where t=(1+c)/2≤1. Subtracting J4/4 tensor I2 gives the literal source matrix. On the vector (1,−1,1,−1) tensor e1, the J4 term vanishes and the quadratic form is

−4+2t = c−3 ≤−2 <0.

The source matrix is Hermitian, all kernel entries are central scalar multiples of I, and the failure also occurs before subtracting J4/4. The counterexample therefore does not depend on non-Hermitian products, product-order conventions, or the Schur/Jordan-product ambiguity. The already proved commutative theorem and original scalar Novak theorem are untouched.

Independent floating eigendecomposition of the actual 2x2 input differences yields c≈0.921436514468169 and quadratic form≈−2.078563485531832, agreeing with the exact formula. Numerical data are exploratory checks only; the symbolic proof above supplies the proposed sign.

## Complete formal route

`formal/CosineBridge.lean` proves the literal matrix-exponential cosine bridge via SemiconjBy.exp_right on rI±M. NovakWitness proves every cosine evaluation. NovakConclusion proves the literal source-block/flattened-matrix endpoint, self-adjoint inputs, a Hermitian source matrix, exact quadratic form and non-PSD. All36declarations replay strictly with only the standard3axioms. No assumed cosine evaluation remains. Frozen candidate in candidates/cstar-novak.
