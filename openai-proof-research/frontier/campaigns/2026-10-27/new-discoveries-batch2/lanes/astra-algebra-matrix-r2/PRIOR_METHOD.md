# Decisive prior-method objection: rank obstruction transfers

No discovery credit is requested. This is a diagnostic adaptation of an older
public method, not asserted to be new mathematics.

## Prior source

The answer by user14972, posted July 28, 2016, to Nathan BeDell's question
[Does every finite dimensional real nil algebra admit a multiplicative basis?](https://math.stackexchange.com/questions/1858832/does-every-finite-dimensional-real-nil-algebra-admit-a-multiplicative-basis)
uses the truncated symmetric algebra on five generators, with one rank-five
quadratic relation. Its rank obstruction prevents any two pair products from
becoming proportional. There are then too many required output basis directions.
The answer concerns commutative associative algebras, not Lie algebras. The
following exterior-algebra transfer is this lane's deduction; it is not a claim
that the 2016 answer literally states the Lie result.

## Exact rational example and proof of the transfer

Let K be any field of characteristic zero, let V=K^6 with basis e_1,...,e_6,
and let W=(exterior square V)/K omega, where

    omega = e_1 wedge e_2 + e_3 wedge e_4 + e_5 wedge e_6.

Set L=V direct-sum W, with bracket [v+w,v'+w'] the class of v wedge v'.
It is bilinear and alternating; all brackets are central, so Jacobi holds.
Its derived algebra is W, of dimension 14, and L has dimension 20. It is
nonabelian, so has nilpotency class exactly two.

Suppose L has a multiplicative basis B. Since the derived algebra is spanned
by brackets of basis vectors, it is spanned by the subset of B that occurs as
nonzero bracket outputs. This subset has 14 elements and is a basis of W.
The other six basis vectors project to a basis u_1,...,u_6 of L/W=V.
The 15 bivectors u_i wedge u_j (i<j) form a basis of the exterior square of V.

Associate to any bivector its skew-symmetric coefficient matrix in a fixed
basis of V. A decomposable bivector u wedge v has matrix uv^T-vu^T, of rank
at most two; a linear combination of at most two such bivectors has rank
at most four. The matrix of omega is the direct sum of three invertible
2-by-2 alternating blocks, of rank six. Nonzero scalar multiples of omega
also have rank six.

None of the 15 images of u_i wedge u_j in W is zero: otherwise a nonzero
decomposable bivector would be a multiple of omega, contradicting rank.
No two images are proportional: if two were proportional, a nonzero linear
combination of two distinct basis bivectors would be a nonzero multiple of
omega, contradicting rank at most four versus six. The combination is
nonzero because those two bivectors are independent.

Multiplicativity would therefore require 15 distinct output basis directions
inside W, which has only 14 basis directions. Contradiction.

An explicit multiplication table uses the 14 central vectors z_ij for all
1<=i<j<=6 except (1,2). All their brackets vanish. Set
[e_1,e_2]=-z_34-z_56, and [e_i,e_j]=z_ij for every other i<j, and impose
skew-symmetry. These are rational structure constants. The preceding proof
applies over R and C and refutes the literal class-two clause of the source.

## Consequence for the 12-dimensional generic candidate

The dimension-count proof in PROOF.md was developed before this search found
the 2016 answer. Its smaller dimension and generic family are mathematically
different conclusions, but resolving the existence conjecture already follows
by this short adaptation of a public method. A reduced dimension or a generic
parameter version is not being nominated as a separate discovery. Under this
campaign's unusually strict bar, recommend NO CREDIT; at a minimum the
substantive-novelty gate is unresolved. Do not describe the literal Lie result
as a located public theorem: our bounded search located the antecedent method,
not a public source explicitly making the transfer.

## Verification boundaries

scripts/check_exact.py checks this rational table, all 8000 basis Jacobi
identities, centrality of all brackets, derived dimension 14, the defining
relation's rank six, and the separate generic coordinate formula with exact
rational arithmetic. It does not certify the universal no-basis argument in
Lean. The finite calculations support the proof, not replace it.
