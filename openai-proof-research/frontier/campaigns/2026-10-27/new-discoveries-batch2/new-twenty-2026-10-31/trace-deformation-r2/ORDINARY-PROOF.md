# Explicit deformation of the arXiv reduction: ordinary proof and formal boundary

Scope: Hoge, **arXiv:1104.0904v1**, Conjecture 2.10, Definition 2.5 and its five-step algorithm, with E of Lemma 3.2 and the fixed list of Theorem 4.1/Remark 4.2. This document gives an ordinary finite-certificate counterexample argument for that version. It is **not** a Lean proof, a published-version comparison, a novelty clearance, or an accepted MathDB solution. All finite identities described below were checked by `verify_certificates.py` using rational arithmetic, not kernel checked.

The argument uses the source facts that N(3)=6 and E generates C33. It does not use the second fundamental theorem, the claimed rank 104/105, completeness of the old 243-column enumeration, a one-dimensional relation-space assertion, or Theorem 4.1's presentation computation. The lower columns are used only as explicit identity witnesses. No source theorem is imported into Lean as an axiom; no Lean project is claimed.

## Explicit data and sign convention

Write [w] for a cyclic formal trace. We use

    F(B1,B2,B3,B4) = sum over σ in S4 of sign(σ) product over cycles C of [product of Bj along C].

Changing the overall sign of F changes neither its identities nor its reduction. Each F vanishes on 3 by 3 matrices: expand the trace products by matrix indices; the alternating sum is the contraction of the alternating operator on four tensor factors of a three-dimensional space, which is zero. This argument applies to arbitrary matrices substituted for the four B's, including nonconstant words.

Let q be the exact polynomial called `q` in the hash-bound sibling `trace-exact-polynomials.json`. That file supplies its 16-term linear combination of F's. The verifier reconstructs the complete polynomial from that combination; no membership test or rank is used. Q is its **unnormalized** full polarization, assigning 1,2,3 to the three occurrences of the first letter, 4,5 to the second and 6,7 to the third and summing all 3!2!2! assignments. Each term has every label once and each trace factor has length at most six. Polarizing the displayed fundamental-identity combination proves Q is a matrix trace identity. Q has 1374 nonzero terms.

For explicit P0, take the 713 tuple/coefficient entries of the thesis pp.95–103, reproduced in `explicit-reduction.json`. The verifier expands their F combination H and proves its complete single-trace part is **−[1234567]** in our sign convention. Thus H=−[1234567]+P0, with P0 the stored shorter-trace polynomial. Consequently [1234567]=P0 is a genuine identity, not merely the three specializations used later.

Set

    P* = P0 − (47/864) Q.

This is an explicit rational polynomial, not an existential parameter. Both P0 and Q are stored expanded in `explicit-reduction.json` as well as by their source definitions.

## Admissibility, embedding and reduction

P* satisfies the literal Definition 2.5: its difference from [1234567] is a matrix trace identity; every label occurs once; no trace factor has length seven; all coefficients are rational and hence complex. Polarizing the certificate for q expresses Q as a combination of the same allowed multilinear four-word fundamental identities. Its single-trace part is zero, so adding it preserves the Ax=e1 normalization in Section 2. It is not an arbitrary alteration of separately chosen degree-seven traces.

The thesis Definition 6.2.3 additionally works with the first six arguments traceless and the last arbitrary. Our full-matrix identity remains valid under that restriction. The article's full identity is stronger than this restriction, so admissibility does not depend on treating a traceless-only identity as a full identity.

In a trace of length k>6 the algorithm substitutes six single letters and a suffix of length k−6. A proper factor of P* contains at most five of the first six letters if it contains the suffix; it therefore has length at most k−1. If it omits the suffix, its length is at most six. This proves termination, including for k=7. Canonical cyclic representatives are always the lexicographically least rotations, as prescribed. Every step preserves multidegree and actual matrix evaluation.

Here is an elementary justification of the literal CE embedding. Make the triangular change of formal trace coordinates from X,Y,Z to x=X−[X]I/3, etc., with [empty]=3. For length at least two, a centered trace has leading term [w] and the other terms have shorter word length, with polynomial coefficients in [X],[Y],[Z]. The inverse substitution is X=x+[X]I/3, etc. Thus the full formal trace ring is the polynomial algebra on [X],[Y],[Z] and the centered cyclic words of length at least two. The 45 centered E generators are linear combinations of these primitive centered trace variables. They are linearly independent: a linear dependence in any degree at most six would contradict the finite evaluation injectivity certificate below. Linear independence of these linear forms gives the required polynomial embedding, by extending them to a basis degree by degree. This also distinguishes the polynomial algebra CE from the invariant algebra, where p below vanishes.

The `low-injectivity.json` certificate covers **every** centered CE monomial of total weight at most six, in 80 nonempty components, 308 monomials, maximum component dimension 21. For each component it supplies square evaluations on explicit integer traceless matrices and a rational inverse. The independent verifier re-evaluates the literal E expressions, checks every inverse by multiplication, and independently enumerates all monomials as multisets of at most three generators. The latter suffices because every centered generator has weight at least two. Empty components have no positive-weight monomials. Therefore the actual matrix specialization of the centered polynomial CE is injective in weights at most six. Adding the three scalar trace variables preserves this conclusion: the change from arbitrary matrices to independent scalar parts plus traceless matrices is an invertible linear change of matrix coordinates.

By the source generating theorem, each trace of length at most six has an expression in E. Injectivity just proved makes that expression unique. Extend these evaluations multiplicatively; use P* recursively for longer traces. This constructs the source evaluation map R*, fixes every E generator, and commutes with actual matrix specialization. In particular it kills every trace identity of degree at most six. This is a proved low-degree fact, not an arbitrary retraction hypothesis. The same construction works for P0+tQ for every complex t.

## Explicit polynomial in the literal generators

Let q0 be q after setting the three singleton traces to zero. The exact elimination certificate gives

    q0 = p(E) + sum_i c_i L_i,

where each L_i is a product of an explicit fundamental identity of degree at most six with a complementary formal trace monomial, after singleton deletion. Indices refer to the hash-bound sibling columns; their explicit expressions, rather than their alleged span completeness, are what is needed. Applying any of the maps above kills these lower identities, so R(q0)=p in polynomial CE. The ten-term polynomial is

    p = (T1 T35 + T4 T34 + T5 T33)/6
        − T7 T20/3 + T10 T23/3 + T11 T22/3
        − T12 T19/3 − T14 T18/3 + T16 T21/6 − T17 T24/2.

This is nonzero in polynomial CE: the assignment T1=6,T35=1, all other Ti and scalar trace variables zero, gives p=1. This assignment is a separating evaluation in CE; it is deliberately not a tuple of actual matrices. Matrix evaluation gives p=0, since q0 is an identity and the Li are identities. Thus p is a nonzero homogeneous relation of multidegree (3,2,2).

This closes the old unproved passage from q outside a span to R(q) nonzero, without invoking that span's equality with an elimination ideal. There is no rank inference here.

## Annihilation and the exact fixed list

Put M=(111,22,3,3). Its single-trace part is

    −2[1112233] −2[1113223] −2[1113322].

For degree seven all remaining factors have degree at most six, so their evaluations do not depend on t. Direct substitution of the stored P0 and Q at the **canonical rotations**, followed by the same finite elimination certificates, proves after singleton specialization

    R0(F(M)) = −47p/12,
    (Rt−R0)(F(M)) = −72t p.

`finite-elimination.json` supplies the linear combination witnesses for both equalities, and the independent verifier expands them. These are exact polynomial CE equalities after setting the scalar trace variables to zero.

To pass back to full CE, let I be its actual matrix-specialization kernel. Every homogeneous degree-seven element of I is independent of the scalar trace variables. Indeed, expand it as a polynomial in the three independent scalar parts. Any coefficient of a positive scalar degree is a centered CE relation of degree at most six and must be zero by the finite injectivity result. Hence each R_t(F(M)), and also their differences, is determined by its scalar-zero specialization. The displayed equalities therefore hold in full CE. No one-dimensionality of I_(3,2,2) is needed.

At t=−47/864 the sum is zero. Remark 4.2 requires checking the stabilizer of (3,2,2), not merely the distinct permuted multidegrees. The second possibility is M'=(111,33,2,2). Its full-trace words include [1112332] in place of [1113223]. It was checked separately, and the certificates give exactly the same −47/12 and −72 multiples of p. Both selected relations of degree (3,2,2) therefore vanish. Every other letter permutation has another multidegree. All other displayed tuples have total degree at least eight; their actual degrees are determined by their words, regardless of any table heading misprints.

An ideal generated by homogeneous polynomials of total degree at least seven has degree-seven part equal to the constant span of its degree-seven generators. Constants cannot change multidegree. Consequently the ideal generated by the fixed list under R* has zero component of degree (3,2,2), whereas the actual ideal contains p≠0 in that component. The fixed list does not generate that ideal, and therefore is not a minimal generating set. This negates the universal choice-of-reduction assertion in the **arXiv v1** Conjecture 2.10.

## Unmet endpoint requirements

The ordinary argument survives the adversarial checks performed here. No fatal mathematical obstruction was found. Nevertheless these are Python-verified exact arithmetic certificates, not Lean-verified certificates. There is no literal Lean theorem defining the trace ring, centered embedding, matrix specialization, admissibility, recursive reduction and prescribed fixed set. In particular no #print axioms audit or extracted warnings-as-errors replay exists. The source-to-Lean and certificate-to-kernel gaps remain substantive. No weakened conditional theorem was substituted for that endpoint.

The published 2012 body also remains unavailable in this bounded search. The checked current author page has no article attachment; arXiv still lists only v1. This does not prove the published conjecture is unchanged. The argument's scope is deliberately limited to the supplied arXiv source. See `prior-checks.json` for chronology and exact limits. Credit remains zero.
