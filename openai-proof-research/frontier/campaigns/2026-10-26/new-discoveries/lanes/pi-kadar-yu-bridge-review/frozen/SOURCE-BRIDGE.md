# Source interpretation of the arbitrary-head Gram model — review required

This is a proposed bridge for MathDB372352 / Morris–Martin2512.24535v1,
Conjecture4.5.1, NOT an acceptance record. The campaign tally stays16/30.
The new model eliminates the previous cyclic-compression premise and does not
assume its determinant factorization, quotient coprimality, or root conclusions.
An independent adversarial source/formal-scope/novelty review must decide whether
this source interpretation is sufficient or identify exact missing Lean bridges.

## Exact source and parameters

The primary PDF SHA256 is
2d6f180bf33021ca6ab819928dfe51c91d44bed2eba8ccf03d2e443ed6bf5c86.
Relevant printed statements were re-read in the retained actual source text:
(3.7), (3.13), (3.2.3), (3.2.4), (3.17), (3.2.9), (3.2.12), Theorem3.19,
(3.2.17), Proposition3.25, and Conjecture4.5.1 on p35. The original preliminary
review checked the corresponding rendered source and two printed Gram examples.

Fix l>=-1, a partition lambda of l+2, d=dim Specht(lambda)>=1, and N=l+4.
Choose the source's real orthonormal Specht basis. In the mixed family(3.17),
keep d-1 tail parameters equal to N, and vary only the final one from N to N+s.
The resulting initial mixed Gram matrix has a finite NONEMPTY head of size m.
Its attaching basis element is u_(l+3,l+4) b_d. Reorder that element last.
All other heads and all fixed tails remain inside the finite head; no direct-sum
assumption, absence of cross-head couplings, or cyclicity is made.

By(3.2.3), the initial matrix is alpha*I+G, G real symmetric. By(3.2.4) and the
literal border display(3.2.17), adding a tail vertex gives diagonal alpha, a
single coupling+1 to the old final tail vertex, and zero other new entries.
This is exactly gramModelMatrix with h=m-1, arbitrary head G, and s new vertices.
The supplied finite real matrix G is the ONLY model data apart from h. No rank,
inertia, factorization, reducedness, or existence assumptions appear in the
closed gramModelReduced_root_distribution endpoint beyond G.IsHermitian.

## Literal formal convention

headTailMatrix h A c s is an explicit matrix: on the initial(h+1)-square block
it is A; elsewhere it has zero diagonal and entries c on adjacent indices.
It preserves every entry of the head, including couplings between Specht heads.
headTailMatrix_prefix and headTailMatrix_succ_border prove the exact inclusions
and borders for every finite real head, without a tridiagonal hypothesis.

gramModelMatrix = alpha*I + headTailMatrix h G 1 s, as a matrix over R[alpha].
The proven identity gramModelMatrix_eq_charmatrix identifies it with the actual
characteristic matrix of headTailMatrix h(-G)(-1)s. This explicitly resolves the
sign convention; no positive-tail/negative-root identification is assumed.
Both couplings+1 and-1 satisfy c^2=1 in the general head theorem.

## Actual reduction, not a surrogate polynomial

gramModelDeterminant is the literal determinant of gramModelMatrix.
gramModelReduced is that determinant divided by the normalized gcd of the
s=0 and s=1 determinants, exactly the monic maximal-common-factor construction
in(3.2.12). The formal code PROVES:

- the gcd is nonzero and monic;
- it divides every determinant through the genuine border recurrence;
- every quotient is monic and consecutive quotients are coprime;
- the quotient series satisfies the source MINUS recurrence;
- every quotient, and X*p_0-p_1, is squarefree;
- the exterior root multiset count eventually stabilizes;
- the real root union in the CLOSED band[-2,2] is dense, including endpoints.

The source Proposition3.25 gives det Gamma_(N+s,N,...,N) = F*P_(N+s), with
F = C(lambda)*P_N^(d-1) FIXED and monic in this orthonormal convention.
Ramping/reducedness gives coprimality of P_N and P_(N+1). The proven
reduced_series_identification and gramModelReduced_identification force P_(N+s)
to equal the actual gcd quotient, retaining ALL repeated factors of F even
when F and P_N overlap. No assumption gcd(F,P_N)=1 occurs.
At k=-1, the source recurrence gives P_(N-1)=X*P_N-P_(N+1). The formal code
proves this is the quotient of the attaching-coordinate principal minor and
establishes its squarefreeness by the same multiplicity argument, not by merely
assuming a boundary polynomial has the right roots.

## Explicit formal-scope questions for the independent reviewer

1. The new closed endpoint quantifies over EVERY finite real symmetric head,
   not a type of Specht partitions. The literal one-tail matrix and normalized
   gcd are implemented. Does this universal model plus the source's ALREADY
   PROVED real-head/path equations give an adequate faithful formal certificate
   for the full source conclusion, or is an additional Lean representation of
   Specht modules/mixed-basis reindexing essential under this campaign standard?
   Do not decide by theorem name. Identify any uncovered hypothesis or claim.
2. The source works over C[alpha]. ComplexGram.lean now defines the ACTUAL
   quotient over C using the normalized gcd over C, and PROVES that this is
   the coefficient map of the real gcd quotient. The normalized-gcd map,
   polynomial division, evaluation at real arguments, squarefreeness (including
   the boundary), complete root MULTISET map, reality of EVERY complex root,
   complex exterior-root count outside the embedded real interval, and closed-
   band density are all formally transferred. A separate complex identification
   theorem matches ANY monic source factorization with initial coprimality.
   This is an implemented coefficient-extension bridge, not an interpretation
   assumed from equal numerical roots. Inspect its actual types and proof.
3. The derivation invokes the source's previously proved Proposition3.25 and
   reducedness as source dependencies, not new mathematical hypotheses of
   Conjecture4.5.1. These source Specht facts are NOT re-proved in Lean here.
   If this is a decisive scope defect, report HOLD with the precise required
   endpoint rather than silently accepting a hypothetical head-family theorem.
4. All spectral/multiplicity tools are classical and receive zero separate
   credit. The ONLY prospective new outcome is a full resolution of the exact
   source conjecture for every lambda and all k>=-1. Compare nearest classical
   finite-rank Jacobi/spectral-measure results and later/citing source work;
   a generic theorem's correctness alone does not establish a new discovery.

The preliminary source/math review applies to an earlier hand proof via Lanczos,
not automatically to this new multiplicity route or the closed Gram/gcd model.
The latter needs independent fresh review. No manuscript or proof packet for
this candidate has been accepted, and the accepted tally remains16/30.
