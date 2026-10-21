# r173 — finite columns in the original properly infinite target

PREFREEZE calculations, not a frozen candidate or an author-proof submission. All Source303 proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. The complete source and the operative primary interfaces recorded in private/READING-LIMITS.md were read before these extended deductions. The calculations below deliberately retain the finite-column cost until the step that actually removes it.

## 1. The patching operation and its actual cost

Let K be a nonempty compact Hausdorff space, A a complex C*-algebra, and a,b positive contractions in B=C(K,A). Suppose a(x) is Cuntz subequivalent to b(x) for every x. Fix e>0. Scalar-corner compression of stable comparison supplies t_x in A with

    ||t_x* b(x) t_x-a(x)|| < e/4.

Continuity gives an open neighborhood U_x on which the error is <e/2. Choose a finite subcover U_1,...,U_m and a continuous partition of unity phi_i subordinate to it. With t_i the corresponding fixed algebra elements, put S_i(y)=sqrt(phi_i(y))t_i and S=(S_1,...,S_m)^T. Scalar continuous functions act as central multipliers even when A has no unit. Thus every S_i belongs to B, and

    S* diag_m(b) S = sum_i phi_i t_i* b t_i,
    ||S* diag_m(b) S-a|| < e/2,
    ||S||² = ||sum_i phi_i t_i*t_i|| <= M²,
    M=max_i ||t_i||.

The strict uniform error follows either from compactness and continuity or from the uniform local e/2 bound. This gives comparison into m copies of b. It does not, in a general algebra, give comparison into b. The number m is the cover cost; it has not vanished by convex averaging. The construction uses no finite covering dimension or metrizability of K. Empty K and zero algebras give zero statements.

For the remainder assume A satisfies P: every positive element, including zero, is properly infinite. Source303 gives strong pure infiniteness without exactness, nuclearity, separability, or unitality. Kirchberg–Sierakowski v2 Theorem1.3 and its Section6 proof apply with the exact factor C(K); hence B is strongly purely infinite and satisfies P. This is already-paid tensor permanence. No inference is being made for arbitrary maximal tensor products or for a nonexact second tensor factor.

## 2. One row absorbs all m target copies after one common cutoff

Fix 0<delta<1/2, h=(b-delta)+, and k=diag_m((b-2delta)+). Proper infiniteness of h gives diag_m(h) subequivalent to h by finite iteration of block comparison. Apply source foundations.tex, lem:transport, with the single cutoff delta to this comparison. It supplies a rectangular bidual partial isometry w such that

    w*w=e_k, ww*<=e_h,
    r=w k^(1/2) belongs to M_(1,m)(B),
    r*r=k, e_h r=r, ||r||<=1.

Membership of r follows from the actual transport regularity; membership of w itself is neither needed nor asserted. Define the continuous function, zero at zero,

    f_delta(t)=t/delta^(3/2) for 0<=t<=delta,
               t^(-1/2)   for t>=delta.

The row R=f_delta(b)r belongs to M_(1,m)(B), and

    b^(1/2)R=r,
    R*bR=diag_m((b-2delta)+),
    ||R||<=delta^(-1/2).                                      (2.1)

This is the source product-row construction with m finite copies in place of two; the source already proves the rectangular transport and finite block comparison needed for the replacement. In particular the row norm in (2.1) does not grow as sqrt(m). No coordinatewise estimate has been substituted for a matrix norm estimate.

Now T=RS is a single element of the ORIGINAL B. It satisfies

    ||T*bT-a|| < e/2+2delta M²,
    ||T||<=M/sqrt(delta).                                    (2.2)

Choose delta<min(1/2,e/(4 max(1,M²))). The error is <e, so repeating for e down to zero gives a subequivalent to b in B. If M=0 the same estimates work, with S=T=0. This concludes the entire finite-column compression, not just its stable version. Constants depend on local comparison coefficients through M. There is no universal bound on M for arbitrary input pairs from mere pointwise comparison.

## 3. Where the common target cutoff matters

For a bounded product of algebras satisfying P the same construction can be carried out coordinatewise with one delta and one m. The row bound delta^(-1/2) places the rows in the bounded product. For an arbitrary coordinatewise comparison a_i subequivalent to b_i, no such argument follows merely by choosing coefficients separately: a common target cutoff is needed. This is exactly the quantifier in Antoine–Perera–Thiel v2 Lemma5.7, read with its proof. Here proper infiniteness of each (b_i-delta)+ supplies that common cutoff for the repeated-copy operation. It does not prove a new unrestricted product-comparison criterion.

Similarly, (2.1) is not an algorithm for evaluating R from b with a universal finite search budget. The source transport has existential Cuntz coefficients. Its later support constant theta is existential too. An explicit displayed norm bound is not a computed bound on the time, polynomial degree, matrix-model dimension, or modulus of continuity needed to find a witness.

## 4. The r172 comparison has a different geometry

The completed r172 finite-Fourier patch produces m target blocks, and its coinduction construction produces |G|^u duplicated outputs. Those are real costs. The present calculation removes an m-fold repeated positive target only because that target and its cutoffs are properly infinite in the actual function algebra. It does not produce an embedding of a finite-rank occurrence bundle into its original palette. A finite-rank vector-bundle target does not acquire proper infiniteness by writing down a Cuntz comparison elsewhere.

In particular, the free-cover Thom obstruction in r172 still says only that unchanged-slot descent cannot follow from upstairs embedding data alone. Nothing here contradicts that obstruction, proves a radius inequality/equality for any actual algebra in r172, or excludes a construction using stronger quotient-compatible data. Actual occurrence-bundle compression and original-palette saving remain unpaid there.

## 5. Why this is retained but not nominated

The closed operation is finite patching followed by the already-proved proper-target row construction, using already-proved tensor permanence to ensure the target really is properly infinite. It establishes applicability and records the coefficient cost. It is a routine source/primary composition, so it is not offered as the substantial result requested by the campaign. The simultaneous mixed-term issue, which cannot be settled just by independently applying (2.1) twice, is handled next in MIXED.md.
