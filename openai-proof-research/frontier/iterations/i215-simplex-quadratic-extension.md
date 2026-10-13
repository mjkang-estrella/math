# I215 parent extension: quadratic certificates for regular simplices

2026-10-12. **Author-level extension; no independent gate completed and no additional finding counted.** This is part of I209's same density/chord mechanism, not a second finding.

Let S be a regular n-simplex, n>=4, and A_min its minimum (n-1)-dimensional projection volume. Every finite cover by cylinders B_i+R u_i with measurable bases satisfies

    sum_i |B_i| >= 3/[sqrt(2)(n+2)] A_min(S).

The proposed constant is optimal among the same degree-at-most-two nonnegative polynomial density certificates. In dimension three the I209 optimized constant sqrt(15)/9 remains stronger than 3/(5sqrt(2)). The general bound is a proposed extension of that single contribution.

## Calculation

Normalize edge length to two and center at the origin. Write N=n+1, b=2/N, R^2=2n/N, and c=R^2/(n+2). The vertex Gram matrix has diagonal R^2 and off-diagonal -b, hence |x|^2=2 sum lambda_i^2-b. Uniform simplex integration gives mean |x|^2=c: each barycentric coordinate has second moment 2/[N(N+1)].

For a>=R^2 use f_a=(a-|x|^2)1_S. If a chord has length l and midpoint m, its integral is l(a-|m|^2-l^2/12). The I209 barycentric argument gives

    |m|^2 >= max(0,l^2/4-b),    0<=l<=2.

On l<=2sqrt(b), the upper envelope l(a-l^2/12) is increasing because its derivative is a-l^2/4>=R^2-b>0. On the complementary interval the envelope is l(a+b-l^2/3). Since a+b>=R^2+b=2 and 4b<=2 for n>=3, the global maximum is

    M(a)=(2/3)(a+b)^(3/2) for R^2<=a<=4-b,
    M(a)=2(a+b-4/3) for a>=4-b.

This bound is attained: use four different vertices and endpoint barycentric coordinates (z,1-z,0,0,...), (0,0,z,1-z,0,...), z in [1/2,1]. Their supports are disjoint, their squared distance is 2+8(z-1/2)^2, and they are the full intersection of their affine line with S. Thus all maximizing lengths from sqrt(2) to 2 occur, including boundary-face chords in dimensions greater than three.

The accepted simplex identity in `frontier/sources/i209_elliptic_tetrahedron/radial-projections.tex`, proposition `prop:simplex`, gives A_min=n Vol(S)/2. The certificate is consequently

    Q_n(a)=(3/n)(a-c)/(a+b)^(3/2) for R^2<=a<=4-b,
    Q_n(a)=(a-c)/[n(a+b-4/3)] for a>=4-b.

The first derivative has the sign of 2b+3c-a. Its root is a_*=(10n+8)/[(n+1)(n+2)], and a_*-R^2=-2(n-4)/(n+2). Thus a_* equals R^2 at n=4 and lies below the admissible interval for n>4. The second derivative in the other regime has the sign of b+c-4/3<0 for n>=3. The maximum for n>=4 is at a=R^2, where Q_n=3/[sqrt(2)(n+2)]. The density vanishes at vertices but has positive integral, so nonnegativity suffices.

To optimize over all quadratics, average over the simplex symmetry group. The standard n-dimensional permutation representation on sum coordinates zero is irreducible and its invariant symmetric bilinear forms are scalar multiples of the Euclidean one: directly, a permutation-invariant quadratic in N barycentric coordinates has one diagonal and one off-diagonal coefficient, whose restriction to sum lambda_i=1 is a constant plus a multiple of sum lambda_i^2. Thus the averaged polynomial is alpha+beta|x|^2. Averaging preserves its mass and cannot increase its maximal line integral.

For beta>=0, alpha>=0. On an edge, mean |x|^2=R^2-2/3>=c, so its certificate is at most 1/n. For beta<0 rescale to the preceding a-|x|^2 family. Since 3/[sqrt(2)(n+2)]>1/n for n>=4, the candidate gives the exact quadratic optimum. Tonelli then proves the actual finite-cover bound for arbitrary measurable finite-volume bases as in I209.

## Evidence limits

This is written parent mathematics, not a completed independent proof or contribution assessment. The parent checked the exact general-dimensional simplex projection proposition in the retained pinned source and conducted preliminary primary-source searches for regular-simplex cylinder bounds. Search results found the 2009 Bezdek–Litvak cylinder paper and unrelated translative lattice-covering results; this is not a sufficient global novelty check. No new source copy, numerical experiment, code, test, or source-truth audit was used. The existing 2009 comparison and source records remain in the I209/I211 packages.

The extension should be sent for separate validation before any accepted statement is enlarged. It cannot supply both the ninth and tenth findings: it is the same weighted-chord bridge.
