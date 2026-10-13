# I297 — dimension five is positive; the first same-witness failure is six

**E5 PROVED, subject to the stated credited dependencies and independent review. No acceptance claim; count remains 13/20.**

For every A∈M_5(C), finite m≥1 and finite M_m-valued polynomial P, let M=max_{W(A)}||P||>0. If ||P[A]||=2M, there are constant unit u,v∈C^m such that p=v*Pu satisfies ||p(A)||=2M and max_{W(A)}|p|=M. The full W(A) is a nondegenerate disk; on it p is an affine monomial. Reducible A, repeated spectrum, arbitrary degree and arbitrary finite coefficient size are included.

The [complete proof](../experiments/i297_dimension_five_crouzeix_boundary/analysis.md) combines the authenticated dimension-free original-field part of R016 with an old primary pencil theorem. Leake–Lins–Spitkovsky, [*Pre-images of boundary points of the numerical range* (2014), Theorem 5.7](https://files.ele-math.com/articles/oam-08-39.pdf), allows at most two multiply generated round boundary points for an irreducible 5-by-5 matrix. A repeated maximal branch on a generic interval gives a curved exposed arc of multiply generated round points, contradicting that theorem. The proof supplies the repeated-eigenspace curvature identity, rather than assuming a Q²L factorization or a common eigenvector from a linear branch.

An irreducible active block therefore has a simple-support arc. R016's paid original mass-two field has rank d-1 there; its totally isotropic range and X*Y=0 force both coefficient ranks one. Constant compression of **this P** follows. The reviewed scalar disk/interpolation completion excludes reducing summands outside the active disk and gives the conclusion for all of A.

Together with accepted R019, this decides the exact threshold: **six is the smallest base dimension where an attained finite-polynomial complete-equality witness can fail same-witness constant scalar compression.** This does not claim a strict scalar-supremum gap or failure of disk rigidity.

Seeking a wider complete boundary statement also gives an unreviewed all-dimensional rank ceiling: for an irreducible d≥3 attained polynomial extremizer, every norming input and output has Schmidt rank at most floor((d-1)/2). The proof uses the original-field rank inequality in opposite directions and explicitly excludes the half-dimensional Clifford case. In dimension six the bound is two, attained by R019. No claim that the two ranks must agree is made.

**Primary collision and disposition:** the size-five pencil operation is already in the 2014 theorem, and the complete inverse mechanism is already R016. The positive extension is technical. Neither E5 nor the ancillary rank ceiling is forced into a substantiality nomination. No new nonroutine classification or construction has been established beyond this proved boundary deduction.

**Remaining obligation:** independent I297 proof/contribution review before acceptance; no missing operation remains for E5 within its credited inputs. General six-dimensional disk rigidity, unequal-rank equality channels and classification of rank-two witnesses remain unresolved here.

Sources, hashes and semantic extents are in [literature.md](../sources/i297_dimension_five_crouzeix_boundary/literature.md), [input-authentication.json](../experiments/i297_dimension_five_crouzeix_boundary/input-authentication.json), and [reading-and-failures.md](../experiments/i297_dimension_five_crouzeix_boundary/reading-and-failures.md). Only assigned I297 files were written; no prohibited operation was performed. Output hashes are returned detached.
