# MathDB 365301: ordinary counterexample, formal endpoint not completed

This is a candidate for root review, not an accepted result. No Lean theorem is claimed.

Use vertices 0,1,2,3,4, root 0, z vertices 0,3,4, and w vertices 1,2. The edges are 01,02,03,13,24,34. This is a connected finite simple graph. Its root has distance 1 from the nearest w vertex. Conjecture 6.1 of Tully-Doyle–Adlin–Thai–Tiscareno, arXiv:2410.10695, therefore predicts contact order 2.

Let A be its adjacency matrix and let M=A-diag(z,w,w,z,z). In the source's convention the representation is f(z,w)=(M^{-1})_{00}. Direct determinant expansion gives f=N/Q, where

N=(wz-w-1)(wz+w-1),
Q=-w²z³+2w²z+4wz²+2wz-w-3z.

The determinants are computed by scripts/contact_exact.py, independently expanded by scripts/contact_checks.py. N and Q are coprime. The two roots of N are w=1/(z-1),1/(z+1); substitution into Q gives nonzero rational functions (see logs/contact-checks.log), so neither root is a canceled component.

For a positive real level L, put t=1/z and w=t u. The level equation N-LQ=0, multiplied by t, is

F(t,u,L) = [L(1-2t²)+t-t³]u² + [-4L-2Lt+Lt²-2t]u + 3L+t = 0.

At t=0 this is L(u-1)(u-3). Each root is simple. In particular both roots extend uniquely to real analytic functions of t near 0. This can also be seen directly: write F=A_L u²+B_L u+C_L; its discriminant at zero is 4L²>0 and A_L(0)=L>0. The quadratic formula with the positive analytic square root gives the two branches. They yield all level-curve branches near (infinity,0), since the equation has degree 2 in w.

For the root near u=1, coefficient comparison gives

w_{L,1}(t) = t-t²+t³-(1/2)t⁴-t⁵+(17/4-1/(2L))t⁶+O(t⁷).

For the root near u=3, it gives

w_{L,3}(t) = 3t+(3-2/L)t²+O(t³).

These are identities for arbitrary positive L, not a fit from numerical samples. Substitution and coefficient cancellation through degree 6 are performed symbolically in scripts/contact_exact.py. A second calculation expands the actual quadratic radicals independently at L=1,2,3 in scripts/contact_checks.py.

Consequently, for any distinct positive L and H, the differences between corresponding branches have orders precisely 6 and 2: their first nonzero coefficients are (1/(2H)-1/(2L))t⁶ and (2/H-2/L)t². Branches are matched by their distinct first derivatives 1 and 3. There are no additional branches.

The contact-order convention used in the source is the maximum of the vanishing orders of the corresponding generic level branches. This convention is explicitly stated in Bickel–Hong arXiv:2506.12624, Remark 3.2, which cites the underlying general theorem. Conformal changes from z=infinity to t=0 and from the half-plane to the disk have nonzero local derivatives; they preserve these orders. The positive real levels give an open set of levels and the formulas hold for every pair of distinct such levels, so exceptional finite choices of levels do not affect the conclusion. The contact order at (infinity,0) is therefore 6, whereas twice the nearest-w distance is 2.

## Why this is not just the already solved one-w case

The source's Theorem 4.6 treats precisely one w vertex. The example has two. The extra branch has weak coupling to the root, with cancellation of lower-order dependence on the level. The proof of Theorem 4.6 uses a scalar Schur complement and cannot supply the asserted common order for multiple w vertices. Bickel–Hong's three extensions in Theorem 1.5 also retain the one-w model. No contradiction to their proved theorem is claimed.

## Review and formalization gaps

The exact algebra above is reproducible, and supplies an ordinary analytic counterexample subject to independent review of the contact-order convention. It is not a Lean solution. The unresolved formal bridges are: adjacency/diagonal matrix inverse to the displayed coprime quotient; existence and exhaustiveness of the two analytic branches; exact analytic order 6 and 2 rather than truncated jets alone; preservation of order under the conformal maps; and the definition of source contact order as the maximum over generic branches. A theorem solely about the printed polynomials or jets would not meet the assignment's literal endpoint requirement, and none is presented as such.

The bounded prior-art search read the source's single-w proof and open-question paragraph, Bickel–Hong's contact definitions and adjacent single-w extension statements/proofs, and screened current public proof registry paths. No matching public counterexample was located. The exact primary theorem underlying Remark 3.2 was not independently re-proved; source semantics and its application still need adversarial review. The journal version of Bickel–Hong was located by search, but only its accessible arXiv body was read. Global novelty is not certified.
