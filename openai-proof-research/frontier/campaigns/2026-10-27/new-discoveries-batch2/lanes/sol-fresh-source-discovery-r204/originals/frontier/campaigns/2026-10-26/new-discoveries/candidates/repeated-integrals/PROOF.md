# Repeated-integral conjecture: proposed all-order moment-cone proof

Status: parent mathematical argument, NOT independently reviewed, NOT formalized,
credit 0. Novelty/eligibility HOLD: a general earlier smooth moment-representation
theorem is close enough to require an explicit subsumption decision before a
large Lean investment. No assertion of a new-to-literature theorem is made.

## Exact target

Burke, Haris and Madhavendra, arXiv:2512.02151v1, p.2, Conjecture 1.2.
For n>=0, W_n consists of b=(b_0,...,b_n) for which some f in C^n[0,1]
has all initial derivatives through n zero, terminal derivatives b_j, and
f^(n) increasing (non-strictly) and nonconstant. Statement (P_n) asserts:
W_n is open; every b has a C-infinity witness with f^(n+1)>0 on (0,1),
f^(n+1)(0)=f^(n+1)(1)=1, and all higher endpoint derivatives zero.
The paper proves n<=3. Its Proposition 4.4 permits the equivalent repeated
integral formulation. The author's sequel arXiv:2512.23949v1 remains conditional
on this statement (renamed Q_n); its abstract and discussion before Theorem 4.2
explicitly retain the all-n assumption.

## Moment cone and interior

Fix n. Write p(t)=(1,t,...,t^n) in R^(n+1), and let

    C = { integral p(t) dmu(t) : mu finite positive on [0,1] }.

C is a full-dimensional closed convex cone. Indeed C is the conical hull of the
compact set conv p([0,1]), whose first coordinate is 1. For a convergent sequence
lambda_i y_i in this cone, lambda_i equals its first coordinate. Compactness of
the y_i proves closedness when the limiting mass is positive; boundedness proves
the limit is zero when the limiting mass is zero. Distinct n+1 points give a
Vandermonde basis, proving full dimension.

The dual cone consists of coefficient vectors of polynomials q of degree <=n
which are nonnegative on [0,1]. Thus a nonzero atomless positive measure has
its moment vector in int C: a nonzero such q has finitely many zeros, so its
integral is strictly positive. Supporting-hyperplane separation for closed
full-dimensional convex cones gives the assertion. This includes n=0.

## Smooth densities with prescribed endpoint germs

Let A be the moment vectors of global smooth functions rho such that rho>0
on [0,1] and rho=1 on neighborhoods of 0 and 1. We claim

    A = int C.                                                     (1)

A is convex: a convex combination preserves positivity and equals 1 on the
intersections of the two endpoint neighborhoods.

A is open. Fix a witnessing rho. Choose distinct t_0,...,t_n in (0,1).
Nonnegative smooth, integral-one bumps psi_i supported in sufficiently small
disjoint neighborhoods of these points have moment vectors arbitrarily close
to p(t_i). Their moment matrix is invertible by continuity of the determinant
and the Vandermonde determinant. For all sufficiently small coefficient vectors
c, rho+sum c_i psi_i remains strictly positive: rho has a positive minimum on
the compact union of their supports, and the perturbations vanish outside it.
The endpoint germs remain 1. The invertible moment matrix sends a neighborhood
of c=0 to a neighborhood of the original moment vector. Hence A is open.

The closure of A is C. Approximate any positive measure's finitely many moments
by a positive atomic measure, e.g. partition [0,1] and move the mass of each
piece to a point. Each atomic mass, including endpoint masses, is approximated
in moments by a nonnegative smooth bump supported strictly inside (0,1).
To this finite bump sum add a strictly positive smooth baseline with germ 1
at both endpoints and total integral arbitrarily small. Such a baseline is

    eta + (1-eta)(chi_left + chi_right),

where 0<eta<1 and the disjoint smooth cutoffs equal 1 near the corresponding
endpoint and have supports of arbitrarily small length. Its moments are bounded
by its mass. The resulting densities belong to the defining family of A.
As C is closed and A subset C, this proves closure A=C.

For a nonempty open convex set in finite dimension, int(closure A)=A, proving
(1). This elementary proof does not depend on di Dio's representation theorem.

## Identification with the source data

Suppose f witnesses b in W_n. Set g=f^(n). Then g is continuous,
nondecreasing, nonconstant, and g(0)=0. Its Stieltjes measure mu=dg is finite,
nonzero and atomless, and g(x)=mu([0,x]). For 0<=j<=n, repeated integration
and Tonelli (or induction and integration by parts) give exactly

    b_j = 1/(n-j)! * integral (1-t)^(n-j) dmu(t).                    (2)

For j=n the formula is g(1)=mu([0,1]). For n-j>=1, integrate the kernel
(1-x)^(n-j-1)/(n-j-1)! against g(x), interchange x and t, and integrate
over t<=x<=1 to obtain (2).

Let T be the invertible linear transformation on moment vectors defined by
the polynomials (1-t)^(n-j)/(n-j)! for j=0,...,n. Its matrix is a triangular
change of polynomial basis followed by coordinate reversal; all diagonal
coefficients before reversal are nonzero. The moment vector of mu lies in
int C, so by (1) it is also represented by a density rho>0 equal to 1 near
both endpoints. Define

    F(x) = 1/n! * integral_0^x (x-t)^n rho(t) dt.

F is smooth, its initial derivatives through n vanish, and its terminal
derivatives are b by (2). Moreover F^(n+1)=rho>0, rho has endpoint value 1,
and all positive-order derivatives of rho vanish at both endpoints, exactly
as (P_n) requires. Conversely, every vector in T(int C) is witnessed by
this construction. Therefore

    W_n = T(int C),

which is open. This proves both clauses of (P_n), mathematically, for all n.

## Prior theorem and strict eligibility question

Philipp J. di Dio, arXiv:2411.03145v2 (30 Nov 2024), Theorem 2.5 and
Corollary 2.7, pp.5-6, already provide smooth compactly supported representing
densities for interior moment functionals via Dirac-approximating families.
The relevant actual theorem statements and proof were read, not just its
abstract. The paper cites an earlier 2019 Theorem 17 for the central result.
The 2025 published truncated paper is DOI 10.1007/s00013-025-02175-1.

This theorem gives an alternative short route to (1): subtract from an interior
moment vector the tiny endpoint-one positive baseline above, remaining in the
interior. The interior of the moment cone over (0,1) equals int C (by convex
density and the Vandermonde span). Use interior-supported smooth mollifiers
in di Dio's theorem to represent the residual by a nonnegative finite sum of
compactly supported smooth bumps in (0,1). Add back the baseline. The density
is strictly positive and has the required endpoint germs.

Consequently the source conjecture follows from an earlier general theorem
plus Stieltjes/repeated-integral identification and the baseline construction.
Whether that is a substantive unreported source-question resolution or an
uncountable immediate corollary under this campaign's strict standard MUST be
resolved independently. Do not count the general moment-cone facts themselves,
the n<=3 cases, the baseline lemma, or the source's conditional sequel as new
discoveries. No global priority claim; no MathSciNet/zbMATH screen yet.

## Formal scope

No Lean endpoint exists. A faithful endpoint must quantify all n, encode the
literal C^n monotonicity/initial and terminal derivatives, prove the Stieltjes
moment identity, and construct the smooth witness and endpoint jets. Abstract
moment cone assumptions alone would not certify the source conjecture.
