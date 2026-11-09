# W007 — an exact component factorization instead of a depth extrapolation

2026-10-08. New parent derivation, PROVISIONAL pending independent review.
No candidate runs, code or Lean changes, or improved factoring bound.

The [completed residual audit](W007-residual-dynamics-review.md) obtains
generic expected root counts tending to 2,4,7 through depth three and asks
whether the next limit is 11. The following identity attacks all fixed
depths together. It also exposes precisely what the random acquisition
fails to supply: many independently splitting components, rather than
merely a high polynomial degree.

## Actual computation and exact factorization

Let P_0(X)=X, a_j=P_j(r_j), and P_(j+1)(X)=P_j(X)(P_j(X)-a_j).
Treat r_0,...,r_(k-1) first as independent indeterminates. Difference of
squares at one update gives

    P_(i+1)(X)-P_(i+1)(Y)
      =(P_i(X)-P_i(Y)) (P_i(X)+P_i(Y)-a_i).

Thus, over any commutative ring,

    P_j(X)-P_j(r_j)
      =(X-r_j) product_(i=0)^(j-1) Q_(i,j)(X),
    Q_(i,j)(X)=P_i(X)+P_i(r_j)-P_i(r_i).

Substitution into the recurrence gives the compactly specified product

    P_k(X)=X product_(j=0)^(k-1) (X-r_j)
                product_(0<=i<j<k) Q_(i,j)(X).             (1)

There are L_k=1+k(k+1)/2 displayed factors. Their X-degrees sum to 2^k:
1+k+sum_(i=0)^(k-2)(k-1-i)2^i=2^k. The factor count is not an assertion
that each factor splits, nor a faster evaluation algorithm. Evaluating
the original tower already takes k multiplications at a fresh point.
For k>=1, exactly 2k displayed factors are linear: X, all X-r_j and
Q_(0,j)=X+r_j-r_0 for 1<=j<k. The rest are nonlinear.

## Proposed geometric interpretation

Fix i<j, and work over the rational-function field in r_0,...,r_(i-1).
The three variables X,r_j,r_i are independent. P_i is monic of degree
D=2^i. The highest homogeneous part of Q_(i,j) in these three variables
is X^D+r_j^D-r_i^D. In odd characteristic, p does not divide D.
For D>=2 this defines a smooth projective plane Fermat curve: its three
partials have no common projective zero. A reducible plane curve over
an algebraic closure would have intersecting components and be singular,
so the homogeneous part is absolutely irreducible. Hence Q_(i,j) is
absolutely irreducible over that coefficient field. D=1 is linear.

Because Q is monic in X, Gauss's lemma should descend this statement to
the polynomial ring in all training variables. The factors in (1) are
distinct: their X-degrees distinguish i, and the newest independent
variable r_j distinguishes factors with equal i; the linear forms are
also distinct in odd characteristic. This argument needs independent
checking, including special characteristics and possible parameter factors.

If correct, the zero set of P_k in affine (k+1)-space has exactly L_k
geometrically irreducible components, each defined over F_p. Fixed-k
finite-field point estimates, subtracting pairwise component intersections,
then give

    E_r[# {x in F_p : P_k(x)=0}] = L_k + O_k(p^(-1/2)).   (2)

This expectation is over the UNSTOPPED uniform training parameters. Removing
the r_0=0 hyperplane preserves the same fixed-k limit. In particular, the
depth-four limit would be 11, not 16. Constants in (2) must not be treated
as independent of k. A candidate primary reference for explicit point
estimates is Cafure--Matera, Theorem 5.2:
https://bibliotecadigital.exactas.uba.ar/download/paper/paper_10715797_v12_n2_p155_Cafure.pdf .
The parent opened the paper and inspected theorem-related text; the full
application and intersection bound are assigned for audit, not assumed.

## A more explicit proposed upper bound using exponential sums

There is also a direct way to bound the expected roots contributed by each
Q, without assuming that its specialized univariate fibers are irreducible.
Fix all parameters before r_i, and set f=P_i, degree D. For D<p define

    S(t)=sum_x exp(2*pi*i*t*f(x)/p),
    C_f=# {(x,y):f(x)=f(y)} <= D*p,
    T_f=# {(x,y,z):f(x)+f(y)=f(z)}.

Orthogonality and Parseval give

    T_f=p^2+(1/p) sum_(t!=0) S(t)^2 S(-t),
    sum_(t!=0)|S(t)|^2=p*C_f-p^2.

The standard additive Weil bound |S(t)|<=(D-1)*sqrt(p), t!=0,
would yield

    |T_f/p^2-1| <= (D-1)^2/sqrt(p).                      (3)

Here T_f/p^2 is exactly the expected number of roots in X of
Q_(i,j), since r_i and r_j are fresh independent uniform parameters
relative to P_i. This remains true when the intervening later coefficients
are generated adaptively: Q depends on neither of them.

Union-bounding the displayed factors in (1), with each linear factor
contributing exactly one root, gives, provided 2^(k-2)<p,

    E[m_k] <= L_k + B_k/sqrt(p),
    B_k=sum_(i=0)^(k-2) (k-1-i)(2^i-1)^2
       =(4^k-3k-1)/9 - 2*(2^k-k-1) + k*(k-1)/2.       (4)

For k=1, interpret the sum as empty (B_1=0); k=0 is trivial. This
controls a growing-depth range if audited: B_k=O(4^k), so the additive
error is o(1) for k<=(1/4-epsilon)*log_2(p).

Primary source to verify for the exact Weil hypotheses:
https://people.math.ethz.ch/~kowalski/exponential-sums-elementary.pdf .
The parent subsequently read Theorem 3.2 on printed page 31: it assumes
d<q, gcd(d,q)=1, and a nontrivial additive character, exactly satisfied
by the displayed monic degree D<p over an odd prime field. The use of
Parseval, conditional averaging, and the geometric argument remain for
independent audit.
Beware the stale URL exp-sums.pdf: it now serves Kowalski--Soundararajan's
different paper Exponential sums, twisted multiplicativity and moments.
Its introduction is not a substitute for checking the uniform theorem.

An optional quantitative lower bound uses distinctness/irreducibility and
an affine degree/point bound for pairwise intersections. If each pair of
degrees d,e contributes at most de*p^(k-1) points, (3) would imply

    E[m_k] >= L_k-B_k/sqrt(p)-2^(2k-1)/p.                (5)

The intersection theorem and all its field-size conditions are NOT yet
verified; keep (5) provisional. The sum of pairwise degree products is
at most (sum degrees)^2/2=2^(2k-1). No enumeration can replace this check.

## Algorithmic consequences and changed question

If accepted, this removes the need to extrapolate a depth curve or compute
one more finite-depth table to explain the initial triangular growth.
It does not bound k near or beyond (1/4)log_2(p) by a useful uniform error,
and it does not prove a stopped factoring runtime. Conditioning on survival
at both primes changes the distribution. Fixed-horizon unstopped CRT
histories, on the other hand, ARE independent between p and q when all
updates are componentwise functions of independent uniform CRT tapes;
sharing the written integer residues alone does not destroy independence.

The constructive next computation should change acquisition, not simply
increase degree under the same independent-r rule. Equation (1) exposes
the concrete nonlinear factors Q_(i,j): obtain correlations among training
parameters that split many of these factors locally while charging the
work to construct those correlations. Substituting rational relations that
only plant known roots globally must be priced against direct batch
collision detection; it does not give free useful roots. No such correlated
generator has been supplied here. The other live branch instead tries to
remove the scalar-product detector's quadratic intermediate entirely.
