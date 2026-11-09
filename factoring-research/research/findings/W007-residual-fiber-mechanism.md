# W007 — residual fibers and the cost of adaptive absorption

2026-10-08. Parent constructive continuation; new formulas below are PROVISIONAL
until the assigned independent audit. No experiment, candidate execution, or
factoring improvement. This route drops the requirement of rational splitting.

## Actual computation and the useful statistic

Start P_0(X)=X. At stage j draw a fresh uniform r_j modulo N, evaluate
a_j=P_j(r_j), test gcd(a_j,N), and update P_(j+1)=P_j(P_j-a_j).
A later fresh probe x is tested by gcd(P_j(x),N). All coefficients and
training evaluations are actually obtained; naive acquisition through depth k
uses Theta(k^2) modular arithmetic operations, and each fresh probe Theta(k).
One can also test gcd(P_j(x)-a_j,N) before multiplying: retain such factor
opportunities explicitly rather than lose them to a full gcd of the product.

Over one odd prime fix a current output law mu. Write z=mu(0), and let
nu(0)=0 and nu(y)=mu(y) for y!=0. Define

    v=sum_y nu(y)^2,    t=sum_y nu(y)^3,
    R=sum_y nu(y)nu(-y),
    Q=sum_(y,w) nu(y)nu(w)nu(y+w),
    D=sum_y nu(2y)nu(y)^2.

The accepted first-stage law is E[Delta z]=v. Full collision mass is
c=z^2+v: increasing c by accumulating mass at zero need not improve future
absorption. The candidate exact residual law is

    E[v_next-v | mu] = z R + Q - D - t.

Derivation: E[Delta c]=2zv+zR+Q-D by expanding the accepted cubic
convolution formula and cancelling its zero diagonal. Also Delta z=nu(a)
for a drawn from mu, so E[(Delta z)^2]=t. Subtract
E[(z+Delta z)^2-z^2]=2zv+t. These are local conditional laws, not a
joint stopped CRT independence claim.

Thus the missing growth mechanism is precise: generate nonzero fibers with
enough additive triples Q-D (off the equal-input diagonal) and opposite
pairs R to replace fibers consumed by the t term. Total collision mass c
alone does not answer that question.

## Two exact controls and one heuristic to challenge

For a uniform initial field law, z=1/p, v=(p-1)/p^2. Direct counting gives

    R=(p-1)/p^2,
    Q=(p-1)(p-2)/p^3,
    D=t=(p-1)/p^3,
    E[Delta v]=(p-1)(p-3)/p^3.

The p=3 value is zero. This is a single-stage identity, not an asymptotic
doubling law.

If a nonzero support has no solutions y+w=u within itself and no opposite
pairs, Q=R=D=0, hence E[Delta v]=-t. Such additive geometry can destroy
the desired growth despite a large fiber collision probability. This is a
conditional example for a law; one must not claim every such law is
reachable from the polynomial recurrence.

A pseudorandom additive-support heuristic would suggest Q roughly
(1-z)^3/p, giving roughly linear v growth and quadratic early z growth.
At k about sqrt(p), the naive acquisition already costs order p modular
work. This heuristic is NOT adopted: the entire point of the audit is to
decide whether the actual dynamics has enough persistent structure to
do better, or whether an exact bound settles a meaningful restricted case.

## Can training work be shared?

A pre-sampled reservoir of L query inputs can keep all current P_j values.
Each update costs O(L), and a training value may be read from a reservoir
entry. But selecting it kills that entire local fiber and globally makes
the selected entry zero. At most L distinct global training entries exist;
one must charge replenishing a fresh entry by evaluating the entire current
circuit. The naive reservoir does not magically turn k independent
training acquisitions into O(k) total work. Propose a real replacement if
it does, including update traffic, cached values and root saturation.

The decisive symbolic question is whether a useful mass amplification can
outpace these paid costs. Do not use a large frozen zero atom as evidence,
fit a depth curve from toy primes, assume independence after a global stop,
or count full gcd N as success. Compare with a paid rho/batch identity
control before claiming even a power-scale improvement.

## A distinct escape from the rational circuit branch

Rational fully split polynomials must survive an arithmetic-complexity
prior-art check. A uniform family of exponentially many rational roots
with polynomial-size constant circuits may imply a constant-free integer
root family through homogenization, not be merely another parametrization.

For P_j=A_j/D_j with a_j=u_j/v_j and D_0=1, a division-free description is

    A_(j+1)=A_j*(v_j A_j-u_j D_j),
    D_(j+1)=v_j D_j^2.

A_j has integer coefficients and leading coefficient D_j. Any rational
root of A_k has denominator dividing D_k. The homogeneous polynomial

    H_k(Y,D_k)=D_k^(2^k)*A_k(Y/D_k)

therefore has all these roots scaled to integers. Homogeneous recurrence

    H_(j+1)(Y,V)=H_j(Y,V)*
                    (v_j H_j(Y,V)-u_j D_j V^(2^j))

can be evaluated using short circuits and repeated squaring of V; D_k
is itself obtained by the short recurrence. Integer constants and
u_j,v_j generation must be included. The exact conversion to the original
Shub-Smale tau model, including any division in coefficient construction,
needs independent audit. No unproved conjecture is a lower bound.

The finite-field adaptive route does not require such rational roots.
The separation of these requirements is useful even if the rational
construction reaches sixteen roots: that finite milestone alone cannot
justify scalable root acquisition.

