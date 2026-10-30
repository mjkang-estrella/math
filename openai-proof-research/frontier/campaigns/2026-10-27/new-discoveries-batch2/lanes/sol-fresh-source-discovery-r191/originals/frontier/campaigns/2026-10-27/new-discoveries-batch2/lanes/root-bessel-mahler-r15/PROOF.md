# A direct all-p proof candidate for the Bessel–Mahler asymptotic

28 October 2026. Ordinary proof candidate, **credit 0**. No literal Lean
endpoint, independent review, manuscript, acceptance or priority claim yet.
Classical Laplace estimates, the beta integral and Stirling are uncredited.

## Exact target

Mastrantonis, arXiv:2411.10439v2 (26 November 2024), Conjecture 5.2,
equivalently Conjecture 5.1; related MathDB 365832. For each fixed real p>0,
as the positive integer n tends to infinity, put

    F_(n,p) = integral_0^infinity
       r^(n+n/(2p)-1) / I_(n/2)(r)^(1/p) dr.

The source conjectures

    F_(n,p) = [ n^(1+1/(2p)) e^(-1-1/(2p))
                sqrt(p(1+p)^(1+1/p)) ]^n exp(o(n)).

The source proves p=1; that case receives no new credit. The claim below
covers every fixed p>0, with the stronger logarithmic error O_p(log n).

## 1. Exact integral representation

Take n>=3, d=n-1>=2, and define

    c_n = [ integral_-1^1 (1-t^2)^(d/2) dt ]^(-1),
    Z_n(r) = c_n integral_-1^1 exp(rt) (1-t^2)^(d/2) dt.

The standard beta-integral expansion of the genuine Bessel series gives,
for r>0,

    Z_n(r)=Gamma(n/2+1)(2/r)^(n/2) I_(n/2)(r).                 (1)

This is the same representation as the source's Claim 2.23. It follows
directly by integrating the absolutely convergent exponential series and
evaluating its even moments using the beta integral; no asymptotic formula
for Bessel functions is used. In particular all quantities are positive.
Also

    1/2 <= c_n <= d.                                         (2)

Indeed the normalizing integral is at most 2. On |t|<=1/d, Bernoulli's
inequality with exponent d/2>=1 gives
(1-t^2)^(d/2)>=(1-1/d^2)^(d/2)>=1-1/(2d)>=1/2,
so that integral is at least 1/d.

## 2. Uniform elementary bounds, including unbounded r

For u>=0, let

    psi(u)=max_(-1<t<1) [ut+(1/2)log(1-t^2)].

At u=0 the maximizer is t(0)=0. At u>0 the unique maximizer t=t(u) lies
in (0,1), satisfies u=t/(1-t^2), and equals

    t(u)=2u/(1+sqrt(1+4u^2)).

We claim the following **global** estimates for every d>=2 and u>=0:

    c_n/[4d(1+u)] exp(d psi(u))
       <= Z_n(d u) <= 2c_n exp(d psi(u)).                    (3)

The upper bound is the maximum-integrand bound over an interval of length 2.
For the lower bound integrate only over

    t(u) <= t <= t(u)+(1-t(u))/d.

Throughout this interval, ut>=u t(u), while

    1-t^2 >= (1-t(u)^2)(1-1/d).

Thus the integrand is at least exp(d psi(u)) (1-1/d)^(d/2),
and this last factor is >=1/2 by Bernoulli's inequality. The interval's
length is (1-t(u))/d. Finally

    1-t(u)>=1/(1+2u)>=1/[2(1+u)],

since sqrt(1+4u^2)>=2u. This proves (3). The u=0 case is included.
These uniform estimates are what justify the subsequent tail passage;
no local Bessel approximation is extrapolated to an infinite integration
interval.

## 3. One-dimensional maximum and an integrable tail bound

For fixed p>0 define, for u>0,

    H_p(u)=log u-psi(u)/p.

Differentiating the explicit maximizer formula (or cancelling the t'(u)
term at the maximizer) gives psi'(u)=t(u). Hence

    H_p'(u)=1/u-t(u)/p.

The product u t(u)=t(u)^2/(1-t(u)^2) increases strictly from 0 to infinity.
Consequently H_p has a unique global maximum at

    u_p=sqrt(p(1+p)), t(u_p)=sqrt(p/(1+p)).

There psi(u_p)=p-(1/2)log(1+p), and the maximum value is

    h_p=(1/2)log p+(1/2)(1+1/p)log(1+p)-1.                  (4)

The following weighted integral is finite:

    C_p=integral_0^infinity (1+u)^(1/p) exp(H_p(u)) du <infinity. (5)

Near 0 use psi>=0 to bound exp(H_p)<=u. For u>=1 evaluate the
supremum defining psi at t=1/2, obtaining
psi(u)>=u/2+(1/2)log(3/4). The integrand in (5) is therefore bounded
by a fixed power of u times exp(-u/(2p)), which is integrable. These
arguments also establish finiteness of the integrals below.

For d>=2, let J_d(w)=integral_0^infinity w(u)exp(dH_p(u))du.
The global maximum and (5) give

    J_d((1+u)^(1/p)) <= exp((d-1)h_p) C_p.                  (6)

For a matching lower bound, choose L_p>=0 bounding |H_p'| on the compact
interval [u_p,u_p+1]. On [u_p,u_p+1/d] the mean value theorem gives
H_p>=h_p-L_p/d. Thus

    J_d(1) >= exp(dh_p-L_p)/d.                             (7)

In particular both logarithmic integrals equal d h_p+O_p(log d).
This is a self-contained elementary Laplace estimate, not an appeal to an
unstated uniform version of a saddle-point theorem.

## 4. Assemble the literal Bessel integral

From (1), followed by r=d u,

    F_(n,p)=[Gamma(n/2+1) 2^(n/2)]^(1/p)
              d^n integral_0^infinity u^(n-1) Z_n(d u)^(-1/p)du.

Write A_(n,p)=[Gamma(n/2+1) 2^(n/2)]^(1/p)d^n.
Since n-1=d, (3) gives the exact sandwich

    A_(n,p) (2c_n)^(-1/p) J_d(1)
       <= F_(n,p)
       <= A_(n,p) (4d/c_n)^(1/p) J_d((1+u)^(1/p)).           (8)

Combining (2), (6) and (7) proves

    log F_(n,p)
       = (1/p)log Gamma(n/2+1)+(n/(2p))log 2
           +n log(n-1)+(n-1)h_p+O_p(log n).                (9)

Stirling's formula, log Gamma(n/2+1)
=(n/2)(log(n/2)-1)+O(log n), reduces this to

    log F_(n,p)
       = n[(1+1/(2p))log n-1/(2p)+h_p]+O_p(log n).

Inserting (4) yields the exact exponent in Conjecture 5.2, with
O_p(log n)=o(n). This also proves Conjecture 5.1 by the source's exact
ball-volume/Bessel identity and Stirling. No assertion about any Mahler
minimizer, functional Santaló theorem, or p=1 novelty is made.

## Scope, dependencies and objections

- The quantifier is every **fixed** p>0. No uniform claim when p depends on n.
- n>=3 is sufficient for the asymptotic assertion and avoids endpoint
  conventions. This is not a dimension restriction on the conjectured limit.
- Positivity and finiteness of the actual improper integral follow from (8).
- The only special-function input is the exact beta/Bessel identity and
  Stirling, both classical and uncredited. The proof does not rely on the
  source's functional Santaló theorem or its Bessel-K comparison.
- The source's announced follow-up “Asymptotics of the extremizers” is an
  important prior-art lead, not cleared by a negative title search.
- Strongest eligibility objection: classical Laplace asymptotics plus a
  standard Bessel integral representation may make this a routine corollary
  of an existing uniform Bessel asymptotic theorem. A full explicit bridge
  from a published theorem would exclude credit. An independent review is
  required; no novelty or substantive PASS is claimed here.
- No Lean certificate exists yet. A conditional Laplace lemma alone would
  not meet the full-source formal gate: the genuine I-series integral bridge,
  all tail/integrability claims and the exact asymptotic limit must be proved.
