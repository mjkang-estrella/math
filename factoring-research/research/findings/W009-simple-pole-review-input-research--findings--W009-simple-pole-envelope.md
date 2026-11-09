# W009 — a simple pole controls reciprocal acquisition

2026-10-08. Parent derivation, **PROVISIONAL pending independent audit**.
No candidate experiment, code/Lean edit, or improved factoring bound.
This develops the two-anchor reciprocal rule beyond its favorable one-step
subgroup calculation. It also identifies a concrete way to leave the bound.

## The actual first trace law

Fix a legal first pair y,w in F_p^*, y!=w, p odd, and use uniform AFFINE
input. Put A=y+w, c=y*w, Q(b)=(b+A)^2-4c and f=1+chi(c), so f is 0 or 2.
The output counts are n(b)=1+chi(Q(b)) at finite b and n(infinity)=1.
Q has two distinct nonzero geometric roots because c!=0 and
Q(0)=(y-w)^2!=0. Consequently

    z0=2/p, h=1/p, s=(p-3)/p,
    v=(2p-6-f)/p^2, max_b nu(b)<=2/p.

For a nontrivial multiplicative character eta, write eta=omega^a for a
generator omega of all characters, 1<=a<=p-2. Then

    sum_(b!=0) n(b)*eta(b)
      =sum_b omega(b^a * Q(b)^((p-1)/2)).

The polynomial on the right has exactly three distinct geometric zeros
and is not a (p-1)-st power, as its zero at 0 has multiplicity a.
Weil's multiplicative-character bound therefore gives

    |sum_b nu(b)*eta(b)| <= 2/sqrt(p).                 (1)

The source theorem used here is Kowalski, Exponential sums over finite
fields: elementary methods, Theorem 3.1, printed p.31, version 2021-09-14:
https://people.math.ethz.ch/~kowalski/exponential-sums-elementary.pdf#page=33
The parent read its exact hypotheses. The bound uses DISTINCT geometric
zeros, not the potentially large degree after combining characters.
The source is already frozen under W007-component-review-sources/;
this is a new application, not part of that completed review.

## Energy and the second step

For any residual law on F_p^*, define multiplicative convolution
C(c)=sum_(ab=c)nu(a)nu(b), diagonal d(c)=sum_(a^2=c)nu(a)^2,
and Gamma=C-d. Write M(eta)=sum nu(b)eta(b).
Character orthogonality and Parseval give

    E_mul=sum_c C(c)^2=(1/(p-1))*sum_eta |M(eta)|^4,
    sum_eta |M(eta)|^2=(p-1)*v.

If all nontrivial M have magnitude at most delta, then

    s^4/(p-1) <= E_mul
      <= s^4/(p-1)+delta^2*(v-s^2/(p-1)).             (2)

Since C(c)<=v, sum d=v and 0<=Gamma<=C,

    E_mul-2v^2 <= sum Gamma(c)^2 <= E_mul.            (3)

For the trace law, (1)-(3) show sum Gamma^2=1/p+O(1/p^2),
uniformly over all legal first pairs. The removal term
2*s*u3+2*v^2-4*q4 is nonnegative and O(1/p^2), while
ell2=s^2-v=1+O(1/p). For sufficiently large p,

    E[v_next-v | the fixed first map, next local legal pair]
       =1/p+O(1/p^2),
    E[v_next | same] =3/p+O(1/p^2).                  (4)

Thus nearly doubling at the first fold does not continue at the second.
This is a uniform asymptotic statement, not a finite run or an all-depth
conclusion. Small p with ell2=0 have no such conditional expectation.

## Why this extends to every accepted circuit

Represent the current map by reduced polynomials U/V. Initially U=X,V=1.
After every globally legal update

    U_new=(U-yV)*(U-wV), V_new=U*V.

The polynomials remain coprime over each prime, monic, with degrees D,D-1,
where D doubles on an accepted update. At a common zero of U_new,V_new,
the old coprimality and y*w!=0 would give a contradiction. Thus infinity
is always a SIMPLE POLE. This property is stronger than formal degree alone.

For any nontrivial character eta of order d, the sum on the affine inputs
of eta(U/V), with zeros and poles assigned value zero, equals

    sum_x eta(U(x)*V(x)^(d-1)).

The polynomial has at most 2D-1 distinct geometric zeros, and its degree
is d*(D-1)+1. Therefore it cannot be a d-th power. The SAME Weil theorem
gives the history-uniform bound

    |M(eta)| <= (2D-2)/sqrt(p).                       (5)

This argument does not need simple finite zeros or generic parameters.
No character-order or factor information is available to the algorithm;
characters are used only in the analysis.

## A full-tape process that pays for chart rejection

Use a fixed raw-attempt budget k. At each attempt acquire two fresh
uniform residues modulo N=pq and evaluate the current projective map.
If any required chart gcd is nonunit, leave the map unchanged in a
counterfactual full-tape process (including proper-gcd events). Otherwise
perform the reciprocal update. A real implementation may stop at a
proper factor and is coupled to that process until then. A full gcd N
is a charged no-op, not a free resample. No hidden local chart oracle is used.

Conditional on the entire current map modulo N, the two local fresh
sample pairs are independent. A local change at p occurs only when both
charts are legal. If ell_q is q's clean probability, the exact raw drift is

    E[Delta v_p | current map]
       =ell_q * (sum Gamma_p^2 - 2*s_p*u3_p - 2*v_p^2 + 4*q4_p),
    E[Delta m_p | current map]=ell_q*2*(s_p*v_p-u3_p),

where m_p=z_p+h_p. These are NOT survived-history independence claims.
Dropping a nonnegative removal term and using (2), with D<=2^j after
j raw attempts, gives

    E[v_(j+1)] <= (1+delta_j^2)*E[v_j]+1/(p-1),
    E[m_(j+1)] <= E[m_j]+2*E[v_j],
    delta_j=(2^(j+1)-2)/sqrt(p).

With v_0=(p-1)/p^2, m_0=1/p, iteration yields

    E[v_j] <= (j+1)/(p-1) * exp((4^(j+1)-4)/(3p)).

In particular, if 2^k<=sqrt(p), for every j<=k,

    E[v_j] <= 4*(j+1)/(p-1),
    E[m_j] <= 1/p+4*j*(j+1)/(p-1).                  (6)

This bounds the combined root/pole mass under the changed acquisition rule.
It does not say that the two colors have no value, or bound later depths.

For the literal chart protocol (root/pole tests on the two evaluations,
then their affine difference), a proper factor at attempt j implies an
endpoint atom at one prime or equal nonzero finite endpoints there.
The union of the root/pole fibers is absorbing, so intermediate root/pole
tests are also covered by endpoint atom events. The local union bound is
2*m_j+v_j. For t fresh final probes, separate numerator/denominator gcd
success is at most m_k,p+m_k,q per probe. Thus total success is at most
the sum over r in {p,q} of

    2k/r + 2k*(k+1)*(4k-1)/(3*(r-1))
      + t*(1/r+4k*(k+1)/(r-1)),                      (7)

when 2^k<=sqrt(min(p,q)). Cap this upper bound by one.
No actual-work lower bound is claimed by (7); random accepted depths
and no-op costs require a separate ledger. Extra coefficient or
cross-sample tests outside this protocol are not included.

## A constructive escape and its exact resource

The obstruction comes from the simple pole: it excludes perfect-power
degeneracy for EVERY nontrivial multiplicative character. One can remove
it by an explicit different map

    H(z)=((z-y)*(z-w)/z)^e,

evaluated by projective exponentiation in O(log e) operations after
the reciprocal step. This is a real computational change, not a selector.
For a current inner map R with a simple pole, eta(R^e) is identically one
on nonzero finite outputs whenever eta^e is trivial. Their number is
g=gcd(e,p-1). All other characters can still be bounded using the degree
of R, independently of the size of e. Consequently the main energy term
is g*s^4/(p-1), in place of s^4/(p-1).

The possible benefit is a persistent, cheaply imposed power-subgroup
constraint, allowing more mergers per sample. The hidden cost is obtaining
a large g simultaneously with useful CRT separation and preserving
additional structure across the intervening rational fold. Taking powers
without that fold is the familiar group-order compression problem. Merely
choosing a large e supplies no large kernel for an arbitrary unknown p.
Repeated powered folds also lose the simple-pole promise for the inner
map, so the one-step spectral statement is not an all-depth recurrence.

The next constructive question is whether coupled rational updates can
retain several independent, acquired subgroup constraints WITHOUT paying
for unknown p-1 divisors, or whether a different computation can avoid
large useful fiber mass altogether (the scalar product branch). The
displayed powered map alone supplies neither. No experiment is selected
on the strength of formal degree or this conditional resource.

