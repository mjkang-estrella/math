# H025 — An unconditional input-density bound for small residuals

2026-10-08. **Unreviewed parent proof**, using the proposed H024 count lemma.
No experiment or Lean theorem. Verified factoring complexity improvement: **NONE**.

## 1. Finite universe lemma

Fix ell>=2, the first ell primes p_j, and f_j=ceil(j/2).
Let E_bar>=0 and W>=0 be real thresholds fixed for this ell. Put

    U={e in Z^ell: q(e)=sum f_j²e_j²<=E_bar},
    u_e=product p_j^max(e_j,0),
    v_e=product p_j^max(-e_j,0).

Both u_e and v_e are fixed positive integers for each e, independent of N.
For a given e, |u_e-Nv_e|<=W puts N in a closed real interval of length
2W/v_e. The number of integers in it is at most

    floor(2W/v_e)+1 <= floor(2W)+1.                    (1)

The sharper first bound is retained if useful. It includes boundary equality
and W=0. No distribution of u_e modulo v_e is assumed. Restricting to ell-bit
N, namely 2^(ell-1)<=N<2^ell, can only decrease the count.

Consequently the number B_ell(W) of ell-bit N for which there exists *any*
e in U with |u_e-Nv_e|<=W obeys

    B_ell(W)
      <=min(2^(ell-1), sum_{e in U}(floor(2W/v_e)+1))
      <=min(2^(ell-1), |U|*(floor(2W)+1)).             (2)

There is no restriction on how an algorithm chooses e after seeing N.
Even an oracle selecting the best element of U cannot leave this union.
An N-dependent rounded log row and cutoff may restrict U further; they do
not invalidate the upper bound if every allowed e remains inside this fixed
diagonal universe. No computational cost or existence of a useful selector
is assumed in (2).

This proof does not require factorization of N, gcd(u,v)=1, a smoothness
probability or a root-geometry hypothesis. It applies to all integer inputs
in the interval, including special cases. Distinct e need not give disjoint
intervals; union overcount is safe.

## 2. Explicit uniform cutoff for H024's rule

For the N-only rule, ell<=C<10ell and C>=10. Elementary integral bounds give
1/2<log2<1. The certified coefficient errors are at most one, so

    a_1>=C/2-1>=2C/5>0,
    a_1<=C+1<=11ell,
    0<T<=C ell+1<=11 C ell/10.

For r=floor((2T+a_1)/(2a_1)), nearest-integer rounding therefore gives

    |r|<=|T|/a_1+1/2<=11ell/4+1/2<=3ell,
    |a_1 r-T|<=a_1/2.

Hence the exactly computed feasible energy from H024 satisfies

    E_star(N)=r²+(a_1 r-T)²
       <=9ell²+(121/4)ell²=(157/4)ell²<40ell².         (3)

All inequalities hold for every N>1, not merely asymptotically. The bound
uses only ell, not N's factors or digits beyond bit length. Thus every
F_N(e)<=E_star(N) vector lies in the same U with E_bar=40ell².

This does not say that all U elements satisfy the rounded objective, or
that E_star is the actual minimum. Enlarging to U only weakens the bound.

## 3. Population lemma and exceptional fraction

H024 proposes, separately under independent review, the diagonal bound

    |U|<=exp(11 E_bar^(1/3)) for E_bar>=1.             (4)

For E_bar=0 the count is one; for 0<E_bar<1 it is also one. The exact
finite counting lemma (2) stands independently of (4). Subject to acceptance
of (4), set K=11*40^(1/3). Equations (2)–(3) give

    B_ell(W)<=min(2^(ell-1),
                 exp(K ell^(2/3))*(floor(2W)+1)).      (5)

For a uniform ell-bit input the probability is at most the right side divided
by 2^(ell-1). This is an input-density theorem, not random arithmetic inside
a fixed N.

Fix 0<epsilon<1. If |u_e-Nv_e|<=N^(1-epsilon), then
|u_e-Nv_e|<=2^((1-epsilon)ell). Applying (5) with this latter common W gives

    Pr[exists allowed e: |u_e-Nv_e|<=N^(1-epsilon)]
      <=min(1, exp(K ell^(2/3))
                   *[4*2^(-epsilon ell)+2^(1-ell)]) ->0.  (6)

The exponential term is -(epsilon log2)ell+O(ell^(2/3)).
Zero residuals are included in the exceptional event. For any W_ell=exp(o(ell)),
the fraction is instead at most exp(-(log2)ell+o(ell)).
For finite ell the displayed upper bounds can exceed one before clipping;
no useful numerical threshold is claimed.

More generally any fixed-ell universe with the same weights and
E_bar(ell)=o(ell³) has at most exp(o(ell)) elements by (4), and (6) holds with
an o(ell) population term. The bound ceases to imply a vanishing fraction
from energy order ell³ alone; that is a limit of this argument, not a
sufficient threshold for useful supply, or a necessary energy for each N.
A polynomially larger energy still leaves some H021 optimization/counting
ranges polynomial, while its useful distribution remains unresolved.

If an input distribution on ell-bit N has maximum point mass at most
exp(-h ell), (2) instead gives probability at most
|U|*(floor(2W)+1)*exp(-h ell). For a uniform restricted set A_ell, use
denominator |A_ell| directly. No balanced-semiprime or hardness distribution
is asserted here without a separately supplied lower bound on |A_ell|.
Fixed or adversarial exceptional inputs are fully allowed.

## 4. What this resolves and what it does not

The low-energy generator cannot furnish a sublinear-in-N absolute residual
for more than the bounded exceptional input set, irrespective of how cleverly
it selects a vector from this universe. This closes that particular proposed
escape for almost all inputs under the stated input distribution without
assuming random-integer smoothness.

It does not follow that the residuals are nonsmooth, that their parity rows
are useless, or that factoring is hard. Smoothness is compatible with large
residuals. The H024 hypothetical per-attempt exponential-rarity law remains
unproved even after a lower residual-size statement for most inputs.
Nor is this an all-input lower bound: the exceptional set may contain easy
families, hard-looking numbers or useful constructions.

The first-prime list, weights, dimensional bound and common energy universe
are material. N-dependent prime changes or weight permutations may enlarge
the union enormously. A family of K_ell such universes can be union-bounded
with another K_ell factor only if its cardinality, uniform bounds and parameter
selection are explicitly controlled. There is no unrestricted adaptive-base
theorem.

A focused next candidate could increase the energy enough to escape this
cardinality obstruction while providing a costed selector for tiny *actual*
residuals, or exploit a demonstrated useful distribution at larger residual
sizes. A coarse rounded objective and cheap uniform sampler alone supply
neither mechanism. No implementation project is proposed merely to restate
this count.

## 5. Review handoff

Audit the finite interval count, all constants in (3), the fixed-universe
quantifiers, variable-N threshold in (6), exact input-set normalization and
all scope limits. H024's count proof is a separate live review; do not treat
that dependency as independently accepted until its disposition. A review
may accept (2) unconditionally and (5)–(6) conditional on (4).

This report and hypothesis are parent analytic work. No executable, run,
smoothness sample, parameter sweep, package, Lean change, commit or publication
was made. No novelty or full factoring complexity gain is claimed.
