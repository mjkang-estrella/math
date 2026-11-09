# W007 — compressed algebraic norms with distinct roots

2026-10-08. Parent-led fresh branch. PROVISIONAL; no factoring improvement,
candidate execution, new benchmark, or Lean theorem. The question is whether
a norm polynomial with exponentially many DISTINCT useful local roots can be
constructed and evaluated with only polynomially many bit operations.

This replaces relation collection and random group collision generation with
a direct gcd(N,P(x)) test for a succinctly specified polynomial. Both useful
root coverage and the construction of P are charged. A degree bound alone
is never a lower bound on root count.

## Candidate A: anti-commuting block norms — explicit rejection

Let A_1=[[0,t_1],[t_1,0]], and recursively

    A_(j+1) = [[A_j,t_(j+1) I],[t_(j+1) I,-A_j]].

The dimension is 2^j but A_j^2=S_j I, S_j=sum_(i<=j) t_i^2, and trace A_j=0.
Over characteristic zero,

    det(X I-A_j)=(X^2-S_j)^(2^(j-1)).

As an integer polynomial identity it survives reduction modulo any N.
Compute S_j and the displayed power by modular arithmetic without building
the matrix. This really eliminates an exponential determinant, but it leaves
at most two distinct roots over each odd prime. Singular reductions may have
one root, not more. A proper gcd of the huge determinant is already explained
by gcd(X^2-S_j,N); repeated-prime valuations need their own capped treatment.
The exponential degree is only multiplicity. This exact computation therefore
does not provide a root-density gain.

A commuting tensor sum instead has roots sum_i epsilon_i t_i. Repeated or
few distinct weights can again create large multiplicities. Superincreasing
weights give many distinct roots but the obvious norm evaluation enumerates
them; the binary-weight example becomes a large arithmetic-progression product.
The old H029/H030 product gates are not waived by calling that product a norm.

## Candidate B: a concrete nested split polynomial — selected

Set P_0(X)=X and define

    P_(j+1)(X)=P_j(X)*(P_j(X)-a_j).

A supplied list a_0,...,a_(j-1) gives an actual O(j)-operation modular evaluator
for a monic polynomial of degree 2^j. It is also the norm of X-T in the
algebra (Z/NZ)[T]/P_j(T), but no dense basis or general norm routine is used.
This particular recurrence performs the evaluation.

The adaptive construction chooses a_j=P_j(r_j) for an explicitly obtained
rational r_j, so the new polynomial retains old roots and adds that fiber.
Evaluating all training values naively costs O(j^2) modular operations.
There are no hidden p,q or local orders in this program. Every denominator
is gcd-tested before inversion; a proper gcd is an early factor, a full gcd
is an exhausted parameter attempt. Neither raw rational height nor formal
degree is automatically the cost: an explicitly short modular arithmetic
circuit can avoid expanding large integers. Its circuit construction,
constants, denominator branches and reduced operand widths still must be paid.

An actual three-stage split construction is

    a_0=1,  a_1=2,  a_2=-504/625,
    P_1=X(X-1),
    P_2=X(X-1)(X-2)(X+1),
    P_3=P_2*(P_2+504/625).

P_2(-4/5)=-504/625, and

    P_2+504/625
      =(X+4/5)(X-9/5)(X+2/5)(X-7/5).

Thus P_3 has eight distinct rational roots
{-1,0,1,2,-4/5,9/5,-2/5,7/5}. For primes p>13 their denominators are units and
their residues remain distinct (all pairwise numerator differences have
absolute value at most 15). This gives exactly eight roots modulo those primes.
It is a concrete finite construction, not evidence of an all-depth generator.

By contrast, the obvious r_2=3 gives a_2=24 and

    P_2-24=(X-3)(X+2)(X^2-X+4).

Only six rational roots of P_3 are then automatic; the remaining quadratic
has discriminant -15. This explicitly refutes automatic rational root doubling.

For an odd squarefree N=pq, conditional on a fixed eligible polynomial and
a uniform x modulo N, if its local zero fractions are z_p,z_q, then the
proper-gcd probability is z_p(1-z_q)+z_q(1-z_p). A full gcd is not a factor.
At the displayed fixed degree this is only a constant number of ordinary
root tests. A disruptive consequence would require a PAID scalable construction
with many distinct roots modulo unknown input primes and a separating
success law. No such construction has been established.

## Exact next gate: obtaining the fourth fully split fiber

Keep this P_3 fixed. To retain sixteen distinct rational roots via the same
recurrence, obtain a nonzero rational a_3 such that P_3(X)-a_3 splits into
eight distinct rational roots. Its roots are disjoint from P_3(X)=0 when
a_3 is nonzero. The known a_3=0 is a duplicate, not progress.

The degree-eight cover P_3(X)->T has the following proposed finite branch
values, obtained at the three levels' critical points:

    b_2=-63504/390625,
    b_1=121/625,
    b_0=123201/160000.

They are distinct. Proposed inertia orders are 2,2,2 at these values and
8 at infinity. A plausible full geometric Galois group is the three-level
binary wreath product, of order 128. IF that group and ramification audit
is correct, its Galois closure has

    2g-2 = 128*(-2+3*(1-1/2)+(1-1/8))=48,  hence g=25.

This genus is NOT yet accepted. The reviewer must prove the actual group,
constant field, ramification and relation between completely split rational
fibers and rational points, or correct the proposed conclusion. A positive
genus alone is not an algorithmic lower bound, and genus 25 does not prove
there is no additional split fiber. It would invalidate a presumed rational
one-parameter parametrization of the fixed cover's full splitting data.
It does not exclude varying earlier coefficients or working only over F_p.

Why this is a decisive cheap gate: degree four admits a concrete rational
circle construction for a completely split fiber; blindly extending that
parametrization to degree eight may fail for a specific geometric reason.
Do not launch an unbounded rational-point search or assume a point oracle.
A finite symbolic group/branch audit is selected first.

## Candidate C: explicitly paid adaptive fiber absorption

This uses the same evaluator but a different acquisition rule: r_j is a
fresh uniform residue modulo N and a_j=P_j(r_j). Over one prime, fix the
current P_j and let mu(y)=Pr_x[P_j(x)=y], z=mu(0), c=sum_y mu(y)^2.
The fresh a_j has law mu. For a fixed a, the new zero fraction is

    z'=z+mu(a)-1_(a=0)*z,

and therefore E[z'-z | P_j]=c-z^2.
This is an actual size-biased fiber addition, not an assumed concentration
oracle. For the collision probability of the full next distribution, the
quadratic identity y(y-a)=w(w-a) iff y=w or y+w=a suggests exactly

    c'(a)=c+sum_y mu(y)*mu(a-y)-mu(a/2)^2.

These identities need independent audit, especially repeated zeros and the
fixed-field characteristic assumptions. They expose both opportunity and cost:
if fibers grew rapidly, the procedure would absorb useful local inputs;
fresh training evaluations already cost quadratic depth, and globally planted
roots can give full gcds at both primes. No independence after arbitrary
global stopping, no exponential growth model and no complete factor bound
is claimed. A constant fresh parameter unrelated to P_j would have a different
law and must not be substituted.

Symbolic validation only for W007's first task. No experiment is authorized.
The selected next action is the fixed degree-eight splitting gate and the
exact adaptive laws, then choose whether any bounded run could change the
disposition. Keep W006's corrected batch detector as a paid known-scale
control, not a claimed discovery.

