# W006 — power-compressing the blinded norm sampler

Date: 2026-10-08. PROVISIONAL parent mechanism. No experiment, novelty claim,
or new best factoring bound. This is independent of the running coefficient
and reflection validations.

## Actual changed computation

The accepted W005 sampler draws h uniformly in H={c+ie:c^2+e^2=1 mod N}
and outputs x*(1+2i)*h, where x^2=R and only the norm certificate enters
the inner procedure. Replace h by h^E, computed by binary powering in the
quadratic algebra. Choose E before this fresh h, using N,R or earlier
permitted independent transcripts.

This shares exponentially many repetitions of a group action through
O(log E) modular multiplications. It can compress the certificate population
by the kernel size of the powering map. The hidden cost is log E itself;
E=lcm(odd integers <=B) has log E=O(B), not O(log B).
A smaller population alone supplies no useful packet law.

## Proposed independence condition

For every odd positive E, H^E contains every scalar r with r^2=1 mod N:
r^E=r. Uniform h pushes forward to uniform H^E. Multiplication by each such
r preserves H^E and its uniform law. Consequently x*(1+2i)*h^E has the
same distribution for all roots x of R, exactly the property needed by
the accepted root-to-factor wrapper. Repeated prime powers are included.
It need not be uniform on the full norm circle.

There is a useful even extension specific to this algebra: E=2E_odd works
as well. For any scalar r^2=1, define

    z=(1+r)/2 + i*(1-r)/2.

Then Norm(z)=1 and z^2=r. Thus z^(2E_odd)=r. Again the full root-sign
subgroup is contained in the image. This proof uses r only to establish
image invariance; the sampler never needs to compute all root signs.

Do not generalize to all even exponents. For example, modulo a prime with
v_2(p-(-1|p))=2, the fourth-power image has odd order and omits -1.
The W005 proof cannot automatically be reused for E divisible by 4.

More generally a deterministic map F:H->H with
F(rh)=r F(h) for every scalar r^2=1 has a root-sign-invariant pushforward
of uniform h, even when its output fibers are unequal. The form
F(h)=h*G(h^2), with G defined on squares and valued in H, satisfies this
identity. It permits explicitly charged adaptive operations based on h^2;
it does not permit arbitrary stopping predicates on h or leaking its tape.

## What an actual direct-root control buys

For this control only, use the seed x rather than x*(1+2i), so the norm
certificate is u+iv=x*h^E with norm R. Compute gcd(v,N). A proper gcd is
a factor; a full gcd gives u^2=R and allows the outer root comparison.
For a prime p, H_p is cyclic of order m_p=p-(-1|p). Uniform h^E is uniform
on a subgroup of size

    h_p=m_p/gcd(E,m_p).

For odd E or twice odd E the subgroup contains +1 and -1. Therefore the
local v=0 event has exact probability 2/h_p. Independent local group
samples give independent events across different primes. For squarefree
N=pq with a_p=2/h_p and a_q=2/h_q, a direct proper gcd has probability

    a_p*(1-a_q)+a_q*(1-a_p).

If both coordinates vanish, the remaining scalar signs are uniform and
independent; the outer comparison splits with probability 1/2. Total
success for this control is therefore

    a_p+a_q-(3/2)*a_p*a_q.

All early gcds in generating the uniform h and all caps must be included
for a complete sampler law; this displayed probability is conditional on
the uniform H certificate. For repeated prime powers the full order also
has a p^(e-1) factor; do not silently transfer the squarefree law.

This is a familiar p-1/p+1 group-order mechanism in norm-one coordinates.
The factor test even cancels x from gcd(v,N); its direct branch is not a
new hidden-root attack. Its purpose here is to price and verify a concrete
compression operation. It becomes favorable only when E removes enough
of the actual group orders, and acquiring that exponent is the known cost.

## Remaining constructive use

The norm-5R version can be fed into the existing quadratic-field selector
while retaining root-choice independence. It gives a genuinely different
certificate law with a cheap evaluator, unlike the invalid global-x
compatible-field branches. A claimed field-packet gain must now prove its
useful yield under H^E, including the cost of E, exponentiation, all rejected
fields and final recovery. No such gain follows from group compression.

A promising next computation would use a specific equivariant F=h*G(h^2)
to increase a verifiable packet event without enumerating its preimages.
The generator G and its cost must be supplied first. Generic smooth-order
powering is the paid control; a renamed group-order or square-root oracle
does not improve it.
