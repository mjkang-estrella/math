# W010 — batch extraction from a trained map

Parent acceptance and scope corrections: [disposition](W010-batch-extraction-disposition.md).

2026-10-08. Parent constructive mechanism and probability derivation,
PROVISIONAL pending audit. No candidate runs or new factoring bound.
The computational idea uses ordinary polynomial product trees; no novelty
is claimed for those primitives. The new role is a fully priced detector
for the acquired cubic law, bypassing further relation collection or a
separately pinned root. This is separate from the W008 implicit four-list
product question and does not solve it.

## Executable detector, with global collisions handled

Freeze a current polynomial circuit P modulo distinct primes N=pq. Generate
2M fresh independent uniform inputs and evaluate their outputs modulo N.
Keep these conceptually as two lists of M for the probability proof, but
sort their union as canonical residues and remove EXACT modulo-N duplicates.
Let the resulting distinct values be c_1,...,c_L, L<=2M. Define

    F(T)=product_(i<=L)(T-c_i).

Build its monic product tree, formally differentiate, and multipoint-evaluate
F'(c_i) over Z/NZ. No factorial division or field assumption is needed.
For each i, gcd(F'(c_i),N) tests the product of every c_i-c_j, j!=i.
A proper gcd is a factor. If a full gcd occurs, recover a proper leaf by
splitting the other-factor product. Every leaf difference has gcd 1,p,or q,
never N, because exact global duplicates were removed. Thus a nonunit branch
cannot terminate at a full-gcd leaf. There is no assertion that a single
arbitrary branch works BEFORE this duplicate removal.

One concrete recovery implementation uses the sibling nodes on c_i's
root-to-leaf product-tree path: their polynomials partition all factors
except T-c_i. Evaluate these sibling polynomials at c_i and select a nonunit
one. If its gcd is N, recurse on its children. At each split, a unit child
can be discarded; a proper child immediately solves; a full child can be
followed. The sum of the evaluated polynomial degrees is O(L), including
finding the first sibling branch. This recovery is charged only after one
nonunit derivative value is detected, and stops at a proper factor.

Removing duplicate values preserves every useful pair: a pair with proper
gcd has different residues and both survive. It may remove useless full-gcd
pairs; that is precisely why it is needed. L<2 is a paid failure.

With a length-k sequential P circuit, fresh evaluation takes O(M(k+1))
modular operations. Tree construction and multipoint evaluation cost
quasilinear polynomial arithmetic with logarithmic tree overhead; fast
integer polynomial multiplication supplies the corresponding polylog factors
in M and log N. Include sorting, random bits, derivative, all gcds and O(M)
recovery. State the bit bound as

    (M(k+1)+M*polylog(M,N))*polylog(N),

or soft-O(M(k+1)*poly(log N)) when M<=N and the multiplication convention
is explicit. This is not an O(1) unbounded-integer operation model. An
implementation with schoolbook multiplication has a different cost.

## Exact first and second moments for useful pairs

At this fixed map, let mu_p,mu_q be the local output laws. Fresh outputs
have product law mu_p times mu_q by CRT. Define

    w_r=sum_a mu_r(a)^2,   t_r=sum_a mu_r(a)^3,  r=p,q,
    rho=w_p+w_q-2w_p*w_q.

For two independent outputs, rho is exactly the probability that their
difference has a proper gcd: equality at exactly one prime. Zero values
and their mass are included in w; this is not residual v alone.
Let Y count useful pairs across the original two independent M-lists.
Then E Y=M^2 rho. For a sampled output A, the conditional probability
of a useful partner is

    d(A)=mu_p(A_p)+mu_q(A_q)-2mu_p(A_p)*mu_q(A_q).

Writing kappa=E[d(A)^2], expansion gives

    kappa=t_p+t_q+4t_p*t_q+2w_p*w_q
          -4t_p*w_q-4w_p*t_q.                                 (1)

Disjoint list-pair events are independent. Two distinct events sharing one
endpoint have joint probability kappa. Hence exactly

    E Y^2=M^2 rho + 2M^2(M-1) kappa + M^2(M-1)^2 rho^2.          (2)

Paley–Zygmund at zero yields

    Pr(Y>0)>=M^2 rho^2/[rho+2(M-1)kappa+(M-1)^2 rho^2].          (3)

The detector tests at least these cross pairs, so it succeeds whenever Y>0.
A nonunit derivative is sufficient after exact duplicate handling.
No independence between all M^2 pairs is assumed.

## A sufficient birthday bound without flat weights

Suppose w_p,w_q<=1/2. Let T=w_p+w_q<=1. Then rho>=T/2.
Since t_r<=w_r^(3/2), and d<=mu_p+mu_q,

    kappa<=t_p+t_q+2w_p*w_q
          <=T^(3/2)+T^2/2
          <=(3/2)*T^(3/2) < 5*rho^(3/2).                       (4)

For any M>=rho^(-1/2), divide (2) by (E Y)^2. The diagonal term is at
most 1, the shared-endpoint term at most 10, and the disjoint term at
most 1. Thus

    Pr(detector finds a factor)>=1/12.                         (5)

No local L-infinity or uniform-support promise is added. The restriction
w_p,w_q<=1/2 is real: two almost globally constant output laws can have
tiny useful-pair probability arising from rare outliers, for which naive
birthday reasoning is inadequate. The exact (3) remains available there.
At a fixed map, a dyadic M schedule avoids receiving rho or the factors as
advice. It can reach the needed width at geometric total setup cost, with
fresh randomness at each width. This is a conditional detector guarantee;
acquiring the favorable map and any failed attempts still cost work.

## Quantitative target for cubic training

For W010, w_r=m_r^2+v_r. In the moderate-collision regime, rho is comparable
to w_p+w_q. At a fixed trained state the detector's leading evaluation cost
is roughly k/sqrt(rho), plus polynomial arithmetic. With a training cost
A_k, a candidate complete improvement must pay

    A_k + soft-O((k+1)/sqrt(rho)),

and include the probability of actually acquiring such a state. A mean
value of v across training histories does not supply that probability.
If the intended comparison is a sqrt(p) collision control, then for k>=1
one necessary scale target for this evaluator is

    rho substantially greater than k^2/p,
    A_k substantially less than sqrt(p),                      (6)

up to the explicitly retained bit/log factors and equal input assumptions.
This is a threshold comparison, not a lower bound on every implementation.
If useful collision mass grows only like k/p, batching costs roughly
sqrt(p*k), so mere linear growth loses to the identity-map control.
Even hypothetical k^2/p growth only cancels the increased probe depth at
this crude arithmetic scale. Growth faster than quadratic, a cheaper
trained evaluator, or asymmetric extraction outside this collision detector
would be required for the hoped-for exponent change.

The parent's norm-envelope derivation under separate review proposes
O(k/p) mean residual/root mass through 81^k<=min(p,q). If accepted, it
constrains early-depth claims; it does not close the deeper-depth branch
or supply an actual-work lower bound. The Jacobi selector is likewise a
separate detector modification, not a free improvement to (5).

## Decisive next test

Audit duplicate-safe extraction and (1)-(5). Then ask whether a concrete
reachable cubic family can meet (6) with a controlled acquisition tail.
Do not run a depth sweep merely because an expectation is positive. If
no such family or different evaluator emerges, retain the batch detector
as a matched control and pursue a different acquisition mechanism.

## Parent scheduling refinement after D was delegated

This paragraph is additional parent work, not in D's frozen supplied brief.
One batch per successively doubled width does not automatically yield
expected work proportional to the first sufficient width: its failure tail
can be too large. A concrete repair is sixteen independent batches per
dyadic width, with P fixed throughout. At any sufficient width, (5) gives
probability of failing all sixteen at most f=(11/12)^16<1/2. The expected
width cost beyond the first sufficient width is bounded by the geometric
series sum_(h>=0) 2^h f^h. Polynomial log factors do not spoil convergence.
Cap the width at the first power of two at least N and repeat there if
necessary; this uses N only and keeps log M=O(log N). Under w_p,w_q<=1/2,
rho>0 and the cap is certainly sufficient. The early widths have geometric
total cost too. This would justify the conditional expected detector cost
at the first sufficient width, once (5) and the implementation are accepted.
It still says nothing about the cost/probability of acquiring that fixed map.
