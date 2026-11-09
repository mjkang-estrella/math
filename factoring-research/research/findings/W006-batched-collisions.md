# W006 paid collision detector and a concentration threshold

2026-10-08. Parent derivation submitted for independent review. No new best
factoring bound or completed implementation. This is a concrete computation
bypassing useful integral quaternion twin generation.

## A modular pair detector

Work in S_N=(Z/NZ)[i], i^2=-1, with norm-one group H_N. The accepted W005
sampler supplies a uniform h or a paid early factor/exhaustion. No quaternion
of exact integer norm N is needed here. Take two independent lists x_i,y_j
of K accepted group samples, possibly transformed by the same fixed,
root-sign-equivariant map F. Construct the monic polynomial

    P(X)=product_i (X-x_i) over S_N,

and evaluate P at all y_j by monic product/remainder trees. Inspect
g_j=gcd(N,Norm(P(y_j))) in fixed order. A proper g_j is a factor.
At the first full gcd, scan all K leaves Norm(y_j-x_i), returning a proper
gcd if present, otherwise end this trial as a failure. This scan costs O(K)
and is performed at most once. It avoids assuming a free collision reporter.
A sharper success proof may require tree descent or handling an early
globally duplicated sample; that issue is explicitly part of validation.

For an odd prime p, H_p has m_p=p-(-1|p) elements. The exact local property is

    Norm(x-y)=0 mod p  iff  x=y in S_p, for x,y in H_p.

If p=3 mod 4, S_p is a field. If p=1 mod 4, it is F_p x F_p and norm-one
elements have form (t,t^(-1)); zero norm of a difference forces t=s and
therefore both components equal. Thus the norm of P(y) detects a local
collision with at least one x_i. This does not require factoring N, finding
a square root of -1 modulo N, or constructing the split representation.
The proof uses those local models only for analysis.

All polynomials used for division are monic, so product/remainder computation
does not require arbitrary coefficient inverses in this ring. Polynomial
multiplication reduces to a constant number of integer-coefficient convolutions.
Nonnegative residues and Kronecker radix with O(log N+log K) bits per digit
give integer products of O(K(log N+log K)) bits. With fast integer arithmetic
and monic Newton division, the intended cost is K*poly(log N+log K) bit work
and comparable space, plus sample costs. A schoolbook prototype instead costs
quadratic K; do not mislabel its timing as the fast bound. Primary algorithmic
references and all ring hypotheses must be checked independently.

This recovers a known-scale birthday control: uniform samples at a smallest
factor p need K on the order of sqrt(p), giving N^(1/4)*polylog N for balanced
semiprimes, NOT a new factoring bound. An N-only doubling schedule can pay
unknown p; prime powers and complete factor recursion require separate handling.
This note claims no complete general bound until the success/stopping audit.

## What distribution improvement would actually pay

For a fixed deterministic map on H_p, let b_z be its fiber sizes, excluding
failed inputs only with explicit accounting. If all inputs survive, the
output collision probability for two independent samples is

    c_p = sum_z b_z^2 / m_p^2.

The useful quantity is this second moment, not just image cardinality.
If F is scalar-sign-equivariant, output atom masses are paired at z and -z,
so every atom is at most 1/2 and c_p<=1/2. This remains true after conditioning
on a sign-invariant survival event. For a squarefree semiprime and a fixed
local algebraic schedule, conditioning on survival at both primes preserves
independence of the two local output distributions.

For one pair the exact proper-collision probability is

    c_p*(1-c_q) + c_q*(1-c_p).

This supplies a separation guarantee absent from arbitrary concentrated
distributions: collapse to a single global value cannot masquerade as useful
compression under the sign symmetry.

A proposed birthday proof uses Z=sum_{i,j} 1[x_i=y_j mod p but not mod q].
Its mean is K^2*c_p*(1-c_q). If K is on the order of c_p^(-1/2), this is
bounded below by a positive constant. Coincident-edge terms use the mean;
pairs sharing one endpoint are bounded by sum_z mu_p(z)^3<=c_p^(3/2);
disjoint edges are independent. Hence a second-moment inequality should
give constant probability that a proper local collision exists, for arbitrary
output laws with the stated symmetry and independent CRT components. The
algorithm's chosen recovery/stopping rule must still find such a collision:
existence alone is not a full factoring proof.

If a k-step map costs C_k ring operations per input and local survival
probabilities are sigma_p,sigma_q, paid independent accepted samples cost
on the scale C_k/(sigma_p*sigma_q), ignoring any helpful early factors.
The proposed full trial work is therefore

    [C_k/(sigma_p*sigma_q)] / sqrt(c_p) * poly(log N),

with corresponding accepted-sample tree costs. Against uniform birthday,
the required strict gain is approximately

    m_p*c_p > [C_k/(sigma_p*sigma_q)]^2,

up to constants and logarithms. For C_k proportional to k, a compression
factor only k does not pay; it must beat k^2 after survival costs.
This is a conditional accounting threshold, not a success model for F_a.

The W006 rational-map screen already saves every transition and graph. Its
records can later determine fiber second moments at fixed depths without
rerunning the candidate. Such an analysis would be explicitly post hoc and
would not change its frozen primary criterion. No extra experiment is
authorized by this note.

## Different constructive questions exposed

1. Can a nonmonomial, cheaply iterated map amplify collision energy beyond
   squared evaluation cost while preserving appreciable survival?
2. Can a whole batch share the map evaluations enough to reduce C_k per sample?
   For rational degree three, evaluating one step on K points can use batch
   inversion, but repeated k steps still require kK state transitions unless
   an explicit further composition method is provided.
3. Do the map's fixed-point basins give direct extraction sooner than the
   birthday path? These are different event laws and must be compared with
   actual costs, not combined as independent successes.

The reflection obstruction caused by enforcing an exact integer shell does
not apply to this modular group detector. The remaining bottleneck is paid
concentration or shared evaluation, and this construction specifies how an
improvement there would be consumed.

