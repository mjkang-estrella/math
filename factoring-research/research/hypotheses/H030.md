# H030 — Exact polynomial blocks for the reviewed RootProduct problem

2026-10-08. **Constructive proof-only attempt; no algorithmic improvement accepted.**
Verified full factoring complexity improvement: **NONE**.

## Objective and fixed interface

Try one algebraic realization of H029's reviewed RootProduct using certified
blocks and exact polynomial products. The goal is a complete uniform bit bound
with exponent tau<1/5, ideally 1/6, not a faster scalar root computation.
H029's accepted reduction would then give complete deterministic factoring
exponent max(1/6,tau), including its known small-factor preprocessing.

For every integer M>=4096 set K=ceil(M^(1/3)). For each dyadic band
l_j=2^j, h_j=min(2^(j+1)-1,K), let

    T_j=1+ceil(sqrt(M/[16(K+1)^2*l_j])).
    x(k,t)=ceil(sqrt(4kM))+t,
    y(k,t)=floor(sqrt(x(k,t)^2-4kM)),
    A(k,t,-)=x(k,t)-y(k,t), A(k,t,+)=x(k,t)+y(k,t).

Order j, then k=l_j,...,h_j, then t=0,...,T_j, then minus/plus.
Return the exact product for any inclusive interval of this leaf order
modulo any integer 2<=d<=M. Singletons and whole intervals are included;
empty intervals, if supported, return 1 mod d. M has no factorization,
semiprime, squarefree or primality promise for this product interface.
The number of rows is Theta(M^(1/3)). The descriptor itself is polynomial
in log M; it is not a free table of those integer roots.

## Selected realization

Investigate a block decomposition of the dyadic k ranges with exact rational
polynomial approximants or finite-difference descriptions for the outer and
inner integer roots. The proposed benefit is to represent many consecutive
leaves by a small number of explicitly constructed polynomial products, then
use monic product/remainder trees or an explicitly costed resultant identity.

The central obligation is exactness of both floor/ceiling choices. Small real
approximation error alone does not determine an integer root near a boundary.
Give certified rational bounds, a finite boundary/exception rule, and the full
cost of finding and processing all exceptions. Do not certify a long block by
evaluating every leaf and then omit that work. Account for t ranges and partial
interval boundaries, not just complete k bands. Constant degree is a starting
case; any growing degree, denominator or precision must be explicitly charged.
Choose one concrete realization within this lens, rather than producing a
catalog of unrelated factoring conjectures.

A block with known integer polynomial leaves might permit batched products,
but no such representation or cost is granted. Construct all coefficients
from M, prove its identity, and charge degrees, coefficient bit widths,
translation operations, traffic, storage, and changes of modulus. Generic
interpolation of the entire list and a resultant whose degree equals the
whole candidate count do not pass. Monic remainder operations are allowed
over composite rings; inversions of arbitrary differences or factorials
must be justified or avoided.

## Acceptance, scope and stopping rule

Let C_P be all once-per-M construction and retained-data work and P be the
worst-case cost of one arbitrary interval/modulus query. Prove a uniform bound

    C_P(M,n)+P(M,n) <= M^(tau+o(1))*poly(n), n=bitlength(M),

with explicit workspace, for a fixed tau<1/5. All modulus-specific preparation
belongs in P. Include failures and decoding. A result valid only for d|M,
a hidden factor/order/root oracle, or explicit Theta(M^(1/3)) preprocessing
does not instantiate this interface. The identity A_minus*A_plus=4kM+e
does not authorize reducing away 4kM for nondivisor d, and a zero product
does not supply paid factor recovery by itself.

If a concrete realization fails, identify its first exact obstruction and
the narrow claim actually justified. A failure of this representation is
not a lower bound on RootProduct or factoring. A formal specification,
Taylor estimate, symbolic compression, conditional oracle, or finite timing
fit is not a new algorithm. Primary-check known factorial/product techniques
and Harvey's existing Lehman square-root-speedup discussion before novelty
claims. At most one precise revised proof question may be selected.

## Method and ownership

Read the current H029 report, disposition, full independent review and
H004's accepted reduction. The original H029 report and all source snapshots
are preserved; do not repeat that review. Read project instructions/checkpoint.
Only symbolic derivation, primary-source inspection/archiving and report
authoring are authorized in this round. No finite experiment, sweep, benchmark,
solver implementation, Lean edit, package, recursive delegation, commit,
publication or scheduler. If numerical testing becomes essential, propose
a separately preregisterable protocol rather than executing it.

Exclusive child files: research/findings/H030-root-product-blocks.md and
adjacent H030-block-* source/scratch artifacts. The parent owns hypotheses,
registries, STATE, synthesis and all shared code. Deliver a finite candidate
with proof/full ledger if obtained, otherwise a precisely scoped failed
realization and its decisive missing step. New deductions require independent
review before project acceptance.
