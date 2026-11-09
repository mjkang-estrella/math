# W020 parent construction: amortize one interval across many group elements

2026-10-08 local. New concrete primitive, PROVISIONAL pending independent
correctness/cost/prior-art audit. No complete factoring improvement claimed.

The W019-B review identifies repeated annihilator searches as a remaining
cost. Rather than demanding that the first element have unusually large
order, use each small-order result to refine a shared integer divisibility
constraint. This handles both branches by computation.

## Contract

Input: a finite group G with effective equality, multiplication and inverse;
K supplied elements g_i; integers 1<=Hlo<=Hhi. Promise: there is a fixed
positive integer h in [Hlo,Hhi] which annihilates every supplied element.
The order |G| is one valid h. The algorithm does not know h or any factorization.
Let W=Hhi-Hlo. Group operations are charged separately from their bit costs.
Abelianness is not needed for this primitive because it powers each element
separately; downstream class-group torsion extraction does require it.

Output either:

* the certified unique common-annihilator integer h in the narrowed interval;
  more precisely, uniqueness among multiples of the retained divisor L
  which annihilate the queried element, hence uniqueness for all integers
  satisfying the full input promise; or
* L dividing every h consistent with the promise, such that g_i^L=1 for
  every processed/supplied element.

The second output need not equal |G| or h, even if the supplied elements
generate G: a noncyclic group can have exponent less than its cardinality.

## Algorithm with explicit no-growth and growth branches

Maintain L=1. It will divide every common-annihilator integer h in the
original interval. At each stage compute

    a=ceil(Hlo/L), z=floor(Hhi/L), w=z-a.

The promise and invariant imply a<=z. If a=z, output L*a. It is the unique
multiple of L in the interval and equals every promised h. No search needed.

For the next supplied element g compute beta=g^L. If beta=1, mark this
element done with the current L and continue. This branch costs one binary
powering and equality, NOT a bounded search through the whole interval.

Otherwise w>=1. Use exact bounded baby-step/giant-step order search with
radius w. Its output is either r=ord(beta)<=w, or the decision ord(beta)>w.
For the small-order result r>=2 (beta was explicitly not 1), set

    L <- L*r.                                         (A1)

This annihilates g and preserves all previous annihilations. Mark it done.
For the large-order result, find a k in [a,z] with beta^k=1 by ordinary
interval BSGS. It exists because beta^(h/L)=g^h=1. Since ord(beta)>z-a,
there can be at most one such k. Output L*k, which therefore equals every
common-annihilator integer satisfying the input promise.

If all K elements are processed without returning a unique integer, output L.
L=1 and K=0 are valid boundary cases. A singleton initial interval returns
its value; the correctness statement is conditional on the input promise,
not a method to certify a false interval by fiat. One may verify all g_i^h
before emitting a claimed common annihilator, paying O(K log Hhi) operations;
this detects inconsistency but does not establish that h=|G| without the promise.

## Why the invariant and amortization hold

For any remaining promised h, L|h and

    beta^(h/L)=1  =>  ord(beta) | h/L  =>  L*r | h.

Thus A1 preserves the invariant without factoring r, L, h or |G|. The
identity L*ord(g^L)=lcm(L,ord(g)) is another proof, but ord(g) is never
computed by that identity. This is a divisor update, not a potentially
huge product of unrelated annihilators.

At a search stage,

    w=floor(Hhi/L)-ceil(Hlo/L) <= W/L.

Every completed nontrivial bounded search either terminates the whole
algorithm or multiplies L by at least two. Therefore

    sum sqrt(w_stage) <= sqrt(W) * sum_(j>=0) 2^(-j/2)
                      = O(sqrt(W)).                    (A2)

There are at most O(log Hhi) growth stages. No-growth elements cost binary
powering only, by the explicit beta=1 branch. The additional interval BSGS
can occur only once, on the terminating branch, so it fits the same bound.
Short/empty intervals and w=1 must use the exact bounded-search conventions.

The proposed group-operation bound is

    O(K log Hhi + sqrt(W) + polylog(Hhi))               (A3)

with actual list sorting/equality/index and integer arithmetic charged for
a bit-machine realization. A conservative soft bound is
O~((K+sqrt(W)+1)*poly(log Hhi)), times effective group-operation/encoding
costs. Max temporary table size is O(1+sqrt(W)); L never exceeds Hhi.
Pay every initial interval shift beta^(-a) and every exponent's bit width.
An adaptive algorithm can request another group element after each finished
one; no generation, mixing or useful-coverage cost is free in A3.

## Factoring interface and limits

For a class-number interval known to contain h(D), this algorithm can
annihilate all members of a paid generator set with a total search budget
O~(sqrt(W)+K), rather than K independent searches. The existing W019-B
cyclic-pivot extraction can inspect each element's 2-part immediately using
the current L. Later multiplication of L does not invalidate that work.
If the unique h branch occurs, it is a common annihilator for later samples.

This discharges a specific amortization condition even when no single
queried element initially has order greater than W. It does NOT produce the
interval, certify its analytic tail, generate enough useful elements, merge
different discriminants' groups, or improve the single-search sqrt(W) term.
Under the old conditional width W~sqrt(N)/sqrt(B), the balance against
Euler-product work B still has exponent 1/5. No changed exponent follows.

The primitive is closely related to exponent accumulation and existing
class-group algorithms; exact prior-art overlap must be checked. A review
should test common-multiple promises versus exact group cardinalities,
noncyclic output L<|G|, beta=1 traffic, r=1 guards, singleton intervals,
and cost under adaptively shrinking widths. These are precise falsifiers,
not requests to fit tiny timings to an exponent.
