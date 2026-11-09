# W007 — pair-selected merging and why an interval gain can be misleading

2026-10-08. Parent constructive note. PROVISIONAL, not yet independently
reviewed; not part of tasks A-D's frozen submitted results. No experiment
or new factoring bound. This changes the parameter acquisition rule instead
of assuming that a rational polynomial can be kept fully split.

## Executable update

For current P, obtain two fresh independent uniform residues r,s modulo N.
Compute u=P(r), w=P(s), choose a=u+w, and replace P by

    P_next(X)=P(X)*(P(X)-a).

This explicitly merges the fibers u and w, because both evaluate to -uw.
It preserves every existing local collision. Evaluation and acquisition are
paid: two depth-j evaluations at stage j, hence O(k^2) training operations
through depth k, then O(k) per fresh probe. Gcd tests of u-w and other
already acquired values may return early factors; all such branches need
accounting. Trained pairs themselves merge globally and are not new proper
factors. At fixed history fresh probes can be batched using a paid detector.

Over an odd prime, let mu be the current output law, c=sum mu^2, and
h(a)=sum_y mu(y)mu(a-y). The actual parameter a has law h. The one-stage
identity consequently gives

    E[c_next-c | mu]
      = sum_a h(a)^2 - sum_y h(2y)*mu(y)^2.

This is a four-sample additive-energy quantity, rather than the cubic law
for selecting a=P(r). It identifies actual saved work if the gain persists:
fewer independent outputs would be needed to witness a useful local
collision. No rapid growth is assumed. After a global stop the ordinary
CRT independence claim must be re-established or avoided.

## A seemingly favorable case and its acquisition trap

For the hypothetical local law uniform on {0,...,L-1}, with 2L-2<p,

    sum_a h(a)^2=(2L^3+L)/(3L^4),
    0 <= sum_y h(2y)mu(y)^2 <= 1/L^2.

Thus this single local update adds roughly (2/3)c for large L. The full
field uniform control instead adds (p-1)/p^2. This is a concrete potential
amplification mechanism, not a result about the reachable laws of P_j.

Generating small ordinary integers modulo N does NOT supply the independent
local interval laws. It supplies a strongly correlated global list. In
fact there is an exact obstruction for that attempted implementation.
Suppose all compared ordinary representatives y,w lie in {0,...,L-1},
a is the sum of two such representatives, and min(p,q)>2L. Then

    f_a(y)-f_a(w)=(y-w)*(y+w-a),

and both integer factors have absolute value less than 2L. Neither can be
a nonzero multiple of p or q. A collision modulo either prime is therefore
an exact integer collision, and occurs modulo both primes. The large
one-step concentration gain contains no separating pair in this attempt.
Gcd of the difference is 1 or N, never a proper factor.

This does NOT refute a componentwise polynomial map whose outputs have
independent local interval laws; those CRT-combined outputs need not have
small global representatives. Obtaining that map from N alone is a separate
paid generator problem, and cannot be replaced by sampling a small interval.

## Why repeated interval amplification is also unproved

Even in one field, a quadratic image of an interval is generally a set of
quadratic values, not another interval. All choices share the identity

    P_next(x)-P_next(y)
      =(P(x)-P(y))*(P(x)+P(y)-a).

Every new local collision therefore has a precise source: a new sum
condition at the previous level. Large formal degree is not a substitute
for many cheaply acquired useful sum conditions. Randomly translating
outputs does not solve their additive structure, since convolution energy
is translation invariant.

A cost test for any proposed k-stage generator is explicit. If it actually
costs k^2 operations to construct and k per independent output, then reaching
local collision mass c_k gives a heuristic sample/evaluation envelope
k^2+k/sqrt(c_k), before bit costs and success/CRT obligations. Linear mass
growth c_k about k/p gives k^2+sqrt(pk), which cannot beat the k=O(1)
sqrt(p) control in this model. Stronger persistent growth or a real training
sharing identity is required. This is only a model comparison, not a lower
bound on factoring or on all ways to detect the collisions.

Next decisive question: can a concrete N-only componentwise algebraic
generator preserve enough additive energy across several updates without
paying for its small local image? No numerical screen is justified merely
by the favorable interval formula; the naive interval generator is already
symbolically rejected. The current residual audit continues independently.

