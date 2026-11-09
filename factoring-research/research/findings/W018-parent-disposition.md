# W018 parent disposition

2026-10-08 local. Both independent reports were read in full during parent
intake. Accepted below means independently reviewed mathematics, not a Lean
refinement or a new all-input factoring bound. New complete improvement: NONE.

## Accepted primitive and applications

For odd composite N with at least two distinct prime factors, arbitrary
positive binary M and B>=1, accept the expected factor-or-powered-order
primitive at O~((bitlen M+sqrt(B)+1) poly(log N)). The returned unit has a
known preimage a and beta=a^M of order greater than B, unless a factor is
returned. Uniform sampling applies to a, not to its power image. Failure is
contained in the equal-local-2-valuation event; no false independence from
the small-order test is required. Retain the whole squaring chain and all
duplicate/boundary handling in the exact bounded-order search.

Even/perfect-power preprocessing, exact rejection sampling, sorting/index
widths and exponent input lengths are paid. A prime input is outside the
composite promise. The order output is a completed decision, not an asserted
short independently checkable certificate. Expected retries are not a
deterministic worst-case theorem, and no priority claim is established.

Accept using M=product m_i, with its total input length charged once, to
share W016 true-error tables. The full consumer keeps K, integer ceilings,
component-order checks, all tags, recovery degree and actual bit widths.
Accept the stronger deterministic progression-product comparator
O~(K+sqrt(total occurrence length)) after clipping candidates to (1,N),
handling nonunit/large strides and descending full gcd products to a leaf.

## Accepted extensions and scope

For distinct odd semiprimes, accept the Cayley norm-one sampling law,
the <=3 expected-trial powered-torus preparation, and paid acquisition of
a Jacobi-minus-one d. Conditioning away a=0 or requiring gcd(a,N)=1 changes
the sampling law; the report's N=15,d=11 counterexample establishes why the
old law cannot then be reused. The all-residue sampler is the accepted one.

Accept the two-dimensional table's sufficient GLOBAL order thresholds and
integer determinant argument. Its dependency on ordinary-unit acquisition
is now discharged by the other completed review. Every explicit table
entry remains paid; global injectivity does not imply component uniqueness
for a different consumer, nor free sharing across slopes.

Accept the rational integer-valued grid-polynomial degree gap: when
2<=d<=H/8 and |R(j)|<=V, V>=H^2/128. The tangent-subtraction application and
positive-stride version have the stated strict error guard. The comparison
excludes the specified dense-degree implementation, not general succinct
circuits or factoring. Short binomial notation alone is not an efficient
representation/evaluation/recovery algorithm.

## Evidence and next computation

All 40 ordinary-review payloads and 41 checksum entries matched the terminal
anchor; all 17 extension payloads and 18 checksum entries likewise matched.
See [ordinary intake](W018-powered-parent-intake-hashes.json) and
[extension intake](W018-extensions-parent-intake-hashes.json). The ordinary
reviewer's one frozen certificate retained 21 cases, 3,287 checks and 16,370
charged events with zero failed checks, including excluded prime-power
controls and legitimate retries. Parent did not rerun or tune it. It is
finite branch evidence, not an asymptotic benchmark. Extensions used symbolic
proofs, with no experiment.

This removes a real base-acquisition obligation. It does not supply useful
factor restrictions. [W019 A](../hypotheses/W019.md) now attempts N-only
coverage of weighted sums through an auxiliary-square modulus. That whole
algorithm and its costs are under a new independent audit; do not treat it
as an automatic corollary of accepting W018.
