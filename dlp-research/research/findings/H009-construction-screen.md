# H009 operational screen: explicit constructor, no demonstrated cap fit

Native Astra /root/h007_additive_relations completed this read-only review of
H009-crt-euclid-v1. No experiment, package installation or code change. Root
accepts the missing-budget conclusion, not an impossibility claim.

An explicit constructor starts with the usual cubic summation polynomial

    S3(a,b,c)=(a-b)^2 c² -2((a+b)(ab+A)+2B)c
              +(ab-A)^2 -4B(a+b)

for curve y²=x³+Ax+B. Substitute the actual CRT monomials, then compute S4 for
(x1,x2,x3,Z) and (x4,x5,r,Z) via two4x4 Sylvester determinants in an eliminated
variable. Their resultant in Z is an8x8 Sylvester determinant giving S6. A
division-free subset-minor determinant recurrence supplies a precise algorithm.
At most2*32+1024 polynomial multiply/add transitions occur, but EACH polynomial
multiplication is an explicitly paid term-pair convolution in sparse maps. This
transition count is not a bound of about one thousand field operations.
[Primary summation-polynomial context](https://eprint.iacr.org/2004/031).

No support/term-update ledger shows that construction plus an informative
Euclidean prefix fits the single1M-event/60s cap. This is unvalidated feasibility,
not proof it cannot fit. Five nontrivial coprime domain sizes already require
product>=2310. At sizes2,3,5,7,11 the degree upper bound is46832, but neither
degree nor this small example proves support size. Tiny parameters can even
reverse the degree ordering used in the eventual large-domain analysis.

Paid instance generation includes candidate primes p=cN+1, primality/factorization,
subgroup certification, curve/order checks, discarded curves and domain points,
targets and all polynomial construction. A preselected uncharged fixture or
precomputed coefficient table would not validate complete paid cost. Arithmetic
fixture validation can be useful but is not a faster ECDLP result.

For frozen v1, a first-remainder diagnostic begins only after the full f_R is
constructed and charged. Reducing modulo T^N-1 during construction, interpolation,
lazy leading-window construction or a lower-arity polynomial is a different
version. A partial prefix may reject a declared finite work allowance without
extraction; cap exhaustion during construction gives no evidence about Euclidean
fill, empty targets, gcd roots or useful relation yield. Successful prefixes
likewise do not establish K/sigma=o(B^(3/2)).

Decision: no numerical pilot yet. A separate candidate-specific reciprocal-series
paper argument is now being independently checked. All alleged support-growth
and full-solver consequences remain unaccepted until that review completes.
Verified improvement NONE; classical square-root baseline unchanged.
