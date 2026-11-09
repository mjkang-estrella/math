# W024 parent disposition

The full 202-line review was read. All 18 delivery payloads match the manifest,
whose SHA-256 also matches the independently delivered terminal anchor; see
W024-parent-intake-hashes.json. The child's 19 checksum entries include that
manifest. This was a symbolic review, with no candidate run or certificate.
Verified new complete factoring improvement: **NONE**.

Accept the public residue test separately for each root SIGN. On a retained
ordinary chart, E is a fixed nonzero residue modulo ell, so every integer
exponent is nonzero without a magnitude guard. At the covered primitive pair,
E = u*(p-1)^2 modulo ell in every valuation stratum. Thus the true sign
survives whenever p is not 1 modulo ell. In particular p=-1 is allowed;
discarding the whole chart would incorrectly lose this useful case.

Accept the explicit public schedule: sieve odd primes until their product
exceeds N, checking gcds first. For n=bitlen(N), the elementary central-binomial
argument in the review gives a sufficient sieve ceiling 16*(n+1)^2 and at
most n scheduled primes. If every legal scheduled prime divided p-1, their
product would divide p-1<N, a contradiction. The algorithm processes all
bases; it never acquires a good base using the hidden factor. The elementary
proof, not an unverified use of Bertrand iteration, supplies the size bound.

Retain the boundary repairs. A public target smaller than ell can occur for
unbounded N: set k=1, M=ell and rebuild the admissible integer ranges. Clamping
U and recomputing V preserves the stated coverage only with a valid renewed
width W, conservatively N*(U+V). It does not preserve an optimized complexity
estimate automatically. At k=1, a signed v chart can have two integer values.
Even/prime-power preprocessing and finite-input fallbacks remain explicit.

Uniformly in growing ell, chart acquisition has the review's conservative
O((1+ell^3*M^(4/5))*B^3) bit bound, with B its input/coefficient width.
This is polynomial-logarithmic overhead when ell is polynomial in log N.
The same conclusion cannot be imported for a future evaluator with unchecked
dependence on ell. Hensel lifting, root trials, inversions and signed endpoint
handling are part of acquisition. Root-series coefficients have denominators
that are powers of 2; an implementation must not invert arbitrary factorials.

The filter retains one or two signs per rooted chart and at least half the
old leaves. It cannot reduce the asymptotic carry count. The reviewed envelope
is O(M + W/M + max(U,V)^4/M^(3/5)), with the same geometric stratum sums.
Subboxes inherit the residue test and can be localized at logarithmic depth,
but each restricted product still has to be computed and paid.

Accept composition with W020's ORIGINAL uniform alpha and full two-adic
recovery after localizing a nonunit leaf. Processing earlier unsuccessful
bases does not invalidate its pointwise failure inclusion. This is a reduction
from a paid, covered product evaluator; no such faster evaluator is supplied.

The parent added three focused integer theorems in Factoring/RootCharts.lean:
covered_exponent_residual, covered_exponent_residue_dvd, and
chart_sign_product_residual. The existing scripts/check.sh run completed:
12 Python tests, source screen, Lean build and axiom audit passed. The new
theorems use only the audited standard axioms propext, Classical.choice and
Quot.sound. They check the algebra/divisibility, not the prime-field unit proof,
schedule, product algorithm or a factoring complexity theorem. No test was
rerun after the successful result.

Constructive continuation: W025 computes a common coefficient multiplier by
fixed-dimensional integer feasibility, then removes its ell-adic valuation.
It aims to shorten the actual common carry interval now permitted by W024,
with explicit acquisition and normalization costs. Its independent Opus audit
is live. Main-thread work continues on its remaining product costs and on a
separate coefficient route; acceptance is not contingent on polling that audit.
