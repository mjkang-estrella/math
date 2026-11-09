# H012 — finite reciprocal-certificate reuse screen

Date: 2026-10-08. Verified new factoring complexity improvement: **NONE**.
Disposition: **finite continuation threshold passed; asymptotic claim open**.

The parent implemented and ran the frozen [protocol](../hypotheses/H012.md)
once. The [source](../experiments/H012/certificate_reuse.py) and complete
[evidence](../experiments/H012/result.json) are immutable. This is a primitive
screen for W001 deterministic Card A, not a factorer or matched benchmark.

## Construction and checks

For each public unit j modulo the publicly factored smooth modulus m, construct
the index-m lattice `u*j² = N*t (mod m)`. Exact Gauss reduction of the scaled
basis `(m*C²,0), (c*C²,N)`, where `c=N*(j²)^(-1) mod m`, yields four candidate
directions per dyadic cell. Choose v in its required residue class modulo m²
nearest to `-u*C-N*t/C`. Both certificate congruences are asserted, and the
constant-quotient direction `u=t=0` is excluded.

The coverage test certifies `|u*z+v+N*t/z| <= H` on a whole real cell. It checks
endpoints and a possible stationary point by integer comparisons. A second
exact implementation checks the equivalent pair of quadratic inequalities,
including their possible interior extrema. The implementations agreed on every
candidate/cell pair in the frozen run. Greedy interval covering counts separate
connected cell runs separately, including reuse of the same certificate.

All 96 registered residue cases completed, with complete covers and no assertion
failures, partial cases, unstarted cases, or corpus shortfalls. The corpus has
six random public odd N values, two at each size, and 16 sampled unit residues
per N. These inputs are not promised semiprimes; no factor data were generated.
All rejected input/residue draws and every candidate certificate are retained.

| Input bits | Completed residues | Dyadic cells | Median selected intervals | Median compression |
|---|---:|---:|---:|---:|
| 64 | 32 | 11 | 2 | 5.5 |
| 128 | 32 | 22 | 2 | 11 |
| 256 | 32 | 43 | 4 | 10.75 |

The recorded run took approximately 0.383 seconds through result assembly,
excluding final JSON serialization. Timing includes corpus generation and
independent envelope checking; it is not a factoring runtime or bit-cost bound.
The registered 55-second internal limit was not enlarged.

## What remains unproved

The chosen `K=16*ceil(sqrt(N/m³))` gives substantial fixed slack. A constant
number of reusable dyadic cells can pass this screen while providing no
asymptotic improvement. The observed ratios do not establish the proposed
uniform `C(n)=O(n/log n)` certificate count, even for this pool.

The script generates O(n) candidates per residue and explicitly checks them
against O(n) cells. It uses ordinary Python arithmetic and Gauss reduction;
its recorded counts do not establish the faster generation and endpoint
selection costs assumed in W001's conditional analysis. The full collision
algorithm, high-order element preparation, handling of partial modular matches,
and all-input reduction are not implemented by this experiment. The tested
modulus is near N^(1/5), not the logarithmically rebalanced theoretical optimum.

Next decisive work: independent review of the lattice, exact envelope tests,
cover selection, and total cost; then a uniform bound or explicit admissible
obstruction to growing reuse. A larger convenient sample alone cannot supply
that result. Known rank-two lattice and collision machinery is not a novelty
claim. An accepted algebraic extraction invariant can be formalized separately
without asserting existence of a fast cover.

## Frozen SHA-256

    source   181e97caeef68b373b639fdb3f510b0811a7c902eb83e2f6ca1ea13cb04f0f13
    protocol 17f456aa1727cff5657d7de00e66251bce3d4b27e2de2d09b5574956c00bc456
    results  77b7d6573586a7eda648473c1cb850ee35bbb3f9fff6a269ecc70e59378f9a07

Source and protocol hashes match those embedded in the result. The coordinator
rechecked them before requesting independent review. Review findings and any
revised experiments must use new files without changing this frozen run.
