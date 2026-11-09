# MathDB 364205: a rigid facet with 34 vertices at scale 5

Candidate only. No acceptance, priority certification, upload, or publication is asserted.

Briggs, Feng and Wells, *Facets in the Vietoris–Rips complexes of hypercubes*, arXiv:2408.01288v1 and v2, Section 2, define maximal diameter and rigidity. Section 6, Conjecture 1, asserts that the largest maximal rigid diameter-r subset of Q_n has size 2^r whenever n >= r. The current arXiv landing page retrieved on 2026-11-01 lists v2, revised 5 August 2024. Both inspected versions retain this conjecture. No separate published version was located in the bounded checks; that is not proof none exists.

Represent a vertex by an integer from 0 through 255. Coordinate i, for i from 0 through 7, is +1 when its binary digit is 1, and -1 otherwise. Take

```
A = {0, 3, 5, 8, 10, 11, 12, 15, 18, 23, 26, 30,
     66, 68, 71, 74, 78, 79, 130, 131, 132, 135, 137,
     138, 140, 142, 143, 150, 158, 194, 198, 203, 206, 217}.
```

These are 34 distinct vertices. Their Hamming distances are numbers of differing binary coordinates. The ordered-pair distance counts for distances 0, 1, 2, 3, 4, 5 are respectively 34, 72, 276, 308, 276, 190; there are no pairs at greater distance. Every row has a pair at distance 5. For every vertex outside A, its maximum distance from A is greater than 5. Thus A has diameter exactly 5, every one of its points attains the diameter, and no further cube vertex can be adjoined while preserving diameter at most 5. It is therefore a maximal rigid facet in the literal source sense. Consequently b'(8;5) >= 34 > 32 = 2^5, refuting the universal conjecture.

The finite computations in this proof are certified by kernel reduction in `Cube.lean`, not by trusting Python. `card_A`, `pair_bound`, `rigid_A`, `outside_A`, and `diameter_attained` prove all required facts over the entire cube, not a sample. `Signed.lean` constructs an explicit equivalence from Boolean coordinates to integer signs, proves that it preserves Hamming distance, and transfers cardinality, maximality and rigidity. Its endpoint `MathDB364205.literal_source_refutation` is the negation of the source assertion expressed with `IsGreatest` on all attainable facet cardinalities. For finite cubes, this is exactly the statement that the largest such cardinality equals 2^r. There is no surrogate predicate or unproved decoder bridge.

`certificate.json` supplies all 256 farthest-distance rows with explicit witnesses. The independent coordinate-comparison implementation in `scripts/certificate.py` reproduces them without using the xor/popcount implementation that discovered A. This script is explanatory redundancy; the Lean endpoint is the proof certificate.

The construction changes the proposed extremal size itself. It uses n = 8 and r = 5, both in the central source domain. It is neither an endpoint correction nor an adjacent homology question. Small finite size and short kernel checks do not establish significance by themselves. Independent significance and bounded prior-art reviews remain necessary. No exact optimum, smallest counterexample, asymptotic result, or additional family credit is claimed.
