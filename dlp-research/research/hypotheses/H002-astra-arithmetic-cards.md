# H002 independent arithmetic cards (unverified)

Native Astra `/root/h002_arithmetic_ideas` completed without reading other cards,
editing files or running experiments. Three distinct high-risk mechanisms; no
improvement established. This record preserves proposed bridges and limitations,
not an acceptance of their correctness/novelty. Let n be subgroup order and g0
the already usable small-automorphism quotient in the matched baseline.

## A1. Arithmetic-selected odd EDS character correlations

Mechanism: s_j=χ(ψ_j(P)); search a small predetermined family of odd products
such as s_j*s_(j+a)*s_(j+b), with offsets selected by addition chains or available
CM identities. Relative signs in a target window may be computed from Q without
knowing k. An odd product would orient the window if the corresponding true-sign
statistic has persistent bias. Use the EDS residue/parity reduction recursively
and verify the final scalar, including quasi-periodicity and index wraparound.

Potential gain: orientation cost cL per stage gives roughly cL*polylog(n) total
plus selection/preprocessing. Under an independence approximation L≈ε^(-2);
c*ε^(-2)*polylog(n) must beat the applicable rho cost sqrt(n/g0). This suggests
ε much larger than n^(-1/4) when per-sample overhead is small, not a theorem for
correlated windows. Use actual reconstruction error and work, not bias alone.

Scope/prior art: [Lauter–Stange](https://arxiv.org/pdf/0803.0728) already proposes
EDS bias/pattern searches and gives reductions subject to conditions including
gcd(n,p−1)=1 and suitable φ(P). Do not claim that proposal as novel. The narrower
arithmetic-selected odd family has UNKNOWN novelty. [Shparlinski–Stange](https://arxiv.org/abs/0912.5246)
gives relevant character-sum bounds. Root additionally found [Bhakta–Shparlinski2025](https://arxiv.org/abs/2507.09271)
on shifted/multidimensional correlations and [Bhakta2026](https://doi.org/10.4153/S000843952610191X)
on multiplicative twists. Only abstracts inspected by root; applicability of
their precise bounds to the proposed family remains unresolved, not a refutation.

Unsupported assumption: inexpensive statistic selection finds strong enough
orientation information on fresh curves/generators without an O(n) learned table.
Cheapest falsifier: fixed family, increasing tiny ordinary curves, fresh seeds,
multiple-testing correction and even-order negative controls (even products cannot
orient global negation). Count known-multiple generation, EDS/character operations,
selection, failed orientation and complete scalar recovery. A toy failure only
rejects that family/configuration. Relation to L1/L2: same broad prediction-to-
recovery goal but a specific arithmetic representation and reduction; deduplicate
at synthesis without erasing the distinct falsifier. No test launched yet.

## A2. Compress the accumulated defect of a p-adic section

Mechanism: for a cheap nonhomomorphic section s into a curve lift modulo p²,
define g(R)=log([n]s(R))/(np) mod p on the prime-to-p subgroup. Define
c(R,S)=g(R)+g(S)−g(R+S). Accumulated binary-chain corrections give
g([k]P)=k*g(P)−C_k mod p. Search a small predetermined section family for an
effectively enumerable small set C containing many complete C_k values, while
g(P)≠0. Enumerate corrections, recover k modulo p, enumerate the few canonical
range representatives and verify kP=Q. Weighted accumulation matters: a small
alphabet of local defects does not imply a small set of complete corrections.

Potential gain: correction support n^α with α<1/2 and equally cheap construction/
enumeration could beat square-root candidate verification, including log factors
and success probability. Count section/lift search, all known samples, ring scalar
operations, description/storage, retries and verification. No O(n) inverse dictionary.

Prior art: [Smart](https://doi.org/10.1007/s001459900052) needs anomalous curves;
[Filippone](https://arxiv.org/pdf/2304.14150) starts with stronger rational-point
relations than arbitrary finite-field lifts. Neither supplies this bridge. Novelty
of compressed NONZERO lifting defects is unknown. Exact additive maps from Z/n
to additive F_p are zero when n≠p; the prime-to-p torsion lift has zero log.
Thus a homomorphic section destroys the desired signal instead of solving ECDLP.

Unsupported assumption: a simple section concentrates complete corrections in
a small computable set on fresh ordinary curves. Cheapest falsifier: examine
whether the section family spans only a few affine features; then tiny exhaustive
support counts with fresh-curve controls. Do not infer asymptotics from them.

Coordinator prerequisite: ring operations and formal-kernel chart handling must
be correct. Existing W019 found a broken general ring-addition prototype; do not
reuse it or divide by nonunits. Focused candidate-specific arithmetic validation
would be required if this card survives independent review, not generic machine
refinement. No arithmetic implementation or experiment has been accepted yet.

## A3. Fast large-orbit canonicalization with a transporter

Mechanism: an efficiently evaluated endomorphism acts by known λ of order m
on the subgroup. Compute a reproducible orbit representative AND its multiplier
λ^j, then perform rho on roughly n/m classes while updating scalar coefficients.
Investigate Lattès/division-polynomial recursive orbit representations with actual
pruning/minimum selection. A fingerprint without a transporter does not suffice.

Potential gain: W_pre+C_can*sqrt(n/m) must beat C_rho*sqrt(n/g0). In particular,
C_can/C_rho<sqrt(m/g0) before considering setup. A linear scan loses; a sqrt(m)
canonicalizer can consume the entire apparent gain. Account for m/λ discovery,
representation size, coefficient transformations, cycles, memory and recovery.

Prior art: [known quotient-rho baseline](https://eprint.iacr.org/2011/003),
[moderate-CM arithmetic](https://eprint.iacr.org/2024/1985). These supply neither
the claimed fast canonicalizer nor a discovery. Multiplication-by2 gives a universal
odd-order test case; rational Frobenius is identity on E(F_p). Exact CM availability
must be stated. Large subgroup permutation order is not a free algorithmic gain.

Unsupported assumption: finite-field orbit structure permits sub-sqrt(m) exact
representative AND transporter evaluation with modest setup/storage. Cheapest
falsifier: on small known-m curves charge all field operations and representation
size for a specified pruning algorithm. Reject that implementation if it scans
m leaves or spends sqrt(m) merely recovering the multiplier. No generic lower
bound alone excludes a coordinate algorithm; no fast pruning method is supplied.

Proposer ranks A1 testability first, A2 cheap obstruction tests second, A3 last.
Coordinator has not accepted this ranking across the whole pool. No experiments,
Lean work or full-size claims follow merely from receiving these cards.
