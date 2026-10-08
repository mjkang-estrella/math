Raw Grok initial report — not endorsed. Task node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h022-independent-mechanisms-grok-20261008-r1

No survivor. Three complete-solver mechanisms are worked far enough to price, and none beats negation-aware rho at low memory or the matched x-only interleaved baby-step giant-step (BSGS) comparator at Θ(√q) memory. Verified improvement stays **NONE**. No experiment was run, and nothing was written to the repo.

The low-memory reference is negation-aware Pollard rho: √(πq/4) ≈ 0.886√q batched affine additions at the project 5M+1S ledger. The high-memory reference is the H019 specialization of Galbraith–Wang–Zhang: about 0.62 times that field work at s=S/M=1, with square-root storage of abscissae. Setup, memory, false matches, and recovery are charged below. These cards do not use an elliptic-divisibility-sequence dependency schedule or a translated-subset index.

## Card 1. Lone involution fold ι(P) = −P − G

**Mechanism.** Use the affine involution ι(P) = −P − G as the only canonicalization of a Pollard walk. Orbits are {P, −P − G}. One fixed point solves 2P = −G. The state count is (q+1)/2. The slope from P to G is constant on each orbit, so a collision of canonical points is an ordinary coalesced endpoint. Labels stay affine: if P = [a]G + [b]Q, then ι(P) = [−a−1]G + [−b]Q. A merged endpoint with coefficients (a,b) and (c,d) gives (a ∓ c) + (b ∓ d)k ≡ 0 or the translated form from the ι update. The coefficient of k is nonzero unless the two b-coefficients match, which is the usual null event of probability O(1/q).

Exact step: from canonical P, add G and negate to materialize ι(P), compare abscissae, replace the label if ι wins, hash the chosen abscissa, add the table jump, and repeat. Negation cannot be substituted for that test: x(ι(P)) ≠ x(P).

**Expected gain.** None. The fold has the same size as the negation quotient, so the step count is again √(πq/4) ≈ 0.886√q. Each step is two affine additions, not one. Total is about 1.77√q additions, twice negation rho and far above the x-only BSGS field-work ratio 0.62. Flipping the sign of y is free for negation because the abscissa is invariant. Here the abscissa moves, so the second point has to be built.

**Prior art and access.** Negation rho is Bernstein–Lange–Schwabe, already the project baseline. H017 blocks using this involution and negation together: the two maps generate a translation by G and the generated equivalence is the whole prime-order group. This card uses ι alone. No new primary paper was read for it. Extra automorphisms at j ∈ {0, 1728} are outside the Aut = {±1} target.

**Unsupported assumption.** None survives. The natural hope was a second √2-type fold at the cost of one addition. The orbit size is real, and so is the label map. The cost is not.

**Falsifier.** Already decided by the operation count. An implementation kills any “same constant as negation” claim as soon as the canonicalization addition is metered separately from the jump. Reopen only if x(P) and x(−P−G) can be compared at cost 0 in the 5M+1S ledger. That forces x(P) = x(−P−G), hence ι(P) = ±P, hence G = O.

**Preprocessing, memory, recovery.** Jump table of size r = polylog(q), built by O(r) additions. Distinguished-point storage is the usual O(θ√q) canonical points plus seeds. Replay of the colliding walks recovers the two labels. One scalar multiplication checks the candidate. Failed cycles and replay are the same kinds of costs as in negation rho, on top of the extra addition per step.

## Card 2. Cubic-algebra “half bit”

**Mechanism.** Let f(x) = x³ + Ax + B, irreducible over F_p because an odd order group has no rational 2-torsion. Let L = F_p[θ]/(f(θ)). The 2-descent symbol of an affine point (x,y) is the class of x − θ in L^*/(L^*)². The proposed solver treats that class, or a chosen square root β² = x − θ, as a trit of k, then walks by halving.

Exact arithmetic content: [2] is bijective on a prime-order group, so E(F_p) = 2E(F_p). The kernel of this descent map contains 2E(F_p), so the symbol is the identity class for every rational point. A square root β, when it is computed, is input to the ordinary halving formulas and returns the unique rational point [2^{−1}]P. It does not choose among cosets. There is no rational 2-torsion coset to label.

Cost if the square root is used anyway: one exponentiation in L, which is Θ(log p) multiplications in a degree-3 extension, hence Θ(log q) base-field multiplications per step. An addition step is Θ(1) in that ledger. A halving rho would be slower by Θ(log q) and would still be a permutation of a set of size q, not a walk on a smaller set.

**Expected gain.** None. The symbol is constant on the rational points, so it contributes no partition of k. Unique halving is multiplication by the public unit 2^{−1} mod q. It preserves the search space.

**Prior art and access.** This is the finite-field 2-descent map, not a p² Hensel digit and not Silverman’s torsion lift. H010’s parity selector assumed an unspecified correction digit on that lift. H003 and Katagiri–Kobayashi already block reading k from p-adic division limits. Direct-halving norm steering is a parked walk and is not reused here. I did not re-read Silverman this session; the bijectivity claim is the prime-order group law. I did not read arXiv:2304.14150 beyond a search snippet and do not use it.

**Unsupported assumption.** That x(P) − θ changes quadratic class with the discrete log, or that the two square roots encode a bit of k. Both fail because the half is unique and the symbol is identically trivial.

**Falsifier.** Already decided. On any one affine rational point, x − θ is a square in L^*. Variability in k would require both classes. A single non-square on any rational point would refute the kernel claim. No search is required to see that a constant predicate does not split the scalar.

**Preprocessing, memory, recovery.** Building L is O(1) field storage. Each step pays a cubic-field square root, not an inversion batch. A walk of length T stores ordinary distinguished points and still needs a real point collision. Recovery is the usual linear equation from labels. If the symbol is used as a filter, it never rejects a rational point, so it cannot reduce the list.

## Card 3. Global almost-additive Wagner key

**Mechanism.** Split the scalar into four public-base blocks of length q^{1/3} and try to merge the four point lists in Wagner’s order, exponent 1/3 rather than the meet-in-the-middle exponent 1/2. Round 1 must emit about q^{1/3} partial sums without adding every pair. That requires a key κ(P), computed from each point in O(1) field operations, such that κ(P) and κ(R) determine a small bucket containing P+R.

The integer-valued version is an almost-homomorphism: |f(X+Y) − f(X) − f(Y)| ≤ D for every pair of rational points, with f : E(F_p) → Z. Normalize f(0) = 0. The pair (0,0) gives |f(0)| ≤ D before normalization, and the defect at most doubles. Induction gives |f(nX) − n f(X)| ≤ (n−1)D′. Set n = q. Then qX = O, so |f(X)| ≤ D′. The image has at most 2D′+1 values.

A 4-list merge of lists of size q^{1/3} needs at least q^{1/3} buckets to cut n² pairs down to n survivors. That forces D′ ≥ q^{1/3}/2. The defect window is then as wide as the whole image, so the predicted bucket does not discard candidates. Exact homomorphisms are the case D = 0, already known to be trivial into F_p and into any 2-group (the source group has odd order).

**Expected gain.** None inside this mechanism. The conditional exponent 1/3 is not available from a global bounded-defect key. Naive pair addition in round 1 costs q^{2/3} field additions and already loses to √q. Meet-in-the-middle 4-sum at list size q^{1/4} costs q^{1/2} and ties BSGS with worse constants.

**Prior art and access.** Wagner’s generalized birthday algorithm is the classical merge (CRYPTO 2002); I did not re-read the PDF this session. Shoup’s generic bound is not used as a coordinate impossibility. The four-list x-prefix mutual-information test is already a project card and is not repeated. The H020 low-bit shadow is a different claim: canonical F_p arithmetic does not simulate integer arithmetic modulo 2^w. This card is about global defect of a key on all pairs, not about simulating carries inside a macro-step.

**Unsupported assumption.** That some explicit coordinate key is almost additive on every pair with defect o(q^{1/3}) and still has ≥ q^{1/3} buckets. The bound forbids that pair of properties together. Keys that are not almost additive on all pairs, and combination rules other than integer addition, are outside the kill. No such key is supplied, and an exact homomorphism onto a Wagner alphabet does not exist.

**Falsifier.** The induction above. For any concrete κ someone writes down, the same test is finite: on one ordinary curve, sample pairs, and kill the key if the median defect is larger than the key range. That sample is specified, not run. A key that passes only on an unstructured subset of pairs does not yield a sort-merge, because finding those pairs is the sum problem again.

**Preprocessing, memory, recovery.** Four lists of size n = q^{1/3} cost Θ(q^{1/3}) point constructions and Θ(q^{1/3}) field elements of memory if a separable merge exists. It does not, under the defect hypothesis. The version that actually adds pairs uses Θ(q^{2/3}) additions and Θ(q^{1/3}) memory after hashing. A genuine 4-tuple with one list shifted by Q gives one linear equation; the coefficient of k vanishes with probability O(1/q). One scalar multiplication verifies it. Those recovery costs never become active, because the merge does not return a true tuple cheaper than BSGS.

## What this pass does not reopen

Passive collinear triples among stored points still wait on a detector. At list size q^{1/3}, a detector of cost n^{3/2} ties √q, and the project already has no witness-producing detector below that line. Rational-image collisions, chord bonuses, signed low-bit macro-walks, and unique-halving norm walks stay closed. Degree of a summation polynomial is not treated as a runtime lower bound. No training set is assumed free.
