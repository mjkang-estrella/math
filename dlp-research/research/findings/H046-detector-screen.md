# H046 detector constructions: exact identities without a complete-work gain

2026-10-09 UTC. Independent initial proposer: native Sol
/root/h034_c4_implementation. Skeptical mathematical/cost reviewer: native Astra
/root/h007_additive_relations. Root independently checked the character count,
chord formulas and signed extraction. Both roles completed; no executable test,
file change by delegates, new Lean claim or claimed novelty.
Working ECDLP exponent1/2; verified complete-work improvement NONE.

## Character fingerprints of an unreduced chord

For ordinary affine inputs C,U with d=x_C−x_U!=0, define

    D=d²,
    N_±=(y_C∓y_U)²−(x_C+x_U)*D.

The two chord abscissae are N_±/D. For a uniform seed r in F_p, p odd,

    chi_p(N_±−rD)=chi_p(N_±/D−r)

because D is a nonzero square. Extend chi_p(0)=0; the fingerprint is ternary.
This is invariant under these square-denominator representations, not under
arbitrary rescaling by a nonsquare. Exceptional d=0/identity cases require
explicit point dispatch.

For fixed unequal u,v, the exact matching probability is

    c_p=(p−3)/(2p).

Self-contained count: the two shifts r=u,v never match. The product-character
sum sum_r chi_p((u−r)(v−r)) is −1. After an affine change of variable this is
sum_t chi_p(t(t−1)); the number of pairs z²=t(t−1) equals p−1, since
(2t−1−2z)(2t−1+2z)=1 is in bijection with F_p^*. On the remaining p−2
shifts, the character product is +1 exactly when the two nonzero characters
match and −1 otherwise. Thus there are (p−3)/2 matching shifts.

For m independent seeds and a FIXED list of T abscissae independent of those
seeds, linearity of expectation gives the exact false-match count

    E[unequal-key matching pairs]
       = #{i<j : u_i!=u_j} * c_p^m
       <= binomial(T,2)*c_p^m.

The list need not have independent keys, but it must satisfy the seed condition.
A fingerprint-dependent successor or stopping length cannot be substituted
without further argument. A fixed complete cap list can bound any stopped
prefix if that cap list is itself seed-independent.

A chain detector stores fingerprints, fractions N,D and descriptors; it confirms
fingerprint hits by N*D'=N'*D. For confirmed P=epsilon*P', epsilon=±1, labelled
P=aG+bQ and P'=a'G+b'Q give

    (b−epsilon*b')*k = epsilon*a'−a.

Exclude zero coefficients and verify kG=Q. Equal abscissae do not alone supply
the sign; test the signed candidate equations or use paid point information.
Infinity, zero denominators and ternary zeros have their own dispatch.

### Cost screen, scoped to the stated circuit

Let A,M,S price field addition/subtraction, multiplication and squaring.
The literal fraction-pair circuit above uses M+3S+6A, excluding input point
production. Sharing r_j*D across the two outputs gives per-key arithmetic

    (1/2)M+(3/2)S+3A + m*((1/2)M+A+C_chi).

The direct cross-product confirmation uses 2M+A per candidate pair, plus
label/sign handling and final scalar verification when needed. Store and charge
two field elements, packed ternary fingerprint, descriptors and chain metadata,
all seed generation/storage, initialization/release and memory traffic.

For long lists of distinct keys, constant m leaves quadratic expected false
comparisons in this explicit chain implementation. m near log2(T) suffices
for O(T) expected false pairs, but then every key pays a growing number of
fingerprint operations. This is a bound on this implementation under the fixed
list model, not a universal lower bound for character-based detection.

Direct Euler powering is one possible expensive C_chi implementation, not a
necessary cost. Binary Jacobi, batched character algorithms, a different
fingerprint family or a different bucket detector need their own invoices.
Even the r_j*D products in the displayed direct circuit remain paid.
H019's comparator may adopt any applicable detector optimization too.

Comparing just this fraction-generation M/S subtotal with H019's limiting
2.5M+S suggests a nominal allowance 2M−S/2 per key before fingerprint costs.
That is NOT a complete saving: the input-generation schedule, finite batches,
additions, peak bytes, nulls, extraction and detection/early stopping must
match. No invoice meeting that gate is supplied. This is elementary field
character fingerprinting, not the scalar Legendre signal of H045/H046.

## Fixed-anchor slope keys

For a finite fixed known-log anchor J=jG in the odd-order subgroup, equal finite
slopes through J mean the same line. Its residual intersections, counted with
multiplicity, give

    R=P or R=−P−J.

At P=J use the tangent value; O and −J are the pole fibre and require explicit
dispatch. Other tangencies are handled by intersection multiplicity. For the
nontrivial collision the labelled recovery equation is

    (b_P+b_R)*k = −a_P−a_R−j.

Again a zero coefficient is a null relation. Translating by J/2 changes the
involution into ordinary negation. Thus this is the shifted negation quotient,
not a larger automorphism quotient or a newly established useful-event surplus.

Using a slope already computed in addition is a possible local reuse. A varying
anchor changes the fibre relation: tagging by the anchor compares only within
one anchor, while equal numerical slopes across different anchors alone do not
give the displayed equation. This does not exclude a separately specified
cross-anchor construction. Full point advancement, descriptor costs and a
useful stopping law are still needed; no such competitive full schedule emerged.

## Fraction-free polynomial intersection

For each role's nonzero denominators form the polynomial product

    F(Z)=product_i (D_i*Z−N_i).

Two products have a nonconstant gcd exactly when their abscissa sets intersect.
Multiplicities cause no false geometric witnesses. Product-tree/gcd descent
can recover source indices without factoring the gcd into every root.
Confirm the actual fractions and use the signed scalar equations above.

Every polynomial operation, leading-coefficient division, tree construction or
rebuild, memory access, index extraction and delayed stop is charged. One common
root can yield only null scalar equations; duplicate geometric keys may force
additional witness reporting/descent before a useful pair appears. The gcd
primitive supplies neither a useful-relation law nor an incremental online
stopping policy.

Ordinary polynomial algorithms are established tools (see the source scope in
H046-half-orbit-evaluator.md). Applying them here is not a novelty claim.
Their straightforward upper bounds do not prove that all fraction-free
detectors lose. No named construction gives a matched complete-work gain.

## Decision and next evidence

Retain all three scoped identities and the fixed-list fingerprint bound. Reject
admission of an experiment on the present evidence: there is no sufficiently
specified competitive complete detector to measure. This is a missing
construction, not an impossibility theorem.

The next decisive paper object is an explicit incremental equality detector
with paid input production, actual memory cap, null/sign recovery and preserved
early stopping, compared against competent batched exact-x detection. No extra
Lean infrastructure is justified by these identities alone. Source/probability
checks are paper evidence; scripts/check.sh validates only existing artifacts.
