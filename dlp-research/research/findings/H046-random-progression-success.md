# H046 randomized affine progressions preserve four-list success

2026-10-09 UTC. Independently checked paper construction, not Lean-certified.
This supplies a success law for a structured input distribution to the H021
four-list route. It supplies **no fast reporter** and no ECDLP work improvement.
Working exponent remains 1/2; verified complete-work improvement **NONE**.

## Construction and exact moments

Fix an odd prime-order subgroup <G>, order q, and Q=[k]G. Fix a public subset
S of this subgroup, size L>0, independently of the randomness below. For each
of four lists j independently choose r_j,h_j uniformly in Fq. For indices
0<=i<n<q define

    P_1(i) = Q + [r_1+i h_1]G,
    P_j(i) = [r_j+i h_j]G, j=2,3,4.

Zero h_j and repeated points are initially permitted. For distinct indices
i,i', the map (r,h) -> (r+ih,r+i'h) has nonzero determinant i'-i. Thus the
two scalar entries are independent uniform. Adding fixed k in the first list
preserves this property. Since the four parameter pairs are independent, the
joint distribution of entries accessed by ANY TWO indexed quadruples is
exactly that of the H021 independent-entry model, with identical variables
where an index repeats. Higher-order independence is unnecessary for these
first and second moments. This holds for every fixed target scalar k.

Let Z count indexed quadruples with

    P_1(i_1)+P_2(i_2) = -(P_3(i_3)+P_4(i_4)) in S.

Then mu=E[Z]=n^4 L/q². Distinct quadruples have zero covariance unless their
complete left pair or complete right pair of indices is the same. For each
such shared pair the joint success probability is L/q³, so covariance is
L(q-L)/q^4. The two disjoint shared-pair cases each occur n^4(n²-1) times in
the ordered variance sum. Therefore

    Var Z = mu(1-L/q²) + 2 n^4(n²-1) L(q-L)/q^4
          <= mu + 2 n^6 L/q³,
    Pr(Z>0) >= 1 / (1 + 1/mu + 2q/(n² L)).

The probability bound follows from E[Z]^2/E[Z²]. With actual density
L/q asymptotic to a positive constant times q^(-gamma), 0<=gamma<1, and
n asymptotic to a positive constant times q^((1+gamma)/4), mu is bounded
away from zero and infinity, and 2q/(n²L) tends to zero. Success is bounded
below by a positive constant. Symmetry of S is not needed if the second
pair explicitly uses -S.

## Output caps, recovery and costs

For either intermediate indexed pair list, distinct indexed sums are
independent uniform by the same two-entry argument. Its output count X has

    E[X]=m=n² L/q,     Var X <= m.

For C>1, aborting above a cap ceil(Cm) loses at most 1/((C-1)²m) probability
per side by Chebyshev. Here m grows like q^((1-gamma)/2), so two such losses
tend to zero. A reporter still needs a bounded-work abort mechanism; an output
cap alone does not cap its unsuccessful scans, preprocessing or workspace.

The probability some slope h_j is zero is at most 4/q. Rejecting those samples
before running a reporter loses at most 4/q from unconditional success, with
retry/setup costs paid. Do not restate the exact moment formulas after
conditioning all slopes to be nonzero. Duplicates and repeated witnesses are
legitimate in the indexed calculation; a deduplicating reporter must retain
enough labels/indices for extraction and respect its stated output model.

A witness gives

    k = -sum_j (r_j+i_j h_j) mod q.

Its target coefficient is exactly one. No matrix-rank or nonzero-denominator
assumption is needed for this oriented equality; final scalar multiplication
verifies kG=Q. A detector returning only abscissae/sign classes must restore
the orientation and compatible indices rather than silently using this equation.

Eight scalar multiplications construct the four starts and steps. Translating
the first start by Q and generating all lists uses O(n) group additions;
scalar labels can likewise be advanced by addition. These are ordinary known
operations, not new primitives. Under output caps, list/report storage is
O(n+m) point/index records, plus the reporter's own workspace. Bit work,
sorting/matching, subset setup, exceptions, verification, unsuccessful attempts
and any amortization remain charged. No inverse table or secret-range promise
is present.

## What the structure does and does not provide

Each pair domain has the public form C+iH_1+jH_2, with distinct independently
sampled directions. Every fixed-i row is a progression. It is generally NOT
a common-step interval of n² points. A row reporter or multipoint method may
exploit those explicit lists, but must supply its actual arithmetic circuit,
sign handling and complete cost on this distribution. No theorem here gives
subquadratic pair reporting, efficient filter construction or a better solver.

This repairs a specific success gap in the algorithm gate. It does not license
the raw H046 Card A interval decomposition, a deterministic progression
success claim, or transferring the moment formulas to adaptively chosen S.
The next decisive construction is a paid reporter on this two-direction grid
that meets H046 Card D's corrected complete-work threshold.

## Process and validation

Root proposed the pairwise-independent progression construction after reviewing
H046's structured-list gap and H021-list-reduction-screen.md. Native Astra
/root/h007_additive_relations independently derived the exact covariance,
success bound, output caps, zero-slope exception and extraction; completed.
Root independently rechecked the two-shared-pair count and probability bound.
Native Sol /root/h034_c4_implementation completed the separate compatible-cost review.
This claim is a paper derivation, not asserted as an original prior-art discovery.
Its elementary proof above is complete within the stated finite-field model;
the missing reporter remains explicit. No new primary theorem is attributed.

No experiment, code/import, seed, new curve or Lean/Audit claim. H034 cap
unchanged. Project checks and exact command are in STATE; compilation does
not certify this probability proof or imply a cryptanalytic improvement.
