# r238: all-ear intersection remains unresolved

Status: HOLD; credit zero. Counts remain 9 additional / 39 total / next 40. No PROOF file is justified. Inverse-KL is retired, without reopening it. The rank19 transform example is not an ordinary-log-concavity counterexample.

## Literal source and inherited reduction

Read frozen Leader–Tan https://arxiv.org/pdf/2610.39116v1, posted 29 October 2026, body dated 30 October, Sections 1, 3, 4 and the proofs of Theorems 2–3 and Lemma 8. Their T_m is C_(m-2). The target is: for every convex n-gon, every family of triangulations whose every pair shares a literal ear diagonal (i-1,i+1) has size at most C_(n-3). n>=5 avoids the quadrilateral's two vertex labels for the same ear diagonal. n=4 is immediate separately.

Theorem 2 concerns intersections witnessed by a specified proper subset of ears. It does NOT mean that omitting from a triangulation family one ear-containing member suffices. Theorem 3 gives only C_(n-3)+C_(n-5). Its proof splits F02={T in F: ears0,2 present} and F13 analogously. Deleting F02 permits the source compression, giving |F\F02|<=C_(n-3); deleting the two ears in either exceptional class gives cross-intersecting reduced polygon families, whence |F02||F13|<=C_(n-5)^2. Neither inequality pays for both exceptional classes.

The exact-ear reduction from r235 is reused, not claimed new:

    w_n(S) = sum_(T separated, T contains S) (-1)^(|T|-|S|) C_(n-|T|-2).

The target is the weighted intersecting-family inequality for these nonnegative integer weights. Prescribing nonadjacent ears and deleting their vertices proves the containment count; inclusion–exclusion proves the formula. Saturation by literal ear patterns proves equivalence. Existing optima n5..10 remain finite diagnostics. This lane does not extend them. The known Talbot-shift, rotation-orbit, and fractional C5 failures are not rerun as new work.

## Mechanism 1: actual triangulation transfer and a failed Hall repair

For T containing ear2, remove diagonal (1,3), delete vertex2, rename vertex1 as2, and insert the new ear1 with diagonal(0,2). This is a bijection phi between the FULL stars of ear2 and ear1: the remaining labeled cyclic polygons are identical. Thus no loss of multiplicities occurs. Define the usual collision-retaining family compression: replace T by phi(T) if phi(T) is not already in F; otherwise retain T. Since ear1 and ear2 cross, these are disjoint stars, and cardinality is preserved.

This fails literal ear intersection on a maximal family, not merely on a singleton weight comparison. At n6 start from the five triangulations containing ear0. The compressed family contains

    A={(1,4),(1,5),(2,4)}, ears(A)={0,3},
    B={(0,2),(2,5),(3,5)}, ears(B)={1,4}.

Their literal ear sets are disjoint. These are genuine noncrossing triangulations, with all three diagonals displayed.

A stronger repair attempt allows ANY new ear1 triangulation, abandoning the fixed phi and all remote-pattern restrictions, while retaining every original member without ear2. For this same hexagon star, three members are retained and two must move. There are ZERO ear1 triangulations intersecting all three retained members on ears. Hence even the unrestricted candidate side of the Hall matching has size0 for demand2. This rules out an entire local compensation-injection scheme, not just the displayed transfer. A successful scheme must also move some members that do not contain the compressed ear, or allow target ears other than ear1. mechanisms.py checks this directly over literal triangulations and records n5..9 diagnostics; n6 alone proves the obstruction.

## Mechanism 2: source boundary split with a deficit invariant

Before assuming a stronger induction, state the tempting boundary claim explicitly:

    For every ear-intersecting F, |F\F02| + |F13| <= C_(n-3).     (D)

It would strengthen the source's independent deletion and cross-product bounds by charging one boundary class to the slack created by deleting the opposite class. Applying both cyclic orientations would imply the desired full bound by choosing the smaller exceptional class.

(D) is FALSE already at n6: let F be the entire ear1 star. Then |F|=5, F02 is empty because ear1 crosses ear0 and ear2, while |F13|=2 (prescribing two nonadjacent ears leaves a quadrilateral). Its claimed left side is7>5. More generally these values are C_(n-3),0,C_(n-4). A valid state theorem cannot charge an asymmetric boundary class without accounting for the retained star orientation. The failing stronger theorem is recorded before any induction uses it.

A different proposed stronger state assertion is: after forbidding any ears B, every intersecting family in the conditioned measure is bounded by its largest conditional star. The restricted diagnostic B={1,3,5}, n6..9, testing only three-pattern intersecting candidates, found no violation. This is NOT proof or exhaustive optimization and is not assumed. It remains a separate, unqualified conjectural strengthening. It would still require a reduction showing the actual changing boundary states are of this form.

The source's C/D compression weights sum TWO patterns only because ear0 is absent. Restoring ear0 produces exactly the retained-star obstruction above. Tracking only total class weights or only their product loses the information about which ears witness intersection with the retained class. The next meaningful state must therefore retain that witness relation (a cross-intersection incidence profile), not just a scalar boundary deficit. No closed all-n recurrence or uniformly nonnegative potential was obtained.

## Breadth result and qualification

SCOUTING.md reads eight distinct original question families, mostly initially posted before 2018. A complete 3x3 Boggle diagnostic found twelve 11-edge lists under the fixed-nine-symbol universe, but EVERY list uses only eight symbols. The all-nine-symbol-support interpretation has zero such lists. This endpoint issue is explicitly withheld from discovery promotion; no source counterexample or substantive credit is asserted. The current broader Boggle scoring result concerns a different task. Exact candidate clues and eight embeddings are saved for root scope review.

No all-n ear proof or strict source counterexample was found. No current complete public-registry inventory could be read through permitted routes; old inaccessible intervals remain parked. Current arXiv screens are bounded and sometimes polluted by unrelated keyword matches. They do not clear novelty. Scientific originals/copies and newly retrieved primary bytes are bound before use and verified after writing. Administrative files are snapshots only.
