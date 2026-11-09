MathDB 331705: one wedge refutes both starlikeness readings

Scope and source. Klén–Mohapatra–Sahoo, arXiv:1511.01298v1, Conjecture 4.7, asks whether every positive-radius Cassinian ball centered at a starlike center in a proper starlike domain is starlike about that center. Its statement imposes no boundedness restriction. The actual cached source text was read. Klén, arXiv:1603.00590, Section 2, defines the stricter meaning by requiring [0,p) ⊂ G for each finite boundary point p. Its actual cached definition was also read. This lane performs implementation and validation, not new literature or priority clearance. All existing review qualifications concerning unread literature and campaign novelty remain for root. Credit remains zero; root alone accepts.

Literal definitions. The original Cassinian.lean was copied byte for byte. In particular, cassinian U a b is the real sSup of the image of the actual mathlib frontier U under p ↦ ‖a-b‖/(‖a-p‖‖b-p‖), and ball U a r = {b ∈ U | cassinian U a b < r}. These are the usual Complex Euclidean norm and domain-restricted strict balls, not a boundary surrogate or a chordal norm. SourceClaim remains literally identical. Wedge.lean adds StrictlyStarlike a U := ∀ p ∈ frontier U, ∀ s, 0 ≤ s → s < 1 → (1-s) • a + s • p ∈ U. SourceClaimStrict has the same universal quantifiers and open, connected, proper, center-membership and positive-radius hypotheses as SourceClaim, with StrictlyStarlike replacing the domain's StarConvex hypothesis. Its conclusion is the same ordinary starlikeness of the ball. Thus even with the stronger domain convention the usual asserted ball conclusion fails. No assertion that a strict-witness hypothesis follows from the ordinary hypothesis is used.

Witness. Write p = u+iv. Set K = {u ≥ 1, 20v ≤ u-1, -(u-1) ≤ 20v} and U = C \ K. The theorem K_abs proves K is exactly the requested closed wedge {u ≥ 1, |v| ≤ (u-1)/20}. K is an intersection of closed half-planes, so U is open. It contains 0 and excludes 1. For w ∈ U, if bw ∈ K with 0 ≤ b ≤ 1, the inequalities imply b > 0 and w ∈ K, a contradiction. Thus U is StarConvex about 0 and path connected, hence connected.

Actual frontier. A frontier point lies in K because K is closed. If both oblique inequalities are strict it belongs to an open subset of K, which contradicts frontier membership. Conversely a point with u ≥ 1 and 20v = ±(u-1) lies in K and is approached from U by subtracting a small positive real number. Hence

    frontier U = {u+iv : u ≥ 1, 20v = u-1 or 20v = -(u-1)}.

This is the union of the rays 1+t(1+i/20) and 1+t(1-i/20), t ≥ 0, with t = u-1. Both directions are proved against mathlib frontier. If p lies on either ray and 0 ≤ s < 1, the corresponding equality and membership of sp in K would imply 1 ≤ s. Consequently [0,p) ⊂ U, proving StrictlyStarlike 0 U. The original slit is separately proved not StrictlyStarlike: p=2 and s=1/2 give the excluded point 1.

Exact estimates, checked with fractions before the analytic Lean estimates. Let y=4+i and z=2+i/2=y/2. Both are in U. Put s=Re p, v=Im p. Every frontier point satisfies s ≥ 1 and 20v ≤ s-1. Squared Euclidean norms give

    (‖p‖‖y-p‖)^2 = (s²+v²)((4-s)²+(1-v)²).

On the successive intervals [1,5/4], [5/4,2], [2,3], [3,4], [4,5], [5,∞), lower bounds for this expression are respectively

    121/16, (25/16)(4+(19/20)²), 4(1+(9/10)²),
    9(17/20)², 16(4/5)², 25.

Each is strictly greater than 153/25. For intervals ending at most 5, use s² for the first factor and the indicated real and imaginary distance bounds for the second; for s ≥ 5, s² ≥ 25 and (4-s)² ≥ 1. All these inequalities are proved by exact nlinarith certificates and the elementary product lower-bound lemma. As ‖y‖²=17, every frontier ratio is ≤5/3. The ratio image is nonempty (p=1) and uniformly bounded, so csSup_le gives c_U(0,y) ≤5/3<7/4. This does not infer a strict supremum bound from pointwise strictness without a uniform margin. The proof does not need or assert the exact optimizing frontier point or the proposed decimal extrema.

For z, every frontier point satisfies ‖p‖ ≥1 and ‖z-p‖ ≥2/5. Indeed if s≤3 then v≤1/10 and the imaginary difference is at least 2/5; if s>3 then the real difference has magnitude greater than 1. The ratios are therefore bounded above by (5/2)‖z‖. This establishes the boundedness prerequisite of le_csSup. The explicit upper-ray point p=2+i/20 gives

    ‖p‖² = 1601/400,  ‖z-p‖ = 9/20,  ‖z‖² = 17/4,
    ratio² = 680000/129681 > 49/16 = (7/4)².

Thus c_U(0,z)>7/4, so z is not in the strict ball. The Lean contradiction uses these exact squared identities, positivity, le_csSup and nlinarith; it does not depend on rounded values. The two ball facts and z=y/2 contradict StarConvex ℝ 0 (ball U 0 (7/4)).

Endpoints. Cassinian331705.Wedge.ordinary_refutation : ¬ Cassinian331705.SourceClaim and Cassinian331705.Wedge.strict_refutation : ¬ Cassinian331705.SourceClaimStrict instantiate their respective universal claims with this SAME U, center 0 and radius 7/4. All geometry, actual frontier, bounds and domain facts are proved in Lean. The plane C represents Euclidean R²; one planar counterexample suffices to refute the source's general assertion for dimensions n ≥2. No all-dimensional transport theorem is claimed.

Infinity convention. The source takes boundaries in the one-point compactification, and the ordinary Euclidean-distance Cassinian contribution of infinity is zero for finite a,b, from the limiting quotient as ‖p‖ tends to infinity. The retained infinity_contribution lemma proves that adjoining zero leaves a nonempty bounded nonnegative ratio supremum unchanged. Sanity.lean instantiates it for the wedge and y; bounded_z_wedge also permits its z instance. This is an insertion-of-zero theorem, not a formal construction of the one-point compactification. No chordal-distance substitution is made.

Validation and trust boundary. See replay-receipt.json and logs. The source-only ZIP contains Lean sources and its hash manifest. scripts/replay.py refuses to reuse a directory, rejects unsafe archive entries, checks every source hash, and strictly recompiles Cassinian, Wedge and Sanity with -j1 -DwarningAsError=true. It runs leanchecker on each and the full Audit.lean enumeration of local declarations by module origin, including generated declarations. The audit records full types, body presence (value? true), safety and partial flags, and transitive axioms; only propext, Classical.choice, Quot.sound are allowed. NegativeMidpoint and NegativeStrictSlit intentionally fail by type mismatch: they test that the y membership theorem cannot prove midpoint membership and that the wedge strictness theorem cannot prove slit strictness. They do not establish general soundness. Sanity examples check both domain memberships, excluded points, frontier samples, Euclidean norm squares, midpoint, both negations and the infinity convention.

The runner sanitizes Lean's environment, uses only pinned cached upstream oleans plus freshly built local modules, sets two-CPU affinity, CPU 120 s and wall 140 s limits, MALLOC_ARENA_MAX=2, and a systemd MemoryMax=6G scope. It samples descendant private RSS; receipts record the peak. The upstream compiler and cached pinned mathlib dependencies are trusted and are not rebuilt. Input trees are hash-bound before and after. No read-only input, shared ledger, git state, remote service, browser, or publication is mutated. No background jobs remain at handback. No bounded-domain optional extension is claimed.
