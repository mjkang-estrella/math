# 083: measurable truncation selection — pre-freeze, no nominee

Myeongjin Kang, no affiliation. Original prose CC BY4.0. No scope was frozen; no full theorem or independent verdict is asserted.

The full question studied is whether there are absolute a∈(0,1/2), C<∞ such that every Lipschitz v:R²→S¹ with Lip(v)≤1 and every complex Schwartz f satisfy

    || sup_{0<ε<a} |∫_{ε<|t|<a} f(z−tv(z)) dt/t| ||₂ ≤ C ||f||₂.       (M)

The direction is frozen at the output point, not followed along its flow. No restriction to one-coordinate fields, one frequency annulus or fixed cutoff is substituted. Measurable selection over finitely many positive cutoffs is equivalent to the corresponding finite maximum bound; continuity of the truncated integral for Schwartz inputs then permits rational cutoffs and monotone convergence. Initially variation was also considered; the operative source check selected (M) as the concrete baseline before any target freeze or claimed proof. A variation theorem is not claimed.

Pinned source083 thm:main puts the supremum OUTSIDE L². Its prose expressly distinguishes this from a maximal assertion and only states pointwise principal values on Schwartz inputs, followed by an L² extension. The source is accepted as true; its stronger lower operations are also credited. In particular:

* red:scale-truncation supplies a uniform L¹ kernel error for each fixed pair of time endpoints.
* red:packets and eq:src-3 allow arbitrary finite deterministic tile subcollections, a smooth scalar selector b_s,j(u), and one common Hilbert-valued input/test.
* conc:coefficient-carleson uses point-dependent but monotone scale selection |u(z)−t|≤w/ℓ_s, controlled by separated interval synthesis.
* red:composition-commutator and red:integrated-commutator pay O(|t|) and O(a) for vertical frequency reassembly of fixed-cutoff operators.
* assembly:all-model-estimates pays the full source phase/hierarchy gain on its specified forms. No assumption that this gain automatically survives new output-dependent selectors is made.

The useful positive result of this screen is the selected main-coefficient Carleson estimate proved in coefficient-lemma.md. A spatially varying lower cutoff does not destroy the monotone-interval argument: it intersects a prefix with a suffix. This is a technical consequence of the source synthesis lemma, not a substantial new finding or a full band theorem.

The separate obstruction in commutator-obstruction.md is exact: even at constant direction, a two-valued measurable cutoff can create a vertical commutator with norm at least1/8, independent of outer length a. Thus the source's O(a) small-time commutator cannot simply be applied after maximal selection. Constant-direction maximal Hilbert transforms are nevertheless bounded; the example refutes that particular proof step, not (M).

There are three unpaid tasks, none replaced by an added hypothesis:

1. Carry selected scale coefficients through the entire ordinary/popular forest, hierarchy and interpolation without losing the logarithmic restricted gain. The main-coefficient lemma alone does not verify all those steps, and variation selections would allow multiple intervals with coefficients rather than just one interval.
2. Reassemble all vertical frequency bands while retaining maximal selection. The explicit rough-output-multiplier commutator prevents the literal fixed-cutoff proof. A vector-valued or off-diagonal argument capable of retaining the selection is needed; none is supplied.
3. Pass from smooth scale partial sums to arbitrary hard time cutoffs. The fixed L¹ error is not a maximal error estimate. Rounding ε within one dyadic annulus costs an average of |f| along the frozen direction; taking its supremum introduces the directional averaging maximal problem rather than resolving it.

Neither source truth nor the positive local coefficient bound pays these tasks. The full (M) remains unproved and unrefuted here. No narrowed variant is nominated, and no formal/manuscript escalation is proposed.
