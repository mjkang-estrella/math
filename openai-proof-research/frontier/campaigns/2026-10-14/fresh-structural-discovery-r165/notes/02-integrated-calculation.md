# Prefreeze calculation: adaptive row-mass retention and final-regime demand

This is a feasibility calculation using Source171's actual final construction, not a frozen theorem or full Ramsey nominee. All pin operations are stipulated true. The complete operative source12–18 bodies were read before this detailed calculation. Source03's avoidance, calibrated injection and clock proofs were also read; its height device and the earlier source04–11 embedding branches remain unread. Primary Hall's original exchange proof, Lee's complete §2, Tikhomirov's block-embedding proof and its DRC input, Lu–Szekely's injection-dependence proof, and Haeupler–Saha–Srinivasan's distribution comparison proof were read before writing this note. Hall/HSS and the focused original-history overlap read were late relative to the first restriction idea, not prior to it.

## 1. Fix the actual low-mode experiment

Keep all source constructions and laws unchanged through a full run R: profiles, corner supports, palettes, permission tables, persistent permutation pools, calibrated cell states, finite initial resampling, terminal conditioning, late sketch tests, deletion kernels, alarms and injective late assignments. No new event is imposed on these histories.

The source uses n→∞, C_n=N/2^n→∞ with C_n≤n. In one patch/palette put M=M_i/chi_i. There are at most2M labels and L≤K M/C_n rows, with log M=n log2+o(n). There are exp(o(n)) patch/palettes. There are r=O(log n) late classes. Each tested row has at most n^{A_c+O(1)} geometric partners. All K,D,C' below are fixed source constants, enlarged finitely if needed.

On full R, the final even probability law q_v is supported on actual common neighbors of EVERY assigned odd neighbor, in its assigned palette and one cleaned corner support. Source18 equation25 and the start of its matching subsection give

    ||q_v||_infinity ≤ D/C_n,
    sup_x q_v({z: z conflicts with x}) ≤ D/C_n.                 (1)

The stronger patch-specific second bound is8K² C_n^-1 exp(-198s_i). The diagonal conflicts, so nonconflicting pairs have distinct endpoints. These are final-row laws, not uniform host laws.

Conditional on R, independently for each row draw its ordered nonconflicting pair with law

    P_v^R(x,z)=q_v(x)q_v(z) 1_nonconflict(x,z)/Z_v(R).           (2)

Source18 Proposition low-endpoint-kernels controls the joint probability, with FULL-RUN INDICATOR, of specified pairs on any t≤n DISTINCT rows:

    exp(O(r)) K^t exp(.01 n m+C'tj) product_v H_v(x_v,z_v),     (3)

where j is the geometric overlap graph's rank, m≤2j its nonisolates, H_v are deterministic symmetric nonnegative kernels fixed before endpoint values, with

    sup_x sum_z H_v(x,z)≤K/M,     max H_v≤M^-2 exp(.01n).        (4)

For nonisolates the source may use H_v=M^-2. No estimate on repeated copies of one row is asserted by (3).

## 2. Retain mass after the WHOLE run, without reweighting it

Choose deterministic0<alpha_n≤1 with

    H_n:=C_n alpha_n² →∞.                                      (5)

For EVERY full history R, let A_v(R) be any subsets of the row's palette, with q_v(A_v)≥alpha_n for EVERY row. The selection can read the entire history and all final laws. It need not be local, independent, fixed beforehand, or the same across rows. It is selected before the added pair draws, not by seeing those draws. Off full histories use arbitrary harmless fallbacks; comparisons always retain the full-run indicator.

Set a_v=q_v(A_v), q_v^A=q_v 1_A/a_v. Its conflict probability obeys

    sum_x q_v^A(x) q_v^A(Conf(x)) ≤ D/(C_n a_v)
                                ≤ D/(C_n alpha_n)=o(1),         (6)

because C_n alpha_n≥C_n alpha_n²→∞. Consequently its nonconflict normalizer Z_v^A≥1/2 eventually. Draw its nonconflicting pair, independently across rows conditional on R and the chosen restrictions. Pointwise,

    P_v^{A,R}(x,z)/P_v^R(x,z)
      = 1_A(x)1_A(z) Z_v/(a_v² Z_v^A)
      ≤ 2 alpha_n^-2.                                         (7)

Zero-probability pairs satisfy domination as well. This is a deterministic kernel inequality at fixed full history. Therefore it remains valid after arbitrary adaptive selection of all the A_v, without conditioning the original run on success of a selection. For t distinct rows it multiplies (3) by (2 alpha_n^-2)^t. The deterministic H_v, their row sums and maxima, geometric partner counts, and rank penalties stay exactly those of the source.

## 3. Pay the ENTIRE endpoint Hall sum

Choose the SAME fixed eta>0 with .02+C'eta<(log2)/2 and t0=floor(eta n). Source geometric averaging over distinct position sets is unaffected: its forest penalty is2^{-n+o(n)} per geometric edge and its correction is at most exp((.02+C'eta)nj). This is a summable geometric series. The new factor in (7) depends only on t, not on that overlap graph.

For a connected p-row endpoint diagram, the source's endpoint-identification tree, leaf integration using (4), and factorial counting give its same bound, with the single replacement

    K/C_n  -->  K/(C_n alpha_n²)=K/H_n.                         (8)

For a connected Hall-violating p-row diagram, p≥3, two further endpoint mergers leave a spanning tree and TWO edges paid with the max bound in (4). It follows that, with full-run indicator, the expected obstruction counts are bounded by

    large:  exp(O(r)) M (K/H_n)^t0,
    small:  exp(O(r)) M^-1 exp(.02n)
                       sum_(3≤p<t0) p^4 (K/H_n)^p.              (9)

All constants in K remain fixed; alpha_n's entire dependence is displayed in H_n. For the first expression the logarithm is

    n log2 +o(n)+eta n log(K/H_n),

which tends to minus infinity faster than a fixed negative multiple of n. The series in the second is bounded eventually, and its leading factor has logarithm−(log2−.02)n+o(n). Multiplication by exp(o(n)) palettes and patches still gives o(1). Sizes1/2 cannot violate Hall since pairs have distinct endpoints. Every large connected component contains a connected t0-row set. Thus no size class is omitted.

The original full run has probability1−o(1). Equations(7)–(9) show, uniformly in the adaptive restriction rule, probability1−o(1) of full completion and a matching using its retained lists. This is more than a naive concentration failure: the entire strongest source endpoint operation still closes.

## 4. Upgrade the quantifier: one run works for all retained lists

This step uses only finite adversarial selection and the preceding uniform bound. Call a full history bad if SOME family A_v with q_v(A_v)≥alpha_n has no distinct representatives. There are finitely many label subsets at each n. Fix an ordering and, at each bad history, choose its first bad family; otherwise choose the full supports. This is a measurable rule (finitely many inequalities in the q_v). If a bad history occurs, EVERY pair experiment inside its chosen family has a Hall failure. Hence its probability is at most the o(1) obstruction bound in(9). With probability1−o(1), therefore, a full history satisfies simultaneously:

    for every collection(A_v)_v with q_v(A_v)≥alpha_n,
    there is an injection f with f(v)∈A_v∩supp(q_v).             (10)

There is no union bound over exponentially many restrictions. Each choice may have a different matching; no single matching is claimed to lie in every restriction. The guarantee concerns the constructed row masses, not absolute/relative host cardinalities or a deleted-edge degree bound.

## 5. Pay a stronger classical consequence: many representatives per row

A uniform multiplicity conclusion for these same final lists does not require pretending that (3) allows repeated rows. The following elementary random-thinning argument avoids that invalid substitution.

Suppose finite probability laws q_v satisfy(10), have max atom≤u, and0<alpha≤1/4 with u/alpha≤1/8. For a nonempty family S of rows let T be the union of their supports. If |T|<|S|/(4alpha), retain each label of T independently with probability2alpha, obtaining T'. For v∈S,

    E q_v(T')=2alpha,
    Var q_v(T')=2alpha(1−2alpha)sum_x q_v(x)²≤2alpha u.

Chebyshev gives P(q_v(T')<alpha)≤2u/alpha≤1/4. Write G(T')={v∈S:q_v(T')≥alpha}. Then

    E(|G(T')|−|T'|) ≥3|S|/4−2alpha|T| > |S|/4>0.

Some T' therefore has |G(T')|>|T'|. Set A_v=T' for those good rows, intersecting supports if desired, and A_v=supp(q_v) for the others. This violates(10) by Hall. Consequently

    |union_(v∈S) supp(q_v)|≥ |S|/(4alpha) for EVERY S.           (11)

For any integer b≤floor(1/(4alpha)), apply Hall to b formal copies of each row. Any collection of copies uses some S of original rows and contains at most b|S| copies, while its union of candidates is at least that large by(11). It admits distinct representatives for all copies. Formally distinct equal sets are explicitly allowed in Hall1935, printed p27. Demand numbers varying by row, each between0 and b, follow by discarding excess copies.

Applying this with u=D/C_n and alpha_n=1/(4b_n), any integer sequence b_n→∞ with b_n=o(sqrt(C_n)) meets(5) and u/alpha_n→0. Thus the actual low-mode completed lists admit b_n distinct representatives per even role, all hitting its ORIGINAL odd neighbors. One example is b_n=floor(C_n^(1/3)/8), eventually positive. This is a final-regime feasibility consequence, not a full Ramsey theorem for a different target.

## 6. High modes and the boundary of the integrated calculation

The complete source15 high-mode proof supplies mass≥1/2 and nth moments K^n for normalized column averages, retaining all stage gates. Choose a FIXED average threshold D0>4K; the union bound N(K/D0)^n≤n2^n(K/D0)^n tends to zero. Thus one successful history has every normalized even column≤D1/C_n after row normalization, with fixed D1. Restricting each row to arbitrary mass≥alpha multiplies columns by at most1/alpha, even when restrictions read the entire history. If C_n alpha→∞ the fractional Hall criterion already completes all such restrictions. Likewise b_n demands with b_n=o(C_n) have column capacity≤1 eventually. No new high-mode construction is needed.

This accounts for ALL final modes of the READ source12–18 construction: high via its existing fractional loads, low via its existing pair kernels plus(7)–(11). Exact-marginal local avoidance is also already provided by source16's two calibration propositions; it is not an additional sampler claimed here.

What remains unpaid is a DIFFERENT, global premise. Deep discrepancy and the measured patch alternatives in source12–13 are obtained earlier by excluding monochromatic ordinary Q_n in BOTH colors. An absence assumption for a different target, such as a one-side replicated cube, does not imply absence of Q_n. The existence of robust final lists does not transfer that premise. Every earlier available-bias/purity/broad/key-grid/cluster/linear-budget alternative would have to produce the new target with the same arbitrary slow C_n divergence, OR a different reduction would have to reach these final hypotheses. Those source04–11 operative proofs have NOT been read in full here and no compatible full transfer has been supplied. This is not an assertion that their transfer is impossible, nor that the low-mode matching step is still missing.

Nor does(10) turn host-cardinality or per-vertex edge deletions into row-mass preservation. Even a tiny host set can contain an entire concentrated row support. A cardinality-to-mass or prechosen-host adversary claim needs its own paid uniform estimate and the appropriate earlier reductions. No such full conclusion is frozen.

## 7. Strongest-reduction and history comparison

Hall's original theorem already permits repeated sets; the b-demand conversion is classical. The thinning calculation uses only variance and a positive-expectation argument. Kernel conditioning(7), the source's complete Hall diagrams, and finite adversarial selection pay the mass-retention result. The needed independence is solely the new pair draws conditional on R, and the separate auxiliary Bernoulli selector in(11); no independence is assumed for the final q_v themselves.

Lee2017 §2 prepares one side by DRC and then orders the other side by inverse-neighborhood defect. It accommodates extra candidates through its existing threshold/greedy step; its density cost remains alpha_density^-d, so it is not an automatic linear-order prerequisite for a new cube target. Tikhomirov2208.14568v3 Lemmas5.4/5.5 sample distinct blocks and inject inside facets, then ensure2^{n−1} common neighbors and finish greedily. Changing that last threshold alone is a classical transfer; it does not remove its earlier quantitative host requirements. His Proposition6.3 provides actual structural alternatives but the uninspected standard-pair/dispersion inputs are not treated as a complete transitive proof.

Completed I60 §7.2 already records simultaneous candidate-deletion resistance paid by source compression/Hall slack. Its full rooted edge-deletion target in §7.1 is refuted at its unchanged scope. The present probability-mass argument is not a renamed repair, and neither its restrictions nor its full old quantifiers are substituted. r32's multicolor and r48's ternary-grid scopes remain unchanged. No perfect history clearance or worldwide novelty claim follows.

These are durable prefreeze calculations. They identify no indispensable new nonroutine full operation beyond the strongest source/classical reduction, and do not submit an unproved blowup/resilience bridge as a finding. No correctness/contribution/acceptance/count grade is assigned.
