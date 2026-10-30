# Unresolved: the full weighted-selection risk conjecture

Credit 0. No full ordinary proof, source counterexample, Lean certificate, acceptance nomination or PROOF.md. Counts stay 5/30 additional and 35/60 total. This lane concerns convex geometry of positive spanning sets and weighted selection, disjoint from the prohibited cascade, Fenner, Tao and Vígh families. All writes are local to this lane.

## Exact source and revision reconciliation

Guangjian Zhang, *Exact Risk Ratios for Weighted Data Selection in Linear Regression*, arXiv:2608.28007v2, revised 2 October 2026; original v1 submitted 28 August 2026. Read the actual v1 and v2 statement bodies, v2 §§2,4,5,6,7 and Appendices G, H and the relevant I/K/L material. The target is v2 **Conjecture 7.2**, not a stale conjecture label in v1 (Conjecture 10.54).

For every integer d>=2 and 1<=k<=d-1, it asserts

    F_w(d,d+k) = 1 + Gamma(d,k),
    Gamma(d,k) = max_{k+1<=s<=d} (s-k) / min_{r_1+...+r_s=d; r_j>=1} sum_j 1/r_j.

Here D is an arbitrary finite multiset of pairs (x_i,y_i) in R^d x R; the selector sees the entire dataset, selects at most d+k effective examples and nonnegative weights summing to one; the learner returns the *Euclidean minimum-norm* minimizer of that weighted squared-loss objective. F_w is the supremum over D of the infimum of full-data loss ratios over selections. Zero-loss conventions are 0/0=1 and c/0=infinity for c>0. Repetitions merge and zero weights do not count. There is no general-position, positive-definite-covariance or positive-optimum restriction in the source conjecture.

The balanced inner minimum has q=floor(d/s), a=d mod s and value (s-a)/q+a/(q+1). No closed formula simplification of Gamma or fixed-cell calculation is claimed as a discovery.

**Public-scope exclusion established early:** v2 already proves F_w(4,6)=3/2, actual Theorem H.1 and full proof. It reduces rank<=3 to exact recovery, handles zero optimum and zero-gradient anchors, then treats minimum positive-basis sizes <=6, 7 and 8. The size-seven branch uses triangle/quotient geometry; the size-eight branch uses four orthogonal lines and two canceling pairs. Thus the v1 “smallest open cell” is obsolete. The full line n=2d-1, cells (3,4), (4,5), (4,6), lower bound in every cell, and exact orthogonal circuit-block class are all public and excluded. The current smallest stated open cell is (5,6), predicted 11/5. Resolving only that cell would not satisfy this lane's full-family mission.

Primary URLs:
- https://arxiv.org/html/2608.28007v2
- https://arxiv.org/html/2608.28007v1
- https://arxiv.org/abs/2608.28007

## Independent reconstruction and exact falsifier attempt

Take rational row vectors v_i in R^3, with sum_i v_i=0, spanning R^3, and labels all equal to 1, with uniform full-data masses. Put M=N^-1 sum_i v_i v_i^T. Then M is positive definite; the full-data optimum is u=0 with loss 1, and loss at u is exactly 1+u^T M u. This verifies the normalization without numerical matrix square roots. A whitening change transports this quadratic metric to Euclidean geometry, but it does **not** transport the min-norm tie rule unchanged. Accordingly all computed profiles concern strictly convex selections only.

At budget 3, each independent triple interpolates its three labels. Its optimum is independent of its positive weights. Enumerate triples B and solve V_B u_B=1; x=min_B u_B^T M u_B is the optimal strictly convex excess with three points.

At budget 4, for each full-rank four-row support T, let h span ker(V_T^T). Deleting i with h_i!=0 leaves a basis and interpolation point u_i. Write C=-h^T 1. Then V_T u_i-1=(C/h_i)e_i. A convex combination u=sum lambda_i u_i has residual components C lambda_i/h_i. Weighted stationarity is diag(alpha)(V_Tu-1)=mu h, so lambda_i is proportional to h_i^2/alpha_i. Thus every strictly positive barycentric combination is realized by positive objective weights; boundary points occur as limits. The h_i=0 rows interpolate throughout. If C=0, all adjacent interpolation points coincide. This rederives the source's Lemma G.2; it is classical linear algebra, not a new theorem.

For each support, minimize u^T M u over that convex hull. The checker enumerates all its faces, solves the equality-constrained Gram KKT equations, and keeps nonnegative barycentric solutions. An optimum has an affinely independent active subset, so singular larger face descriptions do not prevent finding it. This gives y, the optimal four-point strictly convex excess, with exact rational arithmetic. Basis supports are included. It does not optimize the true rank-deficient min-norm branches of the unshifted data.

The full profile-domination route would in particular require

    2*x + 3*y <= 6

for **every** energy-normalized three-dimensional system. Source Appendix K gives this necessary intermediate inequality for composing a two-dimensional simplex component with an arbitrary three-dimensional component. Re-derivation: let t be the residual energy assigned to the three-dimensional component. Spending the one extra point on the two-dimensional simplex gives excess t*x; spending it on the three-dimensional component gives 2*(1-t)+t*y. For x>=y>=0, the maximum over t in [0,1] of their minimum occurs at t=2/(x+2-y) and equals 2*x/(x+2-y). This is <=6/5 iff 2*x+3*y<=6. Even proving this all-system facet would settle only that composition subclass, not the full five-dimensional cell or full conjecture.

Exact probes: standard simplex gives (x,y)=(3,0), facet=6. Symmetric three-axis system gives (1,2/3), facet=4. Twenty-four fixed-seed five-row mean-zero systems give no violation. The checker records their rows, all rational profiles, basis counts and face counts. These are a narrow finite family, not a universal argument or novelty evidence. Inputs with singular support triples are handled by ignoring those triples; no determinant tolerance is used.

## Failed methods and precise missing universal step

1. **Independent endpoint bounds do not give the profile facet.** The public bounds x<=3 and y<=2/3 yield only 2*x+3*y<=8. The formal pair (3,2/3) exhibits the logical weakness of those two inequalities, but it is not asserted to be realized by any system. A quantitative tradeoff depending on the same data is missing.
2. **Circuit decomposition is insufficient.** Classical positive-basis decompositions describe positive dependence and quotient ranks, not domination of the loss profiles with the correct metric and residual energies. Source Proposition I.1 explicitly already blocks naive disjoint low-dimensional circuit covers. No replacement reduction controlling arbitrary cross-flat features was found.
3. **Whitening does not remove tie-breaking.** A rank-deficient selected objective can return u=0 merely because the current optimum is the origin. Such a case cannot validate the worst-case full-rank profile bound. The source's generic large-shift method handles this issue using finitely many bad feature spans; it is a public reduction, not a new counterexample mechanism.
4. **Finite convex hull computations do not prove a uniform profile inequality.** The parameter spaces include arbitrarily many rows, nonuniform masses, varied residual labels, degenerating supports, arbitrary dimension and every intermediate budget. The current diagnostics cover none of these universal limits.

The missing all-scope theorem is a loss-profile domination/completion statement for *every* positive-spanning gradient configuration, including gradients outside a minimum positive basis. Neither an ordinary proof nor a falsifying legal dataset with a certified global lower bound over all supports and weights was obtained. No broad optimizer sweep or large enumeration was performed.

## Classical subsumption objection, at full strength

The strongest objection to any future elementary proof is that **Davis/McKinney positive-basis structure + Cornaz–Kerleau–Royer ear decomposition + standard volume-sampling interpolation bounds + convex-hull/Cauchy–Binet normal equations may already imply precisely the needed profile domination**. Merely rediscovering its two-circuit or block specialization, or proving one more parameter cell, would fail this campaign's substantive gate. Cornaz et al., arXiv:2411.08994v2, actual §5 critical-block characterization (Theorem 5.2 and proof) and nearly extreme-size discussion were inspected: these concern positive-basis structure; no full loss-profile bridge was established here. This is not a claim that no such bridge exists elsewhere.

Dereziński–Warmuth arXiv:1705.06908v1 actual Theorem 5 states expected full loss under size-d volume sampling is (d+1)L* in general position and bounded by that otherwise; §4.1 uses the leave-one-out determinant identity. Its Theorem 8 averages k independent size-d interpolants for factor 1+d/k. The average is not automatically the minimum-norm weighted ERM on a d+k support, and the union can use kd points. Thus that theorem alone does not close the exact intermediate-budget question. The general positive-basis classifications are classical dependencies and receive no credit.

## Current prior-proof screen and chronology limits

Before investment, live heads and untruncated complete trees were obtained/reconciled for Omega D5 (12,478 entries) and Problems (1,541), OpenAI preprints (13,578), Count-ex-machina (183), and AIM (3,541). See coverage.json and http-log.json. The AIM tree fetch hit API403; requests to that API stopped. The freshly observed AIM head exactly equals the saved full-tree commit, so its complete bytes were verified and reused, preserving the failure. No 1,000-entry contents listing was treated as complete. Omega coverage concerns those two subtrees, OpenAI coverage its preprints subtree; neither is a claim of whole-root full text.

Path terms: regression, data-selection, positive-basis, positive-spanning, Steinitz, 28007, Hanneke and Dewasurendra. Actual AIM problem564 is quantitative Steinitz retained-ball radius, not the weighted regression statement. Actual OpenAI memory/precision endpoint proof and posterior-replica model body concern online finite-state noiseless Gaussian regression, with memory/sample tradeoffs and no row selection; neither inspected body supplies the conjectured exact finite-data risk profile. Count had no matching target path. There is no body-wide registry clearance claim.

Live clopen homepage and query results for regression/weighted selection were saved: the regression result is ordinary posterior contraction with neural-network priors; weighted-selection query returns no records. This is bounded query coverage, not evidence of mathematical novelty. The Fenner exclusion from Jin's 14 October original AIM commit is accepted as decisive and never reopened. Existing accepted 35 outcomes, prior exclusions and recent fresh geometry/probability lane summaries were reconciled before this target; no matching older campaign target was found in the inspected records. Search-engine results and badges are leads only.

Actual v2 primary theorem scope, not its abstract, excludes (4,6). All chronology claims refer to recorded primary version metadata. No journal version of the target is asserted. The guessed PMLR original-paper PDF URL returned404 and is preserved; the actual older arXiv original body was read instead. The Dewasurendra paper and vector-valued companion were not body-read, so those closest-companion gaps remain HOLD. No worldwide priority, journal-source PASS, final novelty clearance, or exhaustive specialist database search is claimed.
