# I247 — explicit quantitative complete-witness scalarization

**Verdict: candidate worthy of independent proof and contribution gates for quantitative scalarization; the requested quantitative disk-rigidity extension remains unresolved.** No acceptance or count change is made. The user raised the target to twenty on 2026-10-12; the supplied accepted count is ten.

The completed result is a positive-deficit strengthening of R016's coefficient-channel conclusion. It is not a nonattained-supremum extension or a compactness modulus. The proof is in [analytic-attempt.md](../experiments/i247_quantitative_complete_rigidity/analytic-attempt.md), including early notes, explicit constants, counterexample attacks and the unpaid geometry step. [Reading and failures](../experiments/i247_quantitative_complete_rigidity/reading-and-failures.md) and [literature](../sources/i247_quantitative_complete_rigidity/literature.md) give the bounded source record.

## Exact completed result

Let d>=2, K=W(A) subset R Dbar have interior, and assume dist(sigma(A),partial K)>=delta>0. Suppose partial K has a regular analytic arc of length at least ell>0 on which the top support eigenvalue is simple with gap at least g>0. Put

    C0=8(d-1)R (3R)^(d-1) delta^(-d)
                     [9pi R^2/(g ell)+1/sqrt(6)].

For every finite coefficient size m and every finite-degree matrix polynomial P with max_K||P||=1 and ||P[A]||>=2-epsilon, 0<=epsilon<=1/2, every unit maximal singular pair x=vec X,y=vec Y has squared Schmidt tails

    1-||X||op^2, 1-||Y||op^2 <= C0 sqrt(epsilon).

There are constant unit coefficient vectors u,v such that the original witness has a scalar compression p=v*P u satisfying

    max_K|p|<=1,
    ||p(A)||>=2-epsilon-6C0 sqrt(epsilon).

The base/coefficient tensor vectors are within sqrt(2C0)epsilon^(1/4) of products. The estimate is uniform in degree, coefficient size and polynomial coefficient norms; no bound on those quantities is needed. The spectral parameter is distance from the spectrum to the numerical-range boundary, not separation of distinct eigenvalues. No inverse-polynomial condition is assumed. A full-range normalized active-block version is proved too.

This includes a genuine dimension-four class: the irreducible Crabb chain with weights (sqrt2,1,sqrt2) has W(A)=Dbar, support gap 1/2, boundary spectral distance 1, and exact polynomial witness z^3. Its controlled neighborhoods supply nontrivial positive-deficit classes. This known chain is only a nonvacuity check, not a claimed discovery.

## Proof-bearing increment

The pinned complete certificate gives integrated block slack <=S and ||X*Y||HS^2<=S/6, with S<=64R^2[(3R)^(d-1)/delta^d]^2 epsilon. On a simple-support arc the original positive field has rank d-1. Weighting by the square of the exterior boundary speed converts arc length into a pointwise hyperplane compression estimate without assuming a lower conformal-derivative bound. Interlacing then bounds the second positive and negative eigenvalues of D=XX*-YY*. A minmax argument retaining the small overlap ||X*Y|| controls the second eigenvalues of XX* and YY*, hence both Schmidt tails. Finally, the two singular-vector equations cancel the first-order error when replacing both vectors by their leading Schmidt products. That cancellation improves the scalar ratio loss from a naive fourth root to a square root.

This is the proposed contribution, not the inherited residual, qualitative support-rank argument, finite-level compression or old scalar rigidity theorem.

## Attacks, limits and precise remaining question

The explicit stadium family in the analytic proof has d=4, uniformly bounded degree-one coefficients, fixed interior spectral separation and ratio tending to two, but maximal singular pairs with both Schmidt tails 1/2 while the support gap collapses. Thus omitting g cannot give a uniform estimate for **every** maximal pair. This does not refute the existence of some scalar compression and is not separately nominated as a substantial finding.

The weighted-chain (1,2,1) example still rules out scalar-style nilpotent output rigidity for P[A]. Disk-contained reducing summands rule out classification of all of A by one active block. Unused coefficient channels rule out approximation of the entire matrix polynomial by a scalar channel. Q1–Q4 assert none of those false conclusions.

A bound for inf_{a,rho>0} d_H(W(A),a+rho Dbar) is **not proved**. Scalar near-equality after compression permits old quantitative nilpotent approximation of p(A), but transferring this to A fails at critical spectral values. Jin's full scalar proof uses exact rational collapse, full-level lemniscate identification, and exact algebraic divisibility/contact counting. The needed robust versions are not available here. The analytic note states a precise remaining target with r,R,delta,g,ell,degree and coefficient bounds; it is not represented as a theorem.

## Prior art and assessment boundary

[ACV v3](https://arxiv.org/html/2608.27346v3), Sections 5, 7, 9 and 11, supplies exact Schmidt orthogonality, low-dimensional complete rigidity, scalar/tuple output stability and scalar equality classification. [Jin v2](https://www.preprints.org/manuscript/202609.0079/v2) supplies scalar disk rigidity and its full algebraic argument. R016 already supplies the exact original-field isotropy mechanism. None of the inspected statements gives the displayed quantitative coefficient recovery for the specified complete witness. This is a bounded prior-art comparison, not a claim of worldwide priority. The completed theorem uses only stipulated pinned operations, the finished boundary-limit argument and elementary inequalities proved in the note; external scalar theorems are not needed for its proof.

The actual [MathDB complete Crouzeix problem 392465](https://mathdb.com/p/392465/complete-crouzeix-conjecture) was accessible and relevant. No numerical significance metric is asserted. Details of the stale progress text and access scope are recorded in the literature note.

Independent reviewers should decide whether quantitative scalarization alone meets the substantiality threshold. If the proposed finding must also contain quantitative disk geometry, this attempt remains technical progress and the target is unresolved. Neither review is replaced by this self-assessment.

## Written artifacts and authentication

- `frontier/iterations/i247-quantitative-complete-rigidity.md` — this report.
- `frontier/experiments/i247_quantitative_complete_rigidity/analytic-attempt.md` — full proof and precise unproved geometry bridge.
- `frontier/experiments/i247_quantitative_complete_rigidity/reading-and-failures.md` — reading extents, rejected approaches and operational record.
- `frontier/experiments/i247_quantitative_complete_rigidity/input-authentication.json` — detached input/source/output hashes; its own detached digest is returned to the parent.
- `frontier/sources/i247_quantitative_complete_rigidity/literature.md` — source contracts, prior art, MathDB and access limits.
- Six fully read primary excerpt copies in that source directory, indexed by the authentication JSON.

No subagents, live sibling reads, shared-state edits, research code, tests, numerical experiments, scans, snapshots, staging, commits, publication or public communication were performed. Unrelated work was preserved.
