# Full weighted-selection conjecture: unresolved; composition route has a public subsumer

Credit 0. Assigned target only: Zhang, arXiv:2608.28007v2, Conjecture 7.2. For every integer d>=2 and 1<=k<=d-1,

    F_w(d,d+k)=1+Gamma(d,k),
    Gamma(d,k)=max_{k+1<=s<=d} (s-k)/min_{r_1+...+r_s=d;r_j>=1} sum_j 1/r_j.

F_w uses every finite multiset of real feature/label pairs, at most d+k effective selected rows, positive weights on that support (normalized without changing the fit), full-data uniform risk, and the Euclidean minimum-norm ERM. The stated zero-optimum conventions remain in force. Our experiments impose SPD full covariance and positive optimum; they do not cover every dataset in the source. Actual cached v2, including the setting, source lower bound, H.1, G.2/G.4, and Appendix K, controls; (4,6) is already public. Read the entire prior r24 discovery and checker. No source parameter instance, label transformation, helper or normalization receives credit.

## Early source screen changes the concrete route

Live public search located Liu–Wang, **Weighted Data Selection: Sharp Upper-Half and Five-Dimensional Laws**, https://arxiv.org/abs/2610.00101 and https://arxiv.org/html/2610.00101v1. The actual body was saved and read: Theorems 1–2; Appendix B.1–B.6, including the circuit realization/comparison lemmas, shared-root classification, circuit-plane graph and transfer; D.5. Theorem 2 states the unrestricted weighted minimum-norm value at (5,6) is 11/5, with span-preserving approximations and arbitrary finite evaluation weights. Theorem 1 covers ceil(3d/2)<=n<=2d-1. The remaining intermediate family is explicitly left open. B.6 handles nonzero zero-residual features by a penalty anchor and uses residual-dependent masses otherwise. This is a same-object subsumer of the proposed composition route, not an abstract-only lead. No formal certificate was replayed and no blanket correctness audit is claimed. The displayed primary metadata says v1 submitted 8 September 2026 despite the 2610 identifier; preserve that anomaly rather than silently repair the date. In either case the observed public body predates this lane's work.

Latest target abs bytes match the prior cached observation exactly. The current vector-valued companion v2 was fetched and its scalar/multi-output statement and theorem map read; it does not state the remaining full scalar conjecture. Classical nearest bodies were inspected in the hash-verified r24 cache: positive-basis critical-block/near-extreme-size classification, volume sampling, AIM quantitative Steinitz, and the OpenAI Gaussian-regression endpoints. Positive-basis normal forms do not themselves control the full risk metric; averaging volume-sampled fits does not ensure one weighted ERM on d+k rows. Neither is claimed to prove the remaining family. Dewasurendra's actual body remains an inherited gap.

## General residual labels: exact reconstruction

Let V have rows v_i in R^3, positive rational full-data masses p_i summing to one, and residual labels e_i satisfying V^T diag(p)e=0. Let

    L=sum p_i e_i^2>0, H=sum p_i v_i v_i^T>0, M=H/L.

The full optimum is zero and the ratio at u is 1+u^T M u. The selected objective weights alpha are independent of p. An invertible triple B interpolates V_B u_B=e_B irrespective of alpha>0, so x=min_B u_B^T M u_B.

For a rank-three four-row support T, choose nonzero h in ker(V_T^T) and C=-h^T e_T. Deleting row i with h_i!=0 gives u_i; its residual is (C/h_i) times coordinate vector i. For alpha>0 the output is

    u=sum_i lambda_i u_i, lambda_i=(h_i^2/alpha_i)/sum_j(h_j^2/alpha_j).

This follows directly from alpha_i residual_i being proportional to h_i and the normal equations. If h_i=0 that row interpolates throughout; if C=0 all adjacent interpolants coincide. Every strictly positive lambda is attainable and the entire convex hull is its closure. Thus y is the minimum M-norm over all these hulls, with triple supports included. Enumerating their affinely independent faces and solving rational KKT systems gives the exact infimum. A singular face KKT system cannot lose an optimum: remove affine dependencies until its positive-support representation is affinely independent. These are known linear-algebra reductions, independently checked here, not new results.

When all e_i are nonzero, put a_i=v_i/e_i and mu_i=p_i e_i^2/L. Then sum mu_i=1, sum mu_i a_i=0 and sum mu_i a_i a_i^T=M. Training weights transform by beta_i=alpha_i e_i^2. Consequently arbitrary nonzero residual labels are equivalent to equal labels with **changed masses and metric**, not to the old uniform-mass probes. Sign-changing labels cause no problem because the transformed masses use squares. A zero label with a nonzero feature contributes to M and cannot be discarded. The source's penalty anchor is the relevant mechanism there.

Twenty exact profiles were tested, with seed29102602: three circuit examples, fifteen projected-residual systems of five/six/seven rows (including repetitions), and two zero-label-anchor examples. All satisfy the normal equations and SPD/positive-risk hypotheses; all pass the facet, with maximum6 on the symmetric simplex. 275 independent positive-weight normal-equation identities and 17 label/mass transforms pass. This is finite evidence only. Projection of a random response onto the weighted residual kernel is rational, not numerical least squares. No stochastic optimizer or tolerance is used. Rank-deficient selected supports are not reported as optimized in these component profiles.

## Every support and the large-shift issue

For an orthogonal 2+3 direct sum with residual-energy fraction t assigned to the 3D component, full-rank supports at budget6 must allocate at least two and three rows respectively. The only undominated allocations are (3,3) and (2,4); (2,3) is dominated. Hence the full-rank excess infimum is

    min(t*x, 2*(1-t)+t*y).

For 0<=y<=2/3 and x>=y, its maximum over t in [0,1] is 2*x/(x+2-y), attained at t=2/(x+2-y). The denominator is positive, and this exceeds6/5 exactly when 2*x+3*y>6. The y bound is the public 3D four-point theorem (the weighted extension follows by rational replication and uniform equivalence of positive covariance quadratic forms). This explicitly checks the intersection lies in [0,1]. If x=0 the value is zero.

Here is the finite-span argument needed before turning such a strict violation into a source counterexample. In the original coordinates let H_total>0 be the evaluation covariance and L_total>0 the residual energy. There are finitely many proper spans W of selected feature subsets. Choose z outside their union: a polynomial curve (1,T,...,T^(d-1)) avoids each proper span except at finitely many T, because a nonzero annihilating linear functional gives a nonzero polynomial. Thus one integer T avoids all of them. Put

    delta=min_W min_{w in W}(w-z)^T H_total(w-z)/L_total >0.

For the shifted dataset with optimum A*z and labels e_i+A*v_i^T z, any minimum-norm selected output belongs to its selected feature span W. Every rank-deficient selection, whatever its positive weights, therefore has excess at least A^2 delta. Choose A with A^2 delta greater than the proposed full-rank value. Full-rank outputs merely translate and retain the original profile. This proves a global lower bound over all deficient supports without asserting that whitening preserves minimum norm. Rational full-data masses are represented by repetitions; for nonrational masses a strict violation persists under sufficiently small rational perturbation because the set of full-rank outputs is fixed and positive covariance forms are uniformly equivalent. Thus a genuine strict facet violation would contradict the public Theorem2. Conditional on that theorem, the entire proposed facet route is already excluded, including asymmetric labels and zero-label anchors. This deduction is a routine same-object consequence, not a discovery nomination.

## A second structural route, and its missing step

To avoid stopping with a failed probe, reconstruct a general circuit-anchor game. This is an uncredited extension of the already public circuit/quotient method, not a claimed solution.

Work first with a finite equal-label root system a_i in R^d, positive masses mu of mean zero and covariance I. A circuit is a minimally supported positive zero relation. Let an anchor set S positively span its own span P and have nullity |S|-dim(P)<=k. On P-perp consider the bounded polytope

    Q_P={z in P-perp: a_i^T z<=1 for every i}.

It has zero in its relative interior: the original roots positively span R^d. Express zero as a convex combination of its vertices. Each vertex has d-dim(P) independent active quotient rows. Its anchor evaluations are zero and these active evaluations are one. Positive anchor balancing weights and arbitrary positive interpolating weights give an actual full-rank selected normal equation at that vertex using at most d+k rows. Normalize weights afterward.

For a circuit B with normalized coefficients beta, project onto P-perp, discard zero projections, and decompose its positive relation into projected circuits. If r=dim(P_B)-dim(P_B intersect P), every projected circuit has at most r+1 roots. Under the mean-zero vertex distribution each evaluation T_i has mean zero and satisfies T_i<=1. The pointwise circuit relation gives T_i>=-(1-alpha_i)/alpha_i on a normalized projected circuit. Averaging (T_i+(1-alpha_i)/alpha_i)(T_i-1)<=0 gives E T_i^2<=(1-alpha_i)/alpha_i. Summing alpha_i yields cost at most r. The discarded mass only reduces this bound. Decomposing the original mu into normalized circuits therefore shows that a probability theta on eligible anchors would give excess at most

    max_B sum_S theta_S [dim(P_B)-dim(P_B intersect P_S)].

A universal bound of this game by Gamma(d,k), with zero-label penalty and deficient-rank transfers, would suffice for the full conjecture. **No such bound is proved.** Not every abstract subspace family is realizable as the entire positive-circuit family of a root system; ignoring the additional circuits loses exactly the geometry needed. The proof does not establish that this game is sharp, or that a suitable theta always exists. Sign-cone outputs can improve on anchor outputs, so failure of the game bound would not refute the source. The low-rank graph calculation in the newly located paper is an existing special case of precisely this method. Rebranding that calculation or the label transform would fail substantive eligibility.

## Strongest objection, falsifier, and remaining gap

The immediate strongest objection is actual public same-object Theorem2, not a numerical search failure: any proposed strict facet witness must either expose an error in that theorem or fail one of the reduction hypotheses. Our exact probes expose neither. They cannot establish its correctness or the full conjecture. A valid source falsifier still requires some admissible (d,k), a finite dataset, and an exact lower bound over **all** selected supports and weights, including min-norm deficient selections. No such witness exists in this packet.

The remaining full-scope gap is the universal sparse weighted-risk bound below the public upper half, with arbitrary coupled circuits, zero labels, all observed ranks, and every budget. The anchor-game strategy is only a sufficient target. No ordinary full proof, source refutation, Lean investment, PROOF.md, acceptance request, or count change. Counts remain5/30 additional,35/60 total.

## Bounded registry coverage

All five inherited complete tree files were rehashed against r24's recorded provenance, with entries12478/1541 (Omega subtrees),13578 (OpenAI preprints),183 (Count),3541 (AIM), each nontruncated. The associated live-head observation is09:05UTC29October, not a newly obtained head. Its API403 is preserved and was not retried through API, connector or raw-host substitutes. No 1000-entry listing or stale snapshot is called novelty clearance. New public search, arXiv bodies/metadata, and clopen weighted-selection query were observed at09:21UTC. Clopen bytes equal the earlier query. Registry full-text coverage remains incomplete, and current heads after09:05 are unknown. The material is sufficient to identify the concrete public subsumer, not to certify absence of a full conjecture proof anywhere. Fenner remains excluded by Jin's14October proof; no old accepted family is reopened.
