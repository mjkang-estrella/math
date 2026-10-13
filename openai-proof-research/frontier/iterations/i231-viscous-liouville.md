# I231 — viscous anisotropic Liouville bridge

**Verdict: the finite-positive-viscosity theorem remains unproved here; no substantial finding is nominated.** The exact infinite-viscosity PDE-plus-fit claim is false. The completed partial argument identifies a narrower unpaid contact principle and an independent unpaid local regularity estimate. Neither is replaced by an assumption of globally bounded gradients.

For every m>=1, tau>0 and C0<infinity, the sought statement concerns continuous entire viscosity solutions of

    G_tau[V] := V_tt+2 DxV·DxV_t+DxxV[DxV,DxV]+tau Delta_x V = 0

with, at every center (x,t) and every R>0, some p,a satisfying

    |V(x+h,t+l)-V(x,t)-p·h-(a-|p|²/2)l| <= C0 R
    whenever |l|<=R and |h-pl|<=R.

All upper C² tests satisfy G_tau>=0, all lower tests G_tau<=0. The desired conclusion is that V is affine. No growth or gradient hypothesis beyond these exact fits is added. All pinned results and lower operations at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated; only changed-PDE applicability is checked.

The paid part of the extremal-envelope route is substantive but incomplete. Source 04's fit comparisons and compactness remain valid at fixed tau, as does the source shear/scale normalization with the **same tau**. The source 05 barycentric subsolution operation also survives: adding the trace inequalities through common spatial translation directions makes the variance penalty disappear exactly. This constructs a continuous viscous subsolution W=C_t V-kappa²t/2 below an entire solution V, with contact at (0,1) and a positive barycentric gap. A new fit-only argument supplies the preliminary horizontal-slice alternative without relying on homogeneous envelope convexity.

The precise remaining statement is **SC_tau**: this extremal contact propagates throughout R^m x (0,infinity). If it does, a spatial maximizer of V(y,t)-|y|²/(2t) has zero barycentric gap, contradicting the positive gap. The full conditional proof is in [analytic-attempt.md](../experiments/i231_viscous_liouville/analytic-attempt.md), sections 1–4. Pointwise positive definiteness does not establish SC_tau: the ellipticity ratio degenerates as |DxV| grows. The fit condition alone even permits V(x,t)=x1 sqrt(log(e+x1²)) with C0=10 and unbounded horizontal gradient; the analytic note verifies every sheared box explicitly.

The unchanged source 04–08 envelope propagation cannot fill this gap. Forward quadratic tests now yield convexity only after adding tau m l log l. The source discrete drift acquires a fixed negative loss per step; its stopped-walk estimates and finite-slope conclusion are not obtained. The independent growth route would close from **REG_tau**, a uniform local C^(1,alpha) estimate for the centered viscous fit class, with constants depending on m,C0,tau. The logarithmic growth and shear factors are fully paid after that estimate, but the estimate itself is unpaid. The exponential divergence structure does not justify treating every continuous viscosity solution as a finite-energy minimizer.

For tau->infinity, division by tau gives only Delta_x V=0. The smooth nonaffine function **V(x,t)=sin t** satisfies this PDE and the exact fits with p=a=0, C0=1 at every center and radius. More generally the PDE-plus-fit class has the form b·x+c(t) with constant b; time rigidity is lost. This is a counterexample to the naive limiting theorem, not a constructed limit of exact finite-tau entire fitted solutions. Additional information from an approximating sequence might exclude it; that information has not been proved here.

Primary literature also limits the contribution claim. The exact viscous operator occurs in [Sánchez Morgado, equation (4)](https://arxiv.org/abs/1712.10275v1) and, with the opposite potential sign, in [Porretta, equation (1.7)](https://arxiv.org/abs/2203.04856v1). Their periodic or positive-marginal smooth problems do not supply the needed continuous entire fit theorem. A tempting broad strong-comparison citation was withheld after reading [Ohnuma–Sakaguchi's explicit warning about the earlier gradient-dependent nonuniform proof](https://arxiv.org/abs/1806.03587v1). No worldwide novelty claim follows from these bounded reads.

Exact source contracts, both routes, counterexample calculations, tau/drift transformations and unpaid quantifiers are in the analytic note. [Reading limits and failures](../experiments/i231_viscous_liouville/reading-and-failures.md), [primary excerpts](../sources/i231_viscous_liouville/literature.md), and [authentication](../experiments/i231_viscous_liouville/input-authentication.json) accompany it. No I230/live-agent output, research code, experiments, tests, shared edits, staging, commits, or publication were used. This task does not claim to settle the other regimes of uniform p-harmonic gradient regularity.
