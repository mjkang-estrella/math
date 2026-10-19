# SLE: the full compatible clock reduction

This is preselection operation comparison, not a nominated theorem. R112 had already identified Lawler–Sheffield uniqueness and left clock continuity/no-double-counting checks uncompleted. Those were checked here against the stronger explicit source230 gauge. No target was frozen before or after the calculations.

Fix 0<kappa<8, d=1+kappa/8 and h(r)=r^d(log log(1/r))^((2-d)/2) near zero. Source230 explicit `thm:main` gives positive finite h-Hausdorff measure to every positive-time trace segment, simultaneously, and finite EXPECTED measure of the WHOLE trace in every bounded disk, including boundary points. The introductory operation map describes the uniform stopped-law mass tail, retained-mass deletion, quantitative ribbon visits and common-mesh dense cover; these source operations are stipulated, not reproved here. The other companion's finite-batch gauge is different: no regular-variation claim about it is made.

The COMPLETE explicit source `dense-cover.tex` was subsequently read before archive. `lem:cover-charge` gives a whole-trace sausage expectation bounded uniformly in its mesh, with the real-boundary strip controlled by p<1. `prop:dense-cover-upper` chooses one deterministic mesh below all finite stopped-state cutoffs, bounds adapted failure by iterated conditional expectations, selects disjoint candidate disks all charged to that SAME sausage measure, and sends time/interior cutoffs to infinity with one bounded-region expectation constant. Its proof explicitly supplies random-compact Hausdorff measurability through countable rational open covers and real-axis nullity. Thus these are actual source proof operations, not merely the introductory overview. The ribbon and retained-mass proofs that supply its inputs were not newly read.

For each fixed c>0, h(cr)/h(r)->c^d, uniformly for c in a compact subset of (0,infinity). On a compact subset of a conformal domain, subdivide into small neighborhoods on which |F'| varies by at most eta. The Lipschitz cover inequalities for F and its inverse sandwich the pushed h-measure between the local extremal derivative powers. Taking covering scales to zero and then eta to zero yields

    H^h(F(A))=integral_A |F'|^d dH^h

for Borel A in that compact interior. Exhaustion extends this to the open domain. This is the classical local-cover/regular-variation calculation, not a new conformal invariant.

For kappa<=4 the trace is simple. For 4<kappa<8, Miller–Wu [1303.4725v1](https://arxiv.org/pdf/1303.4725v1), Theorem1.1, gives double-point dimension

    q=2-(12-kappa)(4+kappa)/(8 kappa),
    d-q=6/kappa>0.

Choose q<q'<d. Since h(r)/r^q'->0, that set has zero H^h measure. The real line also has zero H^h measure since d>1. The inspected §5 proof reduces to its flow-line intersection theorem and covers the double points by countably many split-path intersections (Lemma5.2); the entire upstream imaginary-geometry proof chain was not reread.

Let mu=H^h restricted to the trace. On each bounded disk mu is finite almost surely and atomless, since h(0)=0. The function t->mu(gamma([0,t]) intersect D) is adapted and continuous for bounded Borel D: the increasing compact trace sets have left union differing from the endpoint set only possibly at gamma(t), and the decreasing future trace intersections equal gamma([0,t]) by continuity of gamma on compact time intervals. Continuity from above/below of the finite measure proves the assertion even after intersecting with D. For finite t the whole trace segment is bounded pathwise, so the same argument gives finite clock time. Hausdorff measure of random compact traces is measurable using rational open finite covers followed by decreasing cutoffs; restriction to Borel D follows by the random-measure monotone class/completed sigma-field convention. One need not presume a finite expectation for an unbounded random enclosing disk.

No-double-counting is exactly the double-point null statement: increments equal the h-measure of the newly traversed segment. After any stopping time the future lies in the closure of the unbounded surviving domain; its intersection with the past boundary is contained in the past/future intersection plus the real line, both mu-null. Conformal covariance therefore applies by compact interior exhaustion, and the ordinary SLE domain Markov property transfers the entire future clock. Boundary derivative estimates are unnecessary on those null sets.

These checks meet the hypotheses of Lawler–Sheffield [0906.3804v1](https://arxiv.org/pdf/0906.3804v1), Proposition2.2: adapted conformally covariant domain-Markov clock and finite local WHOLE-trace expectation. Its actual proof first identifies the expected density by scaling and the Loewner/Markov martingale, then gives

    E[Theta_infinity(D)-Theta_t(D)|F_t]
      =c_kappa integral_D M_t(z) 1_(T_z>t) dA(z).

Here 0<c_kappa<infinity: finiteness is the local expectation input; positivity follows from source positive segment mass and countable disk exhaustion. In §3 the compensator is unique because the difference of two continuous adapted increasing compensators is a continuous finite-variation local martingale. Lawler–Zhou [1006.4936v2](https://arxiv.org/pdf/1006.4936v2), Theorem1 and its proof following Lemma1.3, supplies the same continuous compensator for every 0<kappa<8, with class-D control from stopped two-point estimates. This latter proof was read; its full Lemma1.3 proof was not newly read.

Thus the explicit-gauge clock has the existing compatible uniqueness reduction, up to a deterministic normalization. This is why it was not selected. This record does not claim to calculate c_kappa, identify the irregular finite-batch gauge with h, prove a new SLE dimension estimate, or establish a new-to-literature clock theorem. The separate Minkowski-content identification paper was not acquired/read anew and is not required for the compensator comparison stated here. No restricted-kappa surrogate is nominated.

Acquisition failures are preserved: guessed Lawler–Sheffield v2 and Miller–Wu v3 URLs returned404; both v1 bodies were then successfully acquired. They are not silently recorded as successful later versions. External primary theorems are ordinary cited inputs, not part of the OpenAI truth stipulation.

