# I236 — contact propagation for the actual viscous barycentric envelope

**Verdict: SC_tau is proved, and the exact finite-positive-tau fitted-class affinity follows.** This is a completed research candidate relative to the stipulated pinned package, not an independent gate approval, novelty certification, or accepted-count change.

For every m>=1, 0<tau<infinity and finite C0>=0, let V be a continuous entire viscosity solution of

    V_tt+2 D_xV.D_xV_t+D_xxV[D_xV,D_xV]+tau Delta_xV=0.

Assume that at every center (x,t) and every R>0 there exist p,a such that

    |V(x+h,t+l)-V(x,t)-p.h-(a-|p|²/2)l|<=C0 R
    for |l|<=R and |h-p l|<=R.

Then **V is affine**. Upper tests use G_tau>=0 and lower tests use G_tau<=0. No global gradient bound or additional regularity hypothesis is imposed.

The parent observation is correct: C_t V-|x|²/(2t) is the least concave majorant of V(.,t)-|.|²/(2t). The delicate extra step is that a continuous, spatially semiconcave G_tau-**subsolution** is locally Lipschitz in time as well. At a spatial supporting quadratic, maximize the subsolution minus that quadratic over a fixed spatial ball. The resulting scalar function h(t) has h''>=-C by the actual viscosity PDE, because the lifted test has bounded spatial Hessian and zero mixed Hessian. Its semiconvexity yields time-Lipschitz bounds. This argument does not assert space-time semiconcavity or assume REG_tau for V.

Apply this to the actual I231 subsolution W=C_t V-kappa²t/2. Near each contact, an infimum of translates of V plus a sufficiently steep **full-space cone** gives a locally Lipschitz supersolution U with W<=U<=V and the same contact. A strict cone-slope inequality ensures that equality W=U implies W=V.

For locally Lipschitz functions the smooth flux

    a(p,q)=exp((q+|p|²/2)/tau)(p,1)

has Jacobian exp((q+|p|²/2)/tau) A_tau(p)/tau, uniformly positive definite on the bounded full-gradient range. The [full proof](../experiments/i236_viscous_contact_propagation/analytic-attempt.md) pays the viscosity-to-weak passage using autonomous sup/inf convolutions and one-sided Fatou; it does not simply integrate a formal PDE. Then U-W satisfies a linear, uniformly elliptic divergence inequality. Linear weak-solution Harnack and an explicit harmonic-replacement argument propagate contact. The original contact set is therefore open and closed in R^m x (0,infinity): **SC_tau holds for the actual pair**.

The proof includes every slice alternative. C0=0 is immediate. If all spatial slices are affine, the exact fits force their slopes to be affine in time, logarithmic growth makes the slopes constant, and the PDE makes the remaining time term affine. Otherwise I231's trace-aware barycentric construction produces the positive-gap contact pair. SC_tau makes W=V everywhere at positive times, contradicting the zero envelope gap at a maximizer of V(y,t)-|y|²/(2t).

The older Ohnuma shortcut remains rejected. Reading Trudinger's actual hypotheses also exposes a Hessian-independent gradient-Lipschitz assumption that this operator fails. Explicit smooth solution families in the proof demonstrate both that failure and the failure of ordinary spatial mollification to preserve the subsolution inequality. The successful route uses the operator's specific divergence structure after proving the necessary bounded gradients.

The finite-tau theorem includes fixed drift with the naturally drifted sheared fits. It gives no uniform estimate as tau tends to infinity, does not invalidate I231's limiting-PDE example V=sin t, and does not settle the other regimes needed for a uniform p-harmonic gradient theorem. [Reading limits and failures](../experiments/i236_viscous_contact_propagation/reading-and-failures.md), [primary literature](../sources/i236_viscous_contact_propagation/literature.md), and [authentication](../experiments/i236_viscous_contact_propagation/input-authentication.json) accompany the proof. No I234/live output, subordinate agent, research code, tests, experiments, shared edits, staging, commits, or publication was used.
