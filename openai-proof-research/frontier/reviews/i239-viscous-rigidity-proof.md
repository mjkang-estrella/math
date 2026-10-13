# I239 — independent proof gate for finite-viscosity fitted-class rigidity

**PASS**, relative to the stipulated OpenAI statements and lower operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. This verdict audits the finalized I236 analytic proof with SHA-256 **`a30077ca36f40e6613e340d3f8ae0ac692000f7b39d6eb4113897f40b7c68931`**, 25,759 bytes, 309 lines. I found no substantive unpaid bridge and require no mathematical repair. The proof is independent of REG_tau and of any regularity or weak formulation assumed for arbitrary continuous V.

This is a proof verdict, not a contribution verdict or acceptance-count change. Nine findings remain accepted. I read no other live gate, used no subordinate agent, and did not modify I236.

## Exact conclusion

For every integer m>=1, every fixed finite tau>0, and every finite C0>=0, every continuous entire viscosity solution of

    V_tt+2 D_xV.D_xV_t+D_xxV[D_xV,D_xV]+tau Delta_x V=0

is affine if, at every center (x,t) and every radius R>0, some p in R^m and a in R satisfy

    |V(x+h,t+l)-V(x,t)-p.h-(a-|p|²/2)l|<=C0 R
    whenever |l|<=R and |h-pl|<=R.

Upper tests use G_tau>=0 and lower tests G_tau<=0, including horizontal gradient zero. The fit coefficients need not be uniform or continuous in center/radius. No bounded-gradient hypothesis is added.

The intermediate contact theorem also passes: a continuous locally spatially semiconcave G_tau-subsolution below a continuous supersolution on a connected open set agrees with it everywhere if it touches at an interior point. The semiconcavity constant is locally uniform in time. This applies to the actual extremal W=C_tV-kappa²t/2 on t>0.

## Findings on the decisive bridges

1. **Time regularity is paid.** A spatial supergradient exists at each base time, with a common bound from the spatial margin and local oscillation. Increasing the support curvature by one creates a fixed boundary gap. The common time modulus keeps the maximum interior on one common time interval. A scalar upper test lifts to a genuine upper test of the subsolution with bounded spatial Hessian and zero mixed Hessian. It gives h''>=-C in the viscosity sense and hence scalar semiconvexity. Bounded convex secant slopes give the upper time increment. Repeating at the other base time, with the same constants, gives the reverse increment. The proof does not confuse slice semiconcavity with space-time semiconcavity.

2. **The full cone really recovers original contact.** For L>Lip(u), every competitor in v_L(z)=min_{|h|<=r}(v(z+h)+L|h|) is at least u(z)+(L-Lip(u))|h|. Near contact all minimizers are interior. Fixed-shift test transfer proves the supersolution property; moving the same physical target between nearby centers proves full Lipschitz continuity. Equality v_L=u forces h=0 and therefore v=u. The conclusion is stronger than the insufficient relation v_L<=v.

3. **The viscosity-to-weak step is valid for the bounded-gradient pair.** Autonomous full-variable sup/inf convolutions preserve the appropriate inequalities. At fixed convolution parameter their one-sided Hessian bounds survive ordinary mollification. Almost-everywhere Hessian convergence and one-sided Fatou yield the weak inequality without deleting unfavorable singular curvature. The later nonlinear flux limit uses a separate proof of almost-everywhere gradient convergence: differentiability of the original Lipschitz function and completion of the square pin down each maximizing/minimizing displacement. Uniform bounded gradients then give L¹ flux convergence. The proof does not integrate the PDE for the original continuous V.

4. **Harnack is applied to a weak solution, with a valid trace conclusion.** The flux derivative is symmetric positive definite on bounded full-gradient ranges. Its averaged matrix linearizes the difference d=v_L-u into a uniformly elliptic divergence supersolution. A Lax–Milgram harmonic replacement w with the same trace satisfies 0<=w<=d by energy tests. Its interior zero and weak-solution Harnack give w=0. Since w-d belongs to H¹_0, d has zero trace. Its actual Lipschitz continuity makes this the pointwise zero restriction on the whole sphere. Repeating for all sufficiently small radii gives an open contact set. Continuity and connectedness finish propagation.

5. **The altered source inputs are checked rather than assumed.** The sheared frame has G_tau[U]=R G_tau[V], retaining the same tau. Source 04's fit-only estimates and compactness transfer; viscosity identification uses continuity of the new operator. The limiting fit is obtained separately at each fixed center/radius, including boundary points. C0=0 and the all-spatial-slices-affine case are fully covered. In the latter, fits force the spatial slope to satisfy the midpoint identity in time; logarithmic growth removes its time-linear part, and the actual PDE makes the remaining scalar term affine.

6. **The common-time trace sum is a legitimate viscosity operation.** Finite attainment provides finitely many positive weights. Separate and synchronize their times. For fixed synchronization parameter, divide the weighted closed jets and apply the individual viscous inequalities. Test the block matrix inequality on the common-time vector and on each common spatial translation vector. First send the theorem-of-sums error to zero, then send the synchronization parameter to infinity. The synchronization Hessian vanishes on every chosen vector. Large time jet components are harmless because G_tau does not depend on the time gradient. The barycentric variance has zero second variation in all required directions, giving exactly the new trace term.

7. **The extremal and final global steps close.** Unit-second-moment measures preserve their mean by first-moment uniform integrability; uniform subquadratic growth preserves the varying value integrals. The envelope sandwich forces equality and prevents second-moment loss. The R=1/kappa frame scales the envelope parameter and gap correctly. Finally a global maximizer of V(y,t)-|y|²/(2t) exists and has zero barycentric gap, whereas propagated contact requires the same gap to be kappa²t/2>0 everywhere. This is an actual contradiction for each fixed t>0.

The full independent calculations, including the weighted matrix inequality and all limit orders, are in [analytic-check.md](../experiments/i239_viscous_rigidity_proof/analytic-check.md). They expand abbreviations without adding hypotheses or relying on a formal smooth argument.

## Failed shortcuts and limits

The candidate's smooth exact solution families really show failure of a Hessian-independent gradient-Lipschitz operator bound and failure of ordinary spatial mollification to preserve subsolutions. These are local PDE counterexamples, not alleged globally fitted counterexamples. The time-only t log|t| example shows why spatial semiconcavity without the PDE cannot replace Lemma 2.1. The earlier Ohnuma argument remains excluded; its later primary warning was read. Trudinger's actual F2 also cannot be supplied for G_tau, even on bounded gradient ranges.

No theorem uniform as tau tends to infinity, no REG_tau, and no p-harmonic gradient convergence is inferred. Fixed drift is covered only with the naturally drifted fit shear and time coefficient. The limiting equation Delta_x V=0 still permits V=sin t with the same type of fits; finite-tau rigidity does not validate that limiting PDE-plus-fit theorem.

[Primary sources and exact read scopes](../sources/i239_viscous_rigidity_proof/literature.md), [reading limits](../experiments/i239_viscous_rigidity_proof/reading-and-failures.md), and [authentication](../experiments/i239_viscous_rigidity_proof/input-authentication.json) accompany this verdict. No claim of worldwide novelty is made.
