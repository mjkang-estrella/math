# Flow bridge on the noncompact Ni–Tam factor

**Author proof draft.** All source results are stipulated at the pinned revision. This note records the weaker inputs at each reused proof operation; it does not quote source338's positive-curvature main theorem with changed hypotheses. Review is pending.

Let (X,g) be complete connected noncompact Kähler, with nonnegative holomorphic bisectional curvature, and suppose X admits a smooth strictly psh function ψ with bounded gradient. The latter implies |ψ(x)|<=C(1+d_g(o,x)). We claim the initial-data, localized-flow, scalar-comparison, disc-envelope and joint-positivity conclusions of source338 hold on X; then every positive-time slice of this flow is complete.

## 1. The analytic package

Replace ONLY the Busemann/Richberg construction at the start of source preliminaries.tex by the supplied ψ. All the remaining operations have these inputs:

* Jet interpolation (functions, canonical sections, tangent fields): completeness, strict Levi positivity of ψ on fixed compacts, and nonnegative curvature of K^-1 and T^(1,0)X tensor K^-1. The last is the Demailly–Skoda tensor-with-determinant implication from Griffiths nonnegative curvature. The pole weights have compactly supported negative Levi parts, dominated by k ddψ with a fixed sufficiently large k for each finite jet problem.
* Canonical-section growth: weighted L2 solution, upper linear bound on ψ, nonnegative Ricci, and local mean-value/relative-volume comparison. No properness of ψ is used. This yields, at every point, a nonvanishing global canonical section S with log|S|²<=C_S(1+r).
* Finite injective immersion and finite tangent generators: the preceding finite jet interpolation plus the source's Baire/transversality argument. Again no properness is claimed.
* The smooth Xi with ddXi>=Ric(g) and Xi<=C(1+r^(3/2)): the source's locally smooth sum of squared canonical norms and its fixed summable coefficients.
* Exhaustion u comparable to 1+r, bounded gradient, and |dd u|<=C/u: the paired index-form upper Hessian comparison uses bisectional nonnegativity, while scalar heat estimates use Ricci nonnegativity. The source Hodge-heat null-vector reaction is nonnegative under nonnegative bisectional curvature. Its cutoff/commutation construction uses completeness and polynomial volume upper bounds, not strict curvature. Thus its dyadic smoothing argument applies unchanged.
* Average absolute logarithmic canonical norm and scalar curvature <=CL and C/L: the canonical-current inequality dd log|S|²>=Ric(g), heat estimates and the preceding cutoffs give the exact source bounds.

These supply every item of source Proposition initial-data. They do not require ψ to be an exhaustion.

## 2. Localized flow and comparison

Use source flow.tex in full with this package. The complete approximants are Hermitian, not asserted Kähler: alpha=e^{F(u/L)}g on {u<L}. This feature and its fixed-L bounded geometry are retained. In its scalar upper estimates the initial inequality is P_t(0)=-R_alpha<=C/L²: nonnegative Ricci is sufficient despite the prose calling it 'positivity'. The largest-eigenvalue calculation uses only -sum lambda_i^-1 R_g(i,bar i,1,bar1)<=0. The canonical-section barriers, two-sided local metric bounds and diagonal smooth convergence therefore give the same global-in-time Kähler flow h_t with 0<h_t<=g, rho=-log(det h_t/det g)>=0, R_h=rho_t>=0, rho(x,t)<=C_x(1+t), and the source average rho bound.

The adapted integrable cutoff and cofactor proof use 0<=g-h_t<=g, its closedness, the average bounds, and Hodge heat for the initial g. All hold. In particular the scalar nonlinear comparison and smooth majorant retain the exact hypotheses used subsequently. Completeness of h_t is NOT assumed at this stage.

## 3. Curvature preservation through joint positivity

Source discs.tex, variation.tex and ellipsoids.tex have now been read in full. Their inputs are the package in §§1–2:

1. The initial cotangent norm is psh because T^(1,0)X is Griffiths nonnegative; strictness is unnecessary. The sandwich N_0<=v<=N_t uses h_t<=g.
2. Disc compactness uses completeness of the INITIAL g, the finite immersion and global generators, and nonnegative curvature of pulled-back tangent bundles. Its removable-puncture lemma explicitly assumes nonnegative curvature.
3. Disc frames, boundary factorization, compact boundary walls, area penalties, and deformations use these objects plus smooth compact coefficient bounds. Their positive constants are spectral/compactness constants, not global lower bounds on bisectional curvature.
4. The symplectic evolution identity is purely tensorial for Kähler–Ricci flow. The differential envelope inequality uses the scalar-comparison supercaloric tails and the proper Q from §2. Its ordered limits and boundary-only constants are retained without change.
5. Ellipsoid optimization, simultaneous contact jets and the scalar gap comparison use no further curvature hypothesis. Hence v=N and the dual norm N(x,xi,exp(w+bar w)) is jointly psh.

The spatial curvature block gives nonnegative bisectional curvature of h_t. Its time and mixed blocks give the source matrix and scalar differential Harnack inequalities. This is proof-level reuse with hypotheses checked; the three source module theorems are not being asserted independently of their displayed construction.

## 4. Completeness without initial strict Ricci positivity

If g is flat, complete simply connected X (the intended application) is already complex Euclidean, and no flow bridge is needed. Suppose g is not flat. Nonnegative bisectional curvature then gives scalar R_g nonzero somewhere. The scalar evolution R_t=Delta_h R+|Ric_h|² and R>=0 imply R(x,t)>0 for every x and t>0: apply the scalar strong maximum principle on compact cylinders along a finite chain joining a point of initial positive scalar curvature to x. Smooth local convergence to g supplies a positive scalar value at arbitrarily small positive times. This is a local argument and needs no complete positive-time slice.

Write A=Ric_h>=0. Source charts.tex equations chart:matrix-harnack and chart:scalar-harnack, derived before completeness, give A_t+A h_t^(-1)A+t^(-1)A>=0 and R_t+t^(-1)R+2 Re ∂_X R+A(X,bar X)>=0. At a fixed point let each unitary frame vector solve E_t=(1/2)h_t^(-1)A E. Since h_t'=−A, this preserves unitarity, and differentiation gives d[t A(E,bar E)]/dt=t(A_t+A h_t^(-1)A+t^(-1)A)(E,bar E)>=0. Sum over the frame to obtain monotonicity of tR(o,t). This is exactly the source moving-frame calculation, not a new Harnack theorem. The bound rho(o,t)<=C_o(1+t) yields

    t R(o,t) log 2 <= rho(o,2t)-rho(o,t) <= C_o(1+2t),

so R(o,t) is bounded for t>=1; smoothness handles [0,1]. Unlike source charts.tex80–87, we do not assert positive definite Ricci or a compact power contraction.

The scalar Harnack inequality can be divided by R>0. For a path from x to o, integrated from t to t′ at constant h_t-speed, A<=R h and h_s<=h_t yield the integrated Harnack estimate. No minimizing complete geodesic is needed. Choose t′=t+1+d_ht(x,o)², using immortality and the global basepoint scalar bound. Then for t<=T,

    R(x,t)<=C_T(1+d_ht(x,o)²)/t.

For initial balls D_L=B_g(o,L), let l_L(t) be the least h_t-length from o to first exit. Compactness of the closed initial ball and local smooth metric equivalence give a length-minimizing first-exit segment. Its proper initial subsegments minimize among competitors contained in D_L. No claim of global distance minimization is needed: a global shorter competitor could leave and reenter D_L. At every point on the segment, global h_t-distance from o is at most its segment length, hence at most l_L. Compactly supported variations of its interior remain in D_L and give the index form. Endpoint-vanishing cutoffs follow by approximation from interior-supported fields; smoothness on the compact closure controls the limiting integrals. The source index-form cutoff of width min(l/2,sqrt(t)/(1+l)) gives

    integral Ric_h(gamma',gamma') <= C_T(1+l)/sqrt(t).

For fixed L, smooth metric equivalence on the compact closure makes l_L locally Lipschitz in time, including at zero. At a differentiability time t, fix a current minimizing curve γ_t. For ε>0, l_L(t−ε)<=Length_(h_(t−ε))(γ_t), whereas equality holds at t. Thus the backward difference quotient of l_L is bounded BELOW by the backward length quotient of this fixed curve. The length variation formula and the preceding index bound give l'_L(t)>=−C_T(1+l_L(t))/sqrt(t) almost everywhere. The constants in this differential inequality do not depend on L, although the local Lipschitz constants may. Integrate first from ε to t and then let ε down to zero, using l_L(0)=L. This is source charts.tex's paid exit-distance argument with the contained-variation convention made explicit. It gives

    1+l_L(t)>=(1+L) exp(-2 C_T sqrt(t)).

Every finite h_t-ball is therefore contained in an initial compact ball. Local equivalence gives compact closure, hence h_t is complete. This proves the flow bridge needed by the fixed-time-factorization note.

## Exact scope of this draft

The analytic-input replacement, discarded strict-Ricci step, and fixed-time rather than time-dependent splitting are the new integration points. No global curvature bound, metric uniform equivalence at infinity, maximal volume growth, or source shrinking-chart estimate is claimed on X. Source338's MAIN theorem is used only later on complete factors for which strict bisectional positivity has separately been proved. Independent review must check these hypotheses and the proof-level reuse, not only verify that the source main theorem is stipulated.
