# I234: local regularity for the viscous limiting equation

Work only in /home/mj-kang/Documents/Dev/math/openai-proof-research. Read AGENTS.md and sources/upstream.json. All pinned OpenAI results and lower operations at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. Nine accepted findings, one remains. GPT-6.1 Sol/high/ultrafast. No subordinate agents. Read actual source contracts and primary literature. No live other-agent outputs. Write partial mathematical notes early. No research code, tests, parameter scans, numerical experiments, snapshots, seals, giant history replay, shared edits, staging, commits or publication. Ordinary retrieval/extraction/source-local lookup and provenance hashes allowed. Return exact hypotheses, full proof or precise unpaid step, verdict, reading limits and detached hashes.

This is a separate local-regularity route supporting, but not duplicating, I231's entire rigidity investigation. The parent's complete conditional reduction is supplied below. Independently seek a local Lipschitz/continuous-spatial-gradient estimate for every bounded continuous viscosity solution of
G_tau[V]=V_tt+2 DxV.DxV_t+DxxV[DxV,DxV]+tau Delta_xV=0,
for fixed tau>0, on an interior product cylinder. Desired constants/modulus depend only on dimension, tau and oscillation, with no already assumed gradient or Hessian bound. A common interior modulus of DxV would close the parent's entire rigidity reduction. Do not assume uniformly elliptic coefficients from pointwise positive definiteness. The integrand exp((V_t+|DxV|²/2)/tau) is strictly convex but has no global uniform ellipticity. Investigate actual local Bernstein/quasilinear regularity and primary literature on this PDE (Sanchez Morgado arxiv1712.10275 equation4, Porretta arxiv2203.04856 equation1.7 with sign change are leads, not assumed theorems). Any imported theorem must cover the precise local viscosity class or be connected by a proved regularization/uniqueness argument. Alternative route can be a weaker estimate specific to solutions with the all-scale fits, if it closes the same global reduction. Distinguish known local estimates from a new bridge. Do not read I231's live output; no independent gate is being run here. Write only frontier/iterations/i234-viscous-local-regularity.md, frontier/experiments/i234_viscous_local_regularity/{analytic-attempt.md,reading-and-failures.md,input-authentication.json}, and frontier/sources/i234_viscous_local_regularity/literature.md plus fully read primary excerpts.

## Complete parent reduction
# I233 — parent calculation for the viscous limit

**Partial conditional reduction, not a finding or a proof of I231.** This calculation is independent of the live I230/I231 outputs. No contribution or prior-art claim is attached.

For a smooth function v(x,t), x in R^d, put w=v_t+|D_xv|^2/2 and

    F[v]=D^2v[(D_xv,1),(D_xv,1)].

Direct differentiation gives F[v]=w_t+D_xv.D_xw. Consequently, for fixed tau>0,

    F[v]+tau Delta_x v=0

is exactly the Euler–Lagrange equation of the strictly convex gradient integrand

    L(p,q)=exp((q+|p|^2/2)/tau).

Indeed L_q=L/tau and L_p=Lp/tau, so partial_t L_q+div_x L_p=L(F[v]+tau Delta_xv)/tau^2. Its gradient Hessian has quadratic form

    D^2 L(p,q)[(xi,eta)] = L[(p.xi+eta)^2/tau^2+|xi|^2/tau],

which is positive definite. It is not uniformly elliptic over unbounded gradients; no regularity theorem is inferred from strict convexity alone.

The equation is invariant under adding constants or a multiple of t, under isotropic scaling v_R(x,t)=v(Rx,Rt)/R, and under the Galilean change

    v^a(x,t)=v(x+a t,t)-a.x-|a|^2 t/2.

For the last identity, D_xv^a=D_xv-a and w^a=w(x+a t,t). Hence the material derivative partial_t+D_xv^a.D_x becomes partial_t+D_xv.D_x on w, and Delta_xv^a=Delta_xv. These are classical identities; extension to viscosity solutions requires checking smooth-test transformations, not differentiating a nonsmooth solution.

Suppose v has the exact I231 all-center/all-radius shear-fit property with error C0 R. At the origin choose p_R,q_R with

    |v(h,l)-v(0)-p_R.h-q_R l|<=C0 R
    for |l|<=R, |h-p_R l|<=R.

At l=0, comparison of the R and 2R fits on |h|<=R gives |p_R-p_(2R)|<=3C0. For dyadic R tending to infinity, therefore |p_R|=O(1+log R).

The normalized functions

    u_R(X,T)=[v(RX+R p_R T,RT)-v(0)
                -R p_R.X-R(q_R+|p_R|^2)T]/R

satisfy |u_R|<=C0 on the unit product cylinder and the same viscous equation. If this bounded family admitted a common interior modulus of continuity for D_Xu_R, then v would be affine. For a fixed (h,l), its transformed coordinate is ((h-p_R l)/R,l/R), which tends to zero by the logarithmic bound. Thus the common modulus would imply D_xv(h,l)=D_xv(0,0). It would follow that v(x,t)=p.x+g(t), and the equation would reduce to g''=0.

**Unpaid lemma:** bounded solutions of the fixed-tau viscous equation on a unit cylinder have classical spatial derivatives with an interior modulus depending only on tau, d and their oscillation. This is not supplied by I224's forced infinity theorem, since the transverse Laplacian is not bounded a priori. Nor does mere strict convexity of L supply it. A full-space fit theorem remains unproved here until that lemma or a different rigidity argument is paid.


## Original motivation and prior results from I231's brief
# I231: viscous anisotropic Liouville bridge

Work only in /home/mj-kang/Documents/Dev/math/openai-proof-research. Read AGENTS.md and sources/upstream.json. All pinned OpenAI results and lower operations at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. Nine accepted findings, one remains. GPT-6.1 Sol/high/ultrafast. No subordinate agents. Read actual source contracts and primary literature. No live other-agent outputs. Write partial mathematical notes early. No research code, tests, parameter scans, numerical experiments, snapshots, seals, giant history replay, shared edits, staging, commits or publication. Ordinary retrieval/extraction/source-local lookup and provenance hashes allowed. Return exact hypotheses, full proof or precise unpaid step, verdict, reading limits and detached hashes.

This is a new focused bridge motivated by the supplied I224 original task, proved R/S, I228 proof PASS and I229 negative contribution. I224's bounded forcing extension is technical and not counted. Seek a genuinely new Liouville/rigidity theorem sufficient for uniform p-harmonic gradient regularity. Under the p-equation Delta_inf u+epsilon |Du|² Delta u=0, I224's anisotropic scaling gives F[V]+(epsilon/lambda)(lambda|DxV|²+(1+lambda Vt)²)(Delta_x V+lambda Vtt)=0. A finite positive epsilon/lambda limit would have F[V]+tau Delta_x V=0, where F[V]=D²V[(DxV,1)], tau>0. Investigate whether the exact source all-center/all-radius sheared affine-fit hypothesis forces every entire solution of this NEW viscous equation to be affine, with constants appropriate to tau and drift. Do not merely assert ellipticity or reuse the homogeneous theorem; gradients need not be globally bounded under the fit hypothesis. Account also for whether the tau->infinity regime gives a valid affine limit or a counterexample (the naive limiting Delta_x V=0 permits arbitrary functions of time). Two routes: adapt the extremal-envelope proof with the trace term, versus a new Liouville/growth argument. Source 04–08 loweroperations may be used only with checked changed PDE inputs. If exactfitcondition admitsnonaffineexample supplyit. Do not read I230's live work. This task does not claim the displayed new Liouville theorem suffices for the whole p convergence problem without the other regimes.

Write only frontier/iterations/i231-viscous-liouville.md, frontier/experiments/i231_viscous_liouville/{analytic-attempt.md,reading-and-failures.md,input-authentication.json}, and frontier/sources/i231_viscous_liouville/literature.md plus fully read source excerpts there.


## Prior complete document frontier/iterations/iteration224-infinity-gradient-stability-brief.md

# I224: quantitative infinity-harmonic gradient stability

Work only in /home/mj-kang/Documents/Dev/math/openai-proof-research. Read AGENTS.md and sources/upstream.json. Accept ALL pinned OpenAI theorems and lower proof operations at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb as true; do not audit them. Nine substantial findings accepted, one remains. User requires continuing until ten but no lowering of proof or contribution standards. GPT-6.1 Sol/high/ultrafast. No subordinate agents. Read actual pinned manuscripts, companion claims and relevant primary prior art. Select strongest plausible target early, pursue at least two genuinely different routes, write partial mathematics early. New-to-project, direct substitutions, compactness-only moduli, standard transfers or equivalent reformulations do not qualify. Try counterexamples actively. No worldwide novelty from search misses. Return exact hypotheses, quantifiers, fully paid proof or precise unpaid estimate and honest verdict. Do not read live other-agent outputs. Do not edit shared ledgers, stage, commit or publish. No research code, numerical experiments, parameter scans, tests, snapshots, seals, or giant historical replay. Ordinary retrieval, extraction, source-local lookup and provenance hashes allowed. Existing source copies should be reused. Only retain new copies you actually read fully (page-limited excerpts fine with explicit limits). Return detached hashes of final outputs. Parent owns both independent gates.

Focused continuation of the unpaid family377 gradient problem. Read I130's relevant Screen I, I140/I143 relevant infinity/p-harmonic sections and I213's screening paragraph only, to avoid recycling. Earlier homogeneous gradient interpolation is technical; affine lifting does not turn p-harmonic equations into infinity-harmonic ones. Seek a genuine quantitative stability estimate for gradients of solutions with small normalized-infinity-Laplacian forcing or a quantitative p-to-infinity gradient convergence theorem under precise assumptions. The newly accepted C1,alpha estimate is for exactly infinity-harmonic functions; quantify the inhomogeneous approximation error rather than assume it. Possible route: comparison-with-cones barrier yielding uniform C0 stability then an improvement-of-flatness argument that pays forcing; alternate route viscosity compactness plus a quantitative blowup/doubling bridge. You may narrow to a concrete class with nonvanishing limiting gradient, but mere interpolation of already assumed uniform C1 bounds is technical. State the actual forcing convention at critical gradients. If impossible, isolate the sharp needed lemma with concrete obstruction; no nomination without it.

Write only frontier/iterations/i224-infinity-gradient-stability.md, frontier/experiments/i224_infinity_gradient_stability/{analytic-attempt.md,reading-and-failures.md,input-authentication.json}, and frontier/sources/i224_infinity_gradient_stability/literature.md plus actually read primary source copies there.


## Prior complete document frontier/iterations/i224-infinity-gradient-stability.md

# I224 — quantitative infinity-harmonic gradient stability

**Research verdict: a proved analytic candidate relative to the stipulated family-377 lower operations; independent proof and contribution gates remain open. No accepted-count change.** The proof does not assume C¹ bounds on the forced solution. The genuine new bridge submitted for scrutiny is a uniform forced-class power estimate; its final interpolation consequence is explicitly technical. This is an extension of the pinned method, and the parent must decide whether that extension clears the prohibition on standard transfers. Worldwide novelty is not certified.

## Exact candidate

For every integer d>=3 there exist dimension constants `a_d in (0,1/3]`, `b_d=a_d/(1+a_d)>0`, and `C_d<infinity` such that the following holds. Let `0<m<=1`, `0<epsilon<=min(1,m²)`. Let `v in C(cl B1)` be infinity-harmonic in B1, with `0<=v<=1` and `inf_(B1)|Dv|>=m`. For every bounded continuous f with `||f||_infinity<=epsilon` and **every existing** viscosity solution `u in C(cl B1)` of

`-Delta_inf^N u=f` in B1, `u=v` on its sphere,

one has actual continuous interior gradients and

`||u-v||_(Linf(B1)) <= epsilon/m²`,

`||Du-Dv||_(Linf(B1/2)) <= C_d (epsilon/m²)^{b_d}`.

The normalized convention is: at an upper C² test with zero gradient use `-lambda_max(D²phi)<=f`; at a lower test use `-lambda_min(D²phi)>=f`. At nonzero gradients use `-D²phi[Dphi,Dphi]/|Dphi|²=f` with the corresponding one-sided inequalities. f may change sign; the statement does not assert arbitrary sign-changing existence or uniqueness. The nonvanishing assumption is on v throughout B1, not on u. Exponents are positive but nonexplicit; no endpoint claim is made.

## What pays the previously missing estimate

The main proof establishes the stronger local regularity bridge

`||Du||_(B1/2)+[Du]_(C^{0,a_d}(B1/2)) <= C_d(osc_(B1)u+||f||_infinity)`

for all bounded continuous solutions of the normalized forced equation. Four steps matter:

1. The lift `U(y,t)=u(y)+t` satisfies the **inequalities** `|Delta_inf U|<=F|DU|²` at tests. Its full test gradient is nonzero. Quadratic cones give `L_r^±<=L_R^±+FR`, local Lipschitz control and affine fixed-center tangent functions.
2. The source's three-point penalty still works with forcing: its jet lower bound changes from zero to a bounded negative number, whereas the same penalty Hessian tends to minus infinity. This yields uniform qualitative affine flatness for the entire forced class, not an assumed common modulus for its gradients.
3. A strengthened running-maximum choice forces `r_i/lambda_i ->0`. After the source anisotropic stretch the residual is bounded on compact jets by `C r_i/lambda_i`. The limiting equation is therefore **exactly** the stipulated homogeneous Liouville equation, with all its required affine fits at every center and radius.
4. Liouville contradiction gives a uniform power law for the forced-class fit parameter. Summable fitted slopes then construct its actual C¹,a_d gradient. Only after this proof do explicit concave/convex compositions of v give the value comparison, followed by elementary interpolation.

The full proof, including the precise source contracts and critical-gradient cases, is in [analytic-attempt.md](../experiments/i224_infinity_gradient_stability/analytic-attempt.md). All source statements at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted, not audited. The affine lift is not used to claim that a p-harmonic approximant becomes infinity-harmonic.

## Distinct route and counterexamples

The alternate variational route for p-harmonic gradients was pursued. Its exact local test yields `||zeta Du_p||_p<=|a| ||zeta||_p+p delta ||Dzeta||_p`. With known value rates, the remaining `p(delta_p/r+r^{a_d})` cannot be made small. Degenerating energy weights cannot be divided out using only a nonzero limiting gradient. This route remains unpaid; no p-to-infinity gradient theorem is submitted.

Smooth transverse oscillations give two concrete limitations. Functions `x1+k^{-4/3}sin(kx2)` have bounded normalized forcing and nonzero gradient, but prohibit a forced-class Hölder exponent above 1/3. With a fixed cutoff, `x1+a² chi(x)sin(x2/a)` has exactly the affine boundary trace, forcing O(a²), and gradient error a at the center. Thus a universal rate exponent above 1/2 in the forcing norm is false, even with an affine nonvanishing comparison function. These do not refute the positive, smaller exponent submitted here.

## Literature and contribution limits

The prescribed overlap reads were limited to I130 Screen I, I140/I143's infinity/p-harmonic sections, and I213's screening paragraph. I130 already spends homogeneous interpolation; that operation alone is not nominated. Actual pinned introduction, flatness, reduction, main-file/bibliography and final Liouville assembly were read. The complete preprint-path catalogue has one family-377 manuscript and no same-family companion with an inhomogeneous conclusion.

Primary comparisons read include Lu–Wang's normalized quadratic-comparison and qualitative value stability statements/proof excerpts; Crasta–Fragalà's normalized critical-gradient convention and constant-source convex-domain C¹ result; Bungert's actual value-rate theorem from the reused copy; and the main statements of the October 9 Sobral–Teixeira–Urbano preprint, whose infinity result is planar and homogeneous. These establish bounded distinctions, not worldwide novelty. The newly proved forced power estimate is the only plausible substantial contribution here; the cone comparison, composition barrier and final interpolation are not individually substantial nominations.

Reading scope, failed retrievals and route failures are in [reading-and-failures.md](../experiments/i224_infinity_gradient_stability/reading-and-failures.md). Primary excerpts and links are listed in [literature.md](../sources/i224_infinity_gradient_stability/literature.md), and exact hashes in [input-authentication.json](../experiments/i224_infinity_gradient_stability/input-authentication.json). No live other-agent output, shared ledger, research code, experiment, test, staging, commit, or publication was used.


## Prior complete document frontier/experiments/i224_infinity_gradient_stability/analytic-attempt.md

# I224 — quantitative infinity-gradient stability: analytic argument

**Status:** proved candidate relative to the stipulated family-377 Liouville theorem and its equation-independent fit operations. Independent proof and contribution gates remain with the parent. No claim of worldwide priority or of an accepted tenth finding.

All OpenAI theorems and lower proof operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted, not audited. The early draft of this file recorded the cone calculation and the unpaid ratio `r/lambda`; the argument below pays that ratio explicitly.

## 1. Statements and conventions

Write `Delta_inf phi = D²phi[Dphi,Dphi]`. For `-Delta_inf^N u=f`, an upper C² test at a nonzero gradient p satisfies `-X[p]/|p|² <= f`; at p=0 it satisfies `-lambda_max(X)<=f`. A lower test satisfies the opposite inequality, with `-lambda_min(X)` at p=0. These are the relaxed normalized conventions of Crasta–Fragalà, Definition 1, and Lu–Wang. In particular, this is not the equation obtained by discarding all zero-gradient tests. The estimates use only `|f|<=F`; f need not have a derivative or a fixed sign.

**Theorem R (the forcing bridge).** For every integer d>=3 there are `a_d in (0,1/3]` and `A_d<infinity` such that every bounded continuous viscosity solution of `-Delta_inf^N u=f` on B1, with `f in C(B1)` bounded, belongs to `C^{1,a_d}(B1/2)` and satisfies

`||Du||_(Linf(B1/2)) + [Du]_(C^{0,a_d}(B1/2)) <= A_d (osc_(B1) u + ||f||_(Linf(B1))).`       (R)

The exponent is a newly obtained nonexplicit dimension constant; it is not asserted to equal the exponent printed in the pinned homogeneous theorem. Uniform estimates also hold on B3/4 after changing A_d. Neither existence for arbitrary sign-changing f nor uniqueness for that problem is asserted: the theorem quantifies over every solution that exists.

**Theorem S (selected stability target).** For every d>=3 there are `b_d=a_d/(1+a_d)>0` and `C_d<infinity` with the following property. Let `0<m<=1`, `0<epsilon<=min(1,m²)`, and let

* `v in C(cl B1)` be infinity-harmonic in B1, `0<=v<=1`, and `inf_(B1)|Dv|>=m`;
* `f in C(B1)` satisfy `||f||_infinity<=epsilon`;
* `u in C(cl B1)` be any viscosity solution of `-Delta_inf^N u=f` in B1 with `u=v` on the sphere.

Then u has classical continuous interior gradients and

`||u-v||_(Linf(B1)) <= epsilon/m²,`

`||Du-Dv||_(Linf(B1/2)) <= C_d (epsilon/m²)^{b_d}.`                         (S)

The derivative of v in the hypothesis exists by the accepted source theorem. No derivative, lower gradient bound, semiconcavity, or common C¹ bound is assumed for u. The bound on v is over the whole open ball; this is a deliberate restriction, not an interior-only condition. Boundary data need only be continuous subject to the stated existence of v. When epsilon=0, homogeneous uniqueness gives u=v. This is not a p-to-infinity gradient convergence theorem.

## 2. Exact source interface

The reused manuscript is `preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026`. In `build/manuscript/sections/03-reduction.tex`, `thm:liouville` says:

For every m>=1, a continuous entire solution

`D²V[(D_x V,1),(D_x V,1)]=0` on `R^m x R`

is affine if one constant C0 gives, at every center (x,t) and every R>0, coefficients p,q such that

`|V(x+h,t+l)-V(x,t)-p.h-q l|<=C0 R`

whenever `|l|<=R` and `|h-p l|<=R`.

The source writes q as `a-|p|²/2`, an unrestricted reparameterization. This theorem, the finite-dimensional cylinder-fit comparison (`lem:cylinder-comparison`), and the geometry/compactness part of `prop:nonaffine-limit` are stipulated lower operations. Their input contracts were read in full. No inhomogeneous PDE is inserted into the homogeneous theorem. Sections 2–3 below construct an **exact homogeneous limit** satisfying its full all-center/all-radius fit contract.

The source's theorem-of-sums operation `lem:sum-rule` is also used. Its application to a doubled maximum gives the standard matching-gradient superjet/subjet pair and the inequality `X[p]<=Y[p]`. This is a stipulated viscosity operation, not an additional regularity theorem. Sections 04–07 proving the source Liouville theorem are not reread or audited; its statement and final assembly are sufficient dependencies.

## 3. Route B: forcing survives until the correct anisotropic limit

### 3.1 A stable lifted class

Consider all continuous lifts `U(y,t)=w(y)+t` on `B1^d x R`, with `w(0)=0`, `osc w<=1`, satisfying the following continuous-operator inequalities at all tests:

`D²phi[Dphi,Dphi] >= -|Dphi|²` at upper tests,

`D²phi[Dphi,Dphi] <=  |Dphi|²` at lower tests.                         (L)

Call this family U. It is closed under locally uniform limits on the available domain. The inequalities are continuous in both jet variables, including the zero gradient. We only assert this closure for (L), not an unproved closure of a differentiable family.

Every w solving the normalized equation with `osc w<=1`, `||f||<=1`, gives such a lift. Indeed an upper test phi of U has `phi_t=1`. Put `p=D_y phi`. If p is nonzero, choose an affine graph t=ell(y) with `D ell.p=1`, and use the upper test `psi(y)=phi(y,ell(y))-ell(y)` for w. Its gradient is p and

`D²psi[p,p] = D²phi[(p,1),(p,1)].`

The normalized inequality yields the lower bound `-|p|²`, hence the weaker `-(1+|p|²)` required in (L). If p=0, restriction to the vertical line gives `phi_tt>=0`, which also proves (L). Lower tests reverse these signs. Thus the actual critical-gradient convention is respected, and the **full** lifted test gradient never vanishes. The lift is only claimed to satisfy inequalities; it is not claimed to solve an exact forced equation.

### 3.2 Quadratic cones and affine tangent functions

More generally suppose W satisfies (L) with a constant F multiplying its right sides. For a ball compactly contained in its domain define

`L_R^+(W;z)=max_(cl B_R(z))(W-W(z))/R`, and analogously L_R^-.

These maxima include the center and are nonnegative. If `F'>F`, the radial function

`C(rho)=W(z)+(L_R^+ + F' R)rho - (F'/2)rho²`

dominates W at rho=0 and rho=R. On `0<rho<R` its radial derivative is strictly positive and `Delta_inf C=-F' |DC|²`. A positive interior maximum of W-C would give an upper test contradicting (L). Therefore

`L_r^+ <= L_R^+ + F R`,  `L_r^- <= L_R^- + F R`,  `0<r<R`.           (C)

This gives a local Lipschitz bound from local oscillation. It gives one common Lipschitz constant on B7/8 for the normalized lifts. It also proves existence of finite limits `L_*^+` and `L_*^-` at each fixed center: take limsup as r goes to zero in (C), then let R go to zero along a liminf sequence.

The two limits are equal. If h_r attains the positive maximum, then `|h_r|<=r`, and

`L_r^+(W;z) <= L_r^-(W;z+h_r) <= L_R^-(W;z+h_r)+F R` for r<R.

For fixed R the slope is continuous in the center, by continuity of W on a compact neighborhood. First let r go to zero, then R go to zero. This proves `L_*^+<=L_*^-`; apply the same argument to -W for equality.

For a fixed W, its linear blow-ups `(W(z+r_j X)-W(z))/r_j` have uniformly bounded local Lipschitz constants. Every subsequential limit H is entire and infinity-harmonic: (L) rescales to a residual bound `r_j F |DH|²`, which vanishes on compact jets. Moreover `L_R^+(H;0)=L_R^-(H;0)=L_*` for every R. The fixed-center affine-blow-up proof in source `prop:affine-blowups` now applies to this **homogeneous** H. In detail its cone slopes at every center are monotone, its origin slopes imply `|H(X)|<=L_*|X|`, sending a comparison radius to infinity makes it globally L_*-Lipschitz, and equality between its positive and negative origin extrema forces equality on an entire line. Sending the endpoints of that line to infinity gives `H(X)=P.X`. Thus all fixed-center tangent functions are affine, without claiming uniqueness of their slopes yet.

### 3.3 Three-point estimate with bounded forcing

The following extension is essential; homogeneous gradient interpolation does not supply it. Let W_i satisfy (L) with `F_i<=F0`, have a common Lipschitz bound on B1, and converge uniformly to affine functions in the sense `||W_i-ell_i||_infinity ->0`. Then

`sup_(x!=y in B1/4) |W_i(x)+W_i(y)-2W_i((x+y)/2)|/|x-y| ->0`.          (T)

Here are all changes required in source `prop:three-point`. Fix a violating defect delta>0 and use its penalized maximum with

`r=|x-y|`, `h=z-(x+y)/2`, `f0(r)=r-r^{3/2}/8`,

`(W_i-ell_i)(x)+(W_i-ell_i)(y)-2(W_i-ell_i)(z)-B((x+y)/2)f0(r)-|h|²/r²`.

Exactly the source's equation-free localization gives `r->0`, `h=O(r²)`, an interior maximum, and bounded test vectors p1,p2,p0 with their positive longitudinal coefficient bounded below by delta/4. For the functions W_i,W_i,-2W_i, the theorem of sums gives matrices X1,X2,X3. The last function has forcing bound 2F0 because amplitude scaling by -2 multiplies the unnormalized operator by -8. Hence

`X1[p1]>=-F0|p1|²`, `X2[p2]>=-F0|p2|²`, `X3[p0]>=-2F0|p0|²`.

With `sigma=(p1,p2,p0)` and A the Hessian of the penalty, let the theorem-of-sums parameter tend to zero. The resulting inequality is

`A[sigma] >= -F0(|p1|²+|p2|²+2|p0|²) >= -C(F0,L,delta)`.

The source's displayed algebra for this **same** penalty is equation-independent and gives

`A[sigma] = -3 B a²/(8 sqrt(r)) + O(1) -> -infinity`.

This is the contradiction. The forcing is bounded, not set to zero; no derivative of f occurs. All constants may depend on the fixed violating delta, which suffices for (T).

### 3.4 Uniform qualitative cylinder flatness

Use exactly the source cylinders

`Z_lambda(z,r;P)={z+h: |h.N_P|<=r, |h-(h.N_P)N_P|<=sqrt(lambda)r}`,

where `N_P=P/|P|`, and call lambda good if some P!=0 satisfies

`|U(Z)-U(z)-P.(Z-z)|<=lambda r` on that cylinder.

Put G=B3/4 in dimension d+1, `D(z)=dist(z,partial G)`, beta_U(z,r)=supremum of bad parameters in (0,1), and

`b(s)=sup{beta_U(z,r): U in U, z in G, 0<r<=sD(z)}`, `0<s<=1/8`.

The geometry of the definition gives `|P|<=L+sqrt(lambda)` and `|P.e_t-1|<=sqrt(lambda)` for every good fit: its cylinder contains the ball of radius sqrt(lambda)r, and the vertical increment of U is exact.

We have `b(s)->0`. To verify rather than assume this, suppose bad parameters lambda_i>=delta occur at `r_i/D(z_i)->0`. Take a locally uniform limit U0 on B7/8 and a limit center z*. Choose slow scales R_i going to zero with

`r_i+|z_i-z*|+||U_i-U0||_(B7/8)=o(R_i)`.

Section 3.2 gives an affine subsequential tangent of this fixed, possibly forced, U0 at z*. Thus `(U_i(z*+R_i X)-U_i(z*))/R_i` converge to the same affine function. Their forcing bounds are R_i<=1, so (T) applies at **every** endpoint separation. Pulling that midpoint estimate back to scale r_i makes every limit of the r_i-blow-ups satisfy the midpoint identity. Continuity makes that limit affine on B2, with vertical slope one. It supplies the allegedly bad delta-cylinder fit for large i, a contradiction. This is the source `lem:family-flatness` argument with both required inhomogeneous inputs now proved.

### 3.5 Selecting scales that pay the forcing

Suppose b has no power bound near zero. Choose `0<gamma_i<=1/2`, gamma_i decreasing to zero. Strengthen source `lem:bad-scales` by choosing its factor-two running maximum so that also

`b(s_i)/s_i^{gamma_i} >= i`, `s_i<1/i`.

This is possible because that quotient is unbounded near zero; on intervals separated from zero it is bounded. Retain the source selection

`b(s)/s^{gamma_i} <= 2 b(s_i)/s_i^{gamma_i}` for `s_i<=s<=1/8`,

`b(s_i)/4 < lambda_i <= b(s_i)`, with lambda_i bad at `(U_i,z_i,r_i)` and `r_i<=s_i D(z_i)`.

Then the missing quantitative separation is explicit:

`r_i/lambda_i <= 4 D(z_i) s_i / b(s_i) <= 3 s_i^{1-gamma_i}/i ->0`.      (F)

The source proof still makes `Lambda lambda_i` good at every center within M r_i and every radius <=M r_i, for every fixed M, where Lambda=32. Indeed the bound is `beta_Ui(z,r)<=8lambda_i(2M)^{gamma_i}<32lambda_i`. Thus strengthening the maximum has not spent the all-center/all-radius information.

### 3.6 Exact limiting PDE and all required fits

Choose a good slope P_i at radius r_i for Lambda lambda_i and set `c_i=|P_i|`. Vertical increments give `1/2<=c_i<=L+1`. Rotate to P_i/c_i and define V_i by

`U_i(z_i+r_i(sqrt(lambda_i)x,t))=U_i(z_i)+r_i c_i(t+lambda_i V_i(x,t))`.

For any smooth test phi the original gradient is

`c_i (sqrt(lambda_i)D_x phi, 1+lambda_i phi_t)`

and its infinity Laplacian is

`(lambda_i c_i³/r_i) D²phi[(D_x phi,1+lambda_i phi_t)]`.

Thus (L) yields the upper-test inequality

`D²phi[(D_x phi,1+lambda_i phi_t)] >= -(r_i/(c_i lambda_i)) [lambda_i|D_x phi|²+(1+lambda_i phi_t)²]`,       (A)

and the lower inequality with the positive right side. The right side tends to zero uniformly on compact jet sets by (F). This is the actual forcing calculation, not the assertion that rescaling preserves a homogeneous equation.

For completeness, the input/output of the remaining reused fit operation is as follows. The available Lambda lambda_i fits at all nearby centers and all fixed multiples of r_i, together with `1/2<=|P|<=L+1`, give bounded normalized transverse and longitudinal coefficients

`p_i'=P_x/(c_i sqrt(lambda_i))`, `q_i'=(P_t/c_i-1)/lambda_i`

on every fixed box at every fixed fitting radius S. This follows from `lem:cylinder-comparison`: angular errors are O(sqrt(lambda_i)), norm errors O(lambda_i), and a finite chain connects the needed fits. The physical cylinder contains in normalized coordinates

`|l|<=S/2`, `|h-p_i' l/(1+lambda_i q_i')|<=S`.

Its error after division is `<=Lambda S/c_i`. These statements involve only function values, affine fits and Euclidean geometry. In particular their proof does not use a homogeneous PDE for U_i. Small S then gives equicontinuity; a fixed enclosing fit gives local boundedness. Hence V_i have a locally uniform limit V on all of `R^d x R`.

Passing (A) through strict upper/lower contacts gives the exact PDE `D²V[(D_xV,1)]=0`. At any center and any target radius R, take S=4R and a subsequential limit of the bounded fit coefficients. The shear tends to p, and the limiting fit error is at most `8Lambda R=256R`. This supplies the precise C0=256 hypothesis of `thm:liouville`, separately for every center and radius; there is no uncountable diagonal requirement because the function V is already fixed.

Finally V cannot be affine. If `V=p.x+qt`, the physical slopes `c_i(sqrt(lambda_i)p,1+lambda_i q)` are nonzero and their lambda_i-cylinders lie in a fixed normalized box. Uniform convergence gives a residual `o(lambda_i r_i)` on that entire cylinder. The allegedly bad parameter lambda_i would then be good. This contradiction is exactly the equation-independent final step of `prop:nonaffine-limit`.

The stipulated Liouville theorem now contradicts nonaffinity. Therefore some `B<infinity`, `gamma>0`, `s0>0`, depending only on d, satisfy `b(s)<=B s^gamma`. Reduce gamma to at most one. This is a **power bound**, not a compactness-only modulus.

### 3.7 Extracting actual derivatives; completing R

For centers in B1/2 and small r, choose good parameters `lambda=A r^gamma` with A fixed. On dyadic scales r_j the inscribed radii are `rho_j=sqrt(A) r_j^{1+gamma/2}` and errors `A r_j^{1+gamma}`. Comparing consecutive affine fits on the common inscribed ball gives

`|P_j-P_(j+1)|<=C r_j^{gamma/2}`.

The tail is summable uniformly in functions and centers. Consequently `P_j->P_infinity`, and for `rho_(j+1)<|h|<=rho_j`,

`|U(z+h)-U(z)-P_infinity.h| <= C |h|^{1+a_d}`, `a_d=gamma/(2+gamma)`.

This proves existence of the derivative at every point, not just an almost-everywhere assertion. Compare the expansions centered at z,z' and evaluated at z'+|z-z'|e for every unit e to obtain `|DU(z)-DU(z')|<=C|z-z'|^{a_d}`. This proves a uniform C¹,a_d bound for the entire lifted class. Restrict to t=0.

For general u,f put `M=osc u+||f||_infinity`. If M>0, `(u-u(0))/M` solves a normalized equation with oscillation and forcing norm at most one, so its lift belongs to the class. Multiplication back proves (R); if M=0 the result is immediate. Covering B3/4 by balls at a fixed distance from the outer sphere proves the asserted enlarged-interior variant. On B_(2R)(z) this also reads

`||Du||_(B_R)+R^{a_d}[Du]_(C^{0,a_d}(B_R)) <= C_d(osc_(B_(2R))u/R + R||f||_infinity)`.

The R factor on forcing is fixed by normalized spatial scaling. No boundary C¹ estimate or endpoint a_d=1/3 is claimed.

## 4. Quantitative value comparison and proof of S

Put `kappa=epsilon/m²` and set

`T_+(s)=s+kappa(2s-s²)`, `T_-(s)=s+kappa(s²-1)` for 0<=s<=1.

Both derivatives are at least one on this interval. We have `T_-<=s<=T_+`, and the deviations are at most kappa. Set `w_+=T_+(v)`, `w_-=T_-(v)`. They are continuous to the boundary and C¹ inside, and `|Dw_±|>=m` there.

At a test of a composition, apply the inverse of T to the test to obtain a test for v. Since Dv exists and never vanishes, the gradient at contact is T'(v)Dv, and the chain rule in this test calculation gives

`Delta_inf^N T(v) = T'(v) Delta_inf^N v + T''(v)|Dv|²`

as viscosity inequalities. Therefore w_+ is a supersolution with `Delta_inf^N w_+<=-2epsilon`, and w_- a subsolution with `Delta_inf^N w_->=2epsilon`. The composite has strictness in the direction needed for comparison with every u having `|f|<=epsilon`.

Here is a direct strict-comparison proof, avoiding an assumption of general uniqueness for sign-changing f. If u-w_+ has a positive maximum, maximize

`u(x)-w_+(y)-|x-y|²/(2eta)` on the closed product ball.

For small eta the maximizers lie in a common compact subset of the open ball and their separation tends to zero. Differentiability in y gives the common jet gradient `p=(x-y)/eta=Dw_+(y)`, so |p|>=m. The theorem of sums gives `X[p]<=Y[p]`, whereas the viscosity inequalities give

`X[p]>=-epsilon|p|² > -2epsilon|p|² >= Y[p]`,

a contradiction. The lower comparison between w_- and u is identical, with reversed signs and differentiation in the smooth-composite variable. Thus `w_-<=u<=w_+` and `||u-v||<=kappa`. For epsilon=0 one can use arbitrary kappa>0, then let it decrease to zero.

Since kappa<=1, `osc u<=1+2kappa<=3`. Theorem R on B3/4 gives a common C¹,a_d bound for u and v depending only on d. For x in B1/2, unit e, and `0<h<=1/8`, their Taylor expansions give

`|(Du(x)-Dv(x)).e| <= 2kappa/h + C_d h^{a_d}`.

Choose `h=min(1/8,kappa^{1/(1+a_d)})`. Taking the supremum over e proves S. This last interpolation is technical; the contribution being submitted is **Section 3's proof of the previously unassumed forced-gradient estimate**, together with a quantitative comparison of the actual solutions. Neither ingredient is replaced by a homogeneous interpolation assumption.

## 5. Route A: p-energy and isotropic replacement, with its unpaid term

Before closing Route B, the distinct variational route was pursued for actual p-harmonic functions. Let w be p-harmonic, ell(x)=a.x+c, `||w-ell||_(B1)<=delta`, and `0<=zeta<=1` be compactly supported. Testing the weak equation with `zeta^p(w-ell)` and using Hölder gives exactly

`||zeta Dw||_p <= |a| ||zeta||_p + p delta ||Dzeta||_p`.                  (P)

Indeed the identity has left side `integral zeta^p |Dw|^p`, and the two right-side terms are `integral zeta^p |Dw|^{p-2}Dw.a` and `-p integral zeta^{p-1}(w-ell)|Dw|^{p-2}Dw.Dzeta`. Dividing by `||zeta Dw||_p^{p-1}` gives (P), with the zero case immediate.

To use this around a C¹,a_d limiting function on radius r requires control of

`p (delta_p/r + C r^{a_d})`.

Even the established value rate delta_p=O(p^{-1/4}) does not make its minimum small: it is of order `p delta_p^{a_d/(1+a_d)}`. This does not close, even using the better positive-gradient value rate O(p^{-1/2}). Testing a monotonicity inequality instead leaves weights of the form |Dw|^{p-2}; a lower bound for the limit gradient is not a lower bound for the approximating gradients and cannot simply be divided into that weight.

An isotropic homogeneous-replacement iteration has a related problem. Source C¹,a_d applied to a replacement h bounds its Taylor error by its **full** oscillation, not by the excess of h over a nonzero affine function. Subtracting that affine function changes the equation; for `u=x1+eta w` the leading shifted limit is `w_11=0`, which has arbitrary transverse functions. No uniformly elliptic large-shift compactness theorem may be substituted for this rank-one limit. Route A remains unpaid and is not nominated. In particular no p-to-infinity gradient theorem is inferred from S.

## 6. Active obstruction checks

### 6.1 Bounded forcing permits at most the 1/3 uniform Hölder exponent

On a ball in dimension at least two let

`u_k(x)=x1+k^{-4/3} sin(k x2)`.

Its gradient never vanishes, `Delta_inf u_k=-cos²(kx2)sin(kx2)`, and

`Delta_inf^N u_k= -cos²(kx2)sin(kx2)/(1+k^{-2/3}cos²(kx2))`.

Thus forcing and oscillation are uniformly bounded. Between x2=0 and x2=pi/k, the transverse derivative changes by `2 k^{-1/3}`. A uniform C¹,a estimate with a>1/3 is impossible, including in a nonvanishing-gradient class. Multiplying by a fixed constant makes oscillation and forcing at most one. Also `||u_k-x1||<=k^{-4/3}` while the gradient difference is k^{-1/3}; the bounded-forcing flatness-to-gradient exponent cannot exceed 1/4 in this local, no-boundary-agreement test. This does not purport to refute S.

### 6.2 Same-boundary small forcing forbids a universally linear gradient rate

Fix a smooth cutoff chi compactly supported in B3/4 and identically one on B1/4. For small a>0 put

`u_a(x)=x1+a² chi(x) sin(x2/a)`, `v=x1`.

The boundary data agree exactly. `D_1u_a=1+O(a²)`, `D_2u_a=O(a)`, and the other derivatives are O(a²). The Hessian entries of the perturbation are O(1) for (2,2), O(a) for pairs with exactly one index 2, and O(a²) otherwise. Consequently `||Delta_inf^N u_a||<=C_chi a²`, while `|Du_a(0)-Dv(0)|=a`. The forcing is smooth because |Du_a|>=1/2. At every fixed a the equation is classical, hence also viscosity. A bound `||Du-Dv||<=C||f||^theta` with theta>1/2 is impossible even for an affine nonvanishing limit. A fixed amplitude normalization gives `0<=v<=1` and changes only constants. This does not contradict b_d<=1/4; it rules out an unjustified linear stability upgrade. No bound on Df is claimed for this example.

### 6.3 Deliberate limitations

The composite-barrier proof uses inf |Dv|>=m on the whole open ball and loses m^{-2}. Critical gradients of u remain fully covered by R, but critical gradients of the comparison v are not covered by S. No removal of m, universal optimal exponent, C¹ forcing-norm rate, p-independent gradient regularity, or boundary gradient convergence is asserted. The analytic candidate is the forced-class power estimate and its nonvanishing-comparison consequence, not a routine consequence obtained by assuming that estimate.


## Prior complete document frontier/reviews/i228-forced-infinity-proof.md

# I228 — independent proof gate for I224

## Partial review (before completion of source-contract checking)

The gate is pending. I have read the complete submitted analytic argument, AGENTS.md, sources/upstream.json, and the pinned section 02-flatness.tex. All pinned results and lower operations are stipulated; this review concerns their applicability only. No other active review has been read.

The lift and quadratic-cone calculation have the required signs. The source three-point operation defines its third gradient as -2p0 and evaluates its third matrix on p0. For the enlarged class the third lower bound is indeed -2F0|p0|², after dividing the -2p0 inequality by four. Thus the candidate's bounded forcing correction survives that otherwise delicate normalization. The source penalty Hessian is independent of the equation and its negative r^(-1/2) term dominates the resulting bounded error.

Remaining checks include the full reduction/cylinder contracts, the simultaneous choice of slow tangent scales, all-center/all-scale compactness, and the final strict comparison. This partial record is not a proof approval or a contribution verdict.

## Final independent verdict

**PASS for both Theorem R and Theorem S, relative to the stipulated pinned theorems and lower operations.** I found no substantive unpaid estimate in the complete I224 candidate. The enlarged inequality class, forced three-point estimate, strengthened bad-scale selection, exact homogeneous limiting equation, and derivative extraction are compatible. The value comparison in S has the correct signs and does not require differentiability of the forced solution. This verdict does not certify literature novelty or authorize an accepted-count change.

This is an independent check of the actual candidate and actual source contracts, not an acceptance of the phrase “same argument.” The expansions below specify how the source operations apply. The initial partial review above was written before reading the complete reduction source; this final verdict supersedes its pending status.

### 1. Exact scope of the conclusions

For each integer d≥3, R provides dimension-only a_d∈(0,1/3] and A_d<∞ such that every bounded u∈C(B1) solving the normalized equation with bounded continuous f satisfies

    ||Du||∞,B1/2 + [Du]C^(0,a_d)(B1/2)
      ≤ A_d (osc_B1 u + ||f||∞,B1).

The critical-jet convention is -λ_max(X)≤f for an upper test with p=0 and -λ_min(X)≥f for a lower test with p=0. No existence or uniqueness assertion for arbitrary signed f is needed.

For S, v∈C(cl B1) is infinity-harmonic, 0≤v≤1, and inf_B1|Dv|≥m with 0<m≤1. For 0<ε≤min(1,m²), every existing u∈C(cl B1) with the same boundary values and continuous |f|≤ε has

    ||u-v||∞,B1 ≤ κ,
    ||Du-Dv||∞,B1/2 ≤ C_d κ^(a_d/(1+a_d)),   κ=ε/m².

The nonvanishing condition is on all of B1 for v. There is no assumed gradient bound or differentiability for u. The proof supplies local C¹,a_d regularity at every interior point through R and fixed-radius coverings.

### 2. Source interface actually checked

I read in full the pinned manuscript's sections 01-introduction.tex, 02-flatness.tex and 03-reduction.tex in the reused corpus. Their Git blob hashes were independently matched to sources/preprints-tree.json. The relevant contracts are:

* `thm:main` and `cor:interior-c1`: exact infinity-harmonic functions; used for the comparator v, never substituted for forced regularity.
* `lem:cone-slopes`, `prop:affine-blowups`: source monotonicity and the fixed-center affine-tangent argument. For forced functions the candidate proves the perturbed slope inequality first; the source's terminal argument is then used only for an exact homogeneous limit with constant origin slopes.
* `lem:sum-rule`: continuous functions, an interior product maximum, a C² penalty, closed superjets, and diag(X_j)≤A+ηA². This operation itself assumes no PDE.
* `prop:three-point`: its original theorem assumes exact infinity-harmonicity. The candidate does not meet that theorem verbatim. Instead it reuses its equation-free localization/Hessian calculation and replaces each of its three jet inequalities; these replacements are checked below.
* `lem:family-flatness`: the needed inputs are uniform bounds/Lipschitz control, closure, affine fixed-center tangents and the all-separation three-point estimate. The candidate establishes each for the enlarged class.
* `lem:bad-scales`: the relevant selection and boundary-distance estimates use the scalar modulus b and goodness definition. The stronger selection remains valid.
* `lem:cylinder-comparison`: same function, same parameter θ², slopes in [c_*,C_*], concentric radii H≤H'≤2H or equal radii with axial/transverse center offsets ≤H/4, θH/4. No equation appears in this contract or its proof.
* `prop:nonaffine-limit`: its source statement is attached to the homogeneous family. Its proof separates geometric compactness and nonaffinity from one PDE-stability passage. All geometric hypotheses are supplied here; that PDE passage is replaced by the calculated vanishing-forcing passage.
* `thm:liouville`: every m≥1, a continuous entire solution of D²V[(D_xV,1)]=0, and one finite constant C0 for fits at every center and every R>0 on |ℓ|≤R, |h-pℓ|≤R. It imposes no differentiability hypothesis on V. Here m=d and C0=256.
* The final part of section 03 extracts actual derivatives from the power-law cylinder fits. It uses only those fits and the common Lipschitz bound.

I did not audit these pinned results. Sections 04–08 and their internal Liouville proof are not needed to check this interface and were not read. No other active review was opened.

### 3. Closure, Lipschitz control, slopes and tangent functions

Write I_F for the pair of test inequalities

    X[p] ≥ -F|p|² at upper tests,
    X[p] ≤  F|p|² at lower tests.

Both operators are continuous in (p,X), including p=0. Strict-contact stability therefore proves closure under locally uniform limits. The algebraic lift identity, normalization at zero, and oscillation bound also pass to limits. Closure does not assume a derivative exists.

For an upper test φ of U(y,t)=w(y)+t one has φ_t=1. If p=D_yφ≠0, the affine graph with Dℓ·p=1 makes φ(y,ℓ(y))-ℓ(y) an upper test for w and gives

    D²[φ(y,ℓ(y))-ℓ(y)][p] = D²φ[(p,1)].

The normalized equation bounds this below by -F|p|², which is at least -F|(p,1)|². If p=0, vertical restriction gives φ_tt≥0 and the required bound. Lower tests give the other inequality. Thus every normalized solution enters I_F after lifting; the full test gradient of a lift is never zero. This does not replace the original normalized convention with a different equation.

For the radial upper barrier C in I224 §3.2, C'=L_R^++F'(R-ρ)>0 for 0<ρ<R and C''=-F'. Thus Δ∞C=-F'|DC|²<-F|DC|². Its outer-boundary excess is F'R²/2≥0, and it agrees at the center. A positive maximum must be away from the center and boundary, where C is C², giving a contradiction. Division by the radius and F'↓F proves

    L_r^± ≤ L_R^± + FR.

Fixed-radius oscillation bounds give common local Lipschitz bounds, including a common bound on cl B7/8 for the normalized lifts. For each fixed center, the last display makes limsup_r L_r^± no larger than liminf_R L_R^±. Hence finite limits exist. At a positive maximizer h_r, the value at the old center is a permitted negative increment from z+h_r, so L_r^+(z)≤L_r^-(z+h_r). The FR error vanishes only after first using continuity at fixed R and then R↓0. This proves equality of the two limiting slopes. No uniform continuity of infinitesimal slopes is being assumed.

For H_j(X)=(W(z+r_jX)-W(z))/r_j the forcing constant is r_jF. Every locally uniform limit H is therefore an exact entire infinity-harmonic function. Its positive and negative origin slopes equal the same L_* at every radius. The source's final cone argument applies to this H: origin growth gives |H(X)|≤L_*|X|; comparisons with increasingly large balls give global L_*-Lipschitz control. Opposite extremizers saturate this bound, lie on opposite rays of a single line, and sending the two line endpoints to infinity forces H(X)=P·X. When L_*=0, H=0 directly. Thus these are actual linear, degree-one homogeneous tangent functions. Their slopes need not yet be unique, and the proof does not claim otherwise.

### 4. Forced three-point operation: all jet constants and signs

Let W_i satisfy I_Fi with F_i≤F0, have a common Lipschitz bound L, and converge uniformly to affine ℓ_i. Evaluations at ±e/2 bound q_i=Dℓ_i; hence W_i-ℓ_i have one common Lipschitz bound C. Negative midpoint defects are reduced to positive defects by changing both signs, which preserves I_Fi.

For a fixed violating δ>0 use exactly the source penalty, including the affine terms in Ψ. Its equation-free localization gives r≤8||W_i-ℓ_i||∞/(δν)→0, |h|≤2Cr², and interior maximizing triples after choosing B_out>(C+3C²/2)/ν. The cutoff B and its first two derivatives are fixed in i. With e=(x-y)/r and f0(r)=r-r^(3/2)/8, the jet vectors are

    p1=q_i+f0 DB/2-h/r²+a e,
    p2=q_i+f0 DB/2-h/r²-a e,
    p0=q_i-h/r²,
    a=B f0'-2|h|²/r³ ≥ δ/4

for all sufficiently large i. These vectors are uniformly bounded. Crucially the third superjet, for -2W_i, has gradient -2p0, not p0.

An upper jet (p,X) for -2W corresponds to the lower jet (-p/2,-X/2) for W. Its inequality gives X[p]≥-2F0|p|². At p=-2p0, division by four gives X3[p0]≥-2F0|p0|². The other two bounds are X1[p1]≥-F0|p1|² and X2[p2]≥-F0|p2|². This also holds if any vector vanishes; no normalization by its length is performed.

Apply the matrix inequality to σ=(p1,p2,p0). At each fixed maximizing triple let η↓0; the matrices may depend on η, but their uniform scalar lower bound does not. It follows that

    A[σ] ≥ -F0(|p1|²+|p2|²+2|p0|²).

The right side is bounded independently of i. The source's second variation gives r'=2a, r''=0, c'=O(1), h'=-(f0/2)DB=O(r). The |h|²/r² term has bounded second variation, as do the cutoff cross terms; the remaining term is

    B f0''(r)(2a)² = -3B a²/(8√r).

It tends to -∞. This contradicts the bounded lower bound and proves T for the enlarged class, uniformly over every nonzero endpoint separation. No derivative of f or of W_i was inserted. Subtracting ℓ_i was used for the maximum, not as an assertion that the PDE is invariant under affine subtraction.

### 5. Moving centers and tiny separations

Uniform bounds on cl B7/8 give a uniformly convergent subsequence U_i→U0 there and z_i→z_*∈cl B3/4. This limit point is interior to B7/8 even when D(z_i)→0. Choose R_i↓0 dominating r_i, |z_i-z_*| and the uniform error. Such a choice is compatible with affine tangents because every chosen R_i sequence has an affine-tangent subsequence; no preselected tangent scale has to dominate the errors.

The R_i-blowups converge uniformly on B1 to that affine function, are uniformly Lipschitz, and satisfy I_Ri. T applies with a common bounded forcing constant. For H,K∈cl B2, the points z_i+r_iH and z_i+r_iK lie in B_(R_i/4)(z_*) eventually. Substitution in T and division by r_i gives their midpoint defect bounded by ε_i|H-K|, with ε_i→0. The r_i-blowups have an affine limit on B2 by continuity and midpoint subdivision. Exact vertical increments give its slope P·e_t=1.

Uniform error <δ on B2 then provides a fit for the actual allegedly bad λ_i≥δ on its cylinder, since that cylinder lies in B2. I224's phrase “bad delta-cylinder” should be read this way: δ is the error threshold, while the failed parameter can be λ_i. This is a wording clarification, not a missing mathematical step. No monotonicity of goodness in λ is required.

### 6. Strengthened selection and geometric compactness

Failure of every power bound makes b(s)s^(-γ) unbounded near zero for each γ>0. For γ_i↓0 with γ_i≤1/2, take a factor-two approximate maximum on a truncated interval large enough that its value exceeds both i and the supremum on [1/i,1/8]. This gives the stated running-maximum inequality, s_i<1/i, and b(s_i)/s_i^γi≥i. Approximate suprema then give a bad λ_i with b(s_i)/4<λ_i≤b(s_i). In particular λ_i→0 and

    r_i/λ_i ≤ 4D(z_i)s_i/b(s_i)
             ≤ 3s_i^(1-γ_i)/i → 0.

For fixed M≥2, D(z)≥D(z_i)/2 at |z-z_i|≤Mr_i eventually. Every r≤Mr_i is admissible, and

    β_Ui(z,r) ≤ b(2Ms_i)
       ≤2b(s_i)(2M)^γi <32λ_i<1.

Thus Λλ_i is good for all these centers and all these radii, with Λ=32. The index threshold may depend on M; the parameter Λ does not. Strengthening the maximum did not discard the small-radius fits.

Here is the full geometric input to the reused compactness operation. For θ_i²=Λλ_i, the lift's exact vertical increment gives 1/2≤|P|≤L+1 for every relevant fit eventually. At the base center, compare successively doubled radii from r_i to Rr_i. The source cylinder lemma yields O(θ_i(1+log R)) direction error and O(θ_i²(1+log R)) norm error. Given a normalized box of size K, choose fixed R≫K(1+log R); the box then lies in the enclosing fit with the lemma's quarter-radius margins. Compare fits at each box center at radius Rr_i with that enclosing fit, then use a finite sequence of doublings/halvings to Sr_i for any fixed S>0. These operations satisfy exactly the two center/radius alternatives of the source lemma. The number of comparisons depends on K,S, not i.

After rotation and normalization this gives |p_i'|+|q_i'|≤C_(K,S). The cylinder decomposition in the source gives the contained domain

    |ℓ|≤S/2,   |h-p_i'ℓ/(1+λ_iq_i')|≤S

and error ≤ΛS/c_i. A large enclosing fit bounds the functions on each box. For equicontinuity, first choose S so 2ΛS is small, then choose the increment small relative to the finite bound C_(K,S). There is no need for C_(K,S) to remain bounded as S↓0. This proves locally uniform subsequential convergence on the exhausted entire space without any PDE regularity estimate. The source's geometric operation is therefore applicable, not merely asserted applicable.

### 7. Actual limiting PDE, full Liouville fits and nonaffinity

The rescaling has physical gradient c_i(√λ_i D_xφ,1+λ_iφ_t) and Hessian

    (c_i/r_i) [ D_xx²φ       √λ_i D_xtφ
                √λ_i D_txφ  λ_i φ_tt ].

Its infinity Laplacian is (λ_ic_i³/r_i)D²φ[(D_xφ,1+λ_iφ_t)]. Thus upper tests satisfy precisely

    D²φ[(D_xφ,1+λ_iφ_t)]
      ≥ -(r_i/(c_iλ_i))
         (λ_i|D_xφ|²+(1+λ_iφ_t)²),

with the opposite lower bound for lower tests. Because c_i≥1/2 and r_i/λ_i→0, the residual tends to zero uniformly on compact jet sets. Strict-contact stability gives the exact homogeneous equation D²V[(D_xV,1)]=0. The limit is not a solution with a retained forcing or a merely formal linearization.

For every fixed center and R>0, use the geometric fit at S=4R and extract its bounded coefficients along a further subsequence. The shears converge to p; the larger contained domain has strict margins around |ℓ|≤R, |h-pℓ|≤R. Local uniform convergence gives the required estimate with one C0=8Λ=256. Set a=q+|p|²/2 to match the source notation. The coefficient subsequence may depend on the center and radius because V has already been fixed. This establishes the full quantifiers in `thm:liouville`.

If V=p·x+qt, the nonzero physical slopes c_i(√λ_i p,1+λ_iq) have λ_i-cylinders inside one fixed normalized box. The residual there is r_ic_iλ_i(V_i-p·x-qt)=o(r_iλ_i), so λ_i is good eventually. This contradicts its selection. This last step uses neither an equation nor derivatives. The exact Liouville theorem contradicts the resulting nonaffine entire limit and hence proves a dimension-only power bound for b.

### 8. Derivatives at every point and the estimate in R

Choose A strictly larger than the power-law constant times (1/4)^(-γ); this strictness puts Ar^γ above β even though goodness need not be monotone. The same small r0 works for every center in cl B1/2. On r_j=2^(-j)r0 the inscribed radii are ρ_j=√A r_j^(1+γ/2). Subtracting two fits on B_ρ(j+1) bounds |P_j-P_(j+1)| by Cr_j^(γ/2). Its geometric tail converges uniformly.

For ρ_(j+1)<|h|≤ρ_j, divide the fit error by |h|, using the lower bound ρ_(j+1), and add the slope tail. This gives a uniform remainder C|h|^(1+a), a=γ/(2+γ). Hence DU exists at each center; no almost-everywhere differentiation theorem or inhomogeneous differentiability input is used. Comparing the two center expansions at z', z'+|z-z'|e gives the uniform Hölder gradient estimate. For larger separations use the Lipschitz bound. Reducing γ≤1 gives a≤1/3.

For M=osc u+||f||∞>0, division by M sends f to f/M and oscillation to at most one. This is valid also at zero-gradient tests because both Hessian eigenvalues scale by 1/M. Multiplication back proves R; M=0 means u is constant. Fixed-radius interior coverings give the B3/4 version and local C¹,a regularity. Spatial rescaling gives the stated forcing factor R||f||∞ in the radius-R gradient bound. These are dimension-only constants.

### 9. S: strict barriers, critical jets and interpolation

With κ=ε/m², T_+'=1+2κ(1-s)≥1 and T_-'=1+2κs≥1 on [0,1], while T_+''=-2κ and T_-''=2κ. Their boundary ordering and deviations ≤κ are correct. The comparator v is C¹ locally by the pinned homogeneous theorem; its nonvanishing gradient ensures every test for v or T_±(v) has nonzero gradient.

If φ is a lower test for T_+(v), apply the local increasing C² inverse of T_+ to φ. The resulting lower test for v has normalized infinity Laplacian ≤0. The test chain rule gives Δ∞^Nφ≤-2κ|Dv|²≤-2ε. Thus w_+ is a strict supersolution of -Δ∞^Nw≥2ε. Upper tests of w_- similarly give Δ∞^Nφ≥2κ|Dv|²≥2ε. C² regularity of v or w_± is unnecessary; the inverse is applied to the C² test.

If u-w_+ has positive maximum, the doubled-variable maxima approach the positive diagonal maximum set, which is a compact subset of B1 because the boundary difference is nonpositive. At such an interior maximum, differentiation only in the w_+ variable gives p=(x-y)/η=Dw_+(y), with |p|≥m. The theorem of sums for u and -w_+ gives X≤Y and thus X[p]≤Y[p]. The upper inequality for u and lower inequality for w_+ give

    X[p] ≥ -f(x)|p|² ≥ -ε|p|²
          > -2ε|p|² ≥ Y[p].

For the lower barrier, maximize w_-(x)-u(y)-|x-y|²/(2η). Now p=Dw_-(x), |p|≥m, and

    X[p] ≥ 2ε|p|² > ε|p|² ≥ Y[p],

where Y[p]≤-f(y)|p|²≤ε|p|². Both contradict X[p]≤Y[p]. Closed-jet inequalities are legitimate: the gradients stay nonzero and the operators and f are continuous there. No critical jet is discarded on assumption; the comparator's gradient excludes such a jet at these particular contacts. Elsewhere, R covers critical gradients of u through its lifted test argument. This proves w_-≤u≤w_+ and the value estimate without sign-changing uniqueness.

For ε=0 one can use any κ>0, with strict gap 2κm², and let κ↓0; this avoids relying on a non-strict doubled-variables argument. In the stated positive-ε theorem, κ≤1 gives osc u≤3. R on B3/4 gives common dimension-only C¹,a bounds. It applies to v as well: nonzero Dv makes the homogeneous unnormalized and normalized tests equivalent, or its exact lift directly belongs to the same inequality class. For x∈B1/2 and h≤1/8 the segment remains in B3/4, and

    |(Du-Dv)(x)·e| ≤ 2κ/h+C_d h^a.

Take h=min(1/8,κ^(1/(1+a))). When the minimum is capped, κ is bounded below by a fixed dimension-only threshold, so enlarging C_d gives the same κ^(a/(1+a)) estimate. Thus S follows with its stated quantifiers and no m-dependence outside κ.

### 10. Limitations, minor wording and provenance

The only corrections I would request are expository: §3.4 should call the eventual fitted parameter λ_i rather than δ, and §4's “smooth-composite variable” should say C¹ comparator variable. Neither changes the argument, adds a hypothesis, or changes this PASS verdict. The explicit expansions above supply the abbreviated source applications without discovering a new estimate or repairing a failed theorem.

The auxiliary p-energy route is not needed for R or S and remains unsubmitted. The supplied oscillatory examples are consistent with a≤1/3 and b≤1/4; they do not contradict either theorem. This gate does not extend the candidate to arbitrary-source existence, boundary gradient estimates, removal of inf|Dv|≥m, an optimal exponent, or p-to-infinity gradient convergence.

Exact source/read scopes and hashes are in `frontier/experiments/i228_forced_infinity_proof/input-authentication.json` and `frontier/sources/i228_forced_infinity_proof/literature.md`. Only the three authorized output paths were written. No research code, experiments, tests, snapshots, seals, shared edits, staging, commits, publication, subordinate agents or other active reviews were used. Hashing/extraction were provenance operations. Contribution remains a separate parent gate.


## Prior complete document frontier/reviews/i229-forced-infinity-contribution.md

# I229 — independent contribution gate for forced infinity regularity

**Final verdict: DOES NOT CLEAR the original brief's stringent independent-contribution gate.** Theorem R is a meaningful enlargement of the solution class and is not the theorem stated in any of the primary comparisons below. Nevertheless, relative to the **full stipulated pinned proof package**, its submitted proof is a technical bounded-forcing extension of that package. The two nominated additions do not supply a sufficiently independent, nonroutine bridge. Theorem S adds a useful restricted stability statement, but its barrier and interpolation are technical once R is available.

This is a contribution decision, not an I228 proof decision. I read the completed I224 argument, including its payment of the anisotropic forcing residual; I have not presumed that an earlier missing estimate remains missing. I have neither read I228 nor certified its outcome. No acceptance-count change is recommended. No worldwide priority assertion follows from the literature retrievals.

## 1. Exact object being judged

For each integer d≥3, R asserts the existence of constants a_d∈(0,1/3] and A_d<∞, uniform over **every** bounded u∈C(B1) solving −Δ∞^N u=f for **every** f∈C(B1)∩L∞(B1), such that u∈C^{1,a_d}(B1/2) and

    ||Du||∞ + [Du]a_d ≤ A_d (osc_B1 u + ||f||∞).

The displayed norms are on B1/2. Neither a modulus of continuity of f, a derivative of f, its sign, semiconcavity of u, nor a lower bound on |Du| is assumed. The result quantifies over existing solutions and does not assert existence or uniqueness for arbitrary sign-changing data. On B_(2r)(z), the corresponding right side for the gradient estimate is C(osc u/r+r||f||∞), with r^{a_d} on its seminorm term.

S restricts to 0<m≤1, 0<ε≤min(1,m²), an infinity-harmonic v∈C(cl B1) with 0≤v≤1 and inf_B1|Dv|≥m, and any existing u∈C(cl B1) with the same boundary trace and continuous forcing ||f||∞≤ε. It asserts actual continuous interior gradients and

    ||u−v||∞,B1 ≤ ε/m²,
    ||Du−Dv||∞,B1/2 ≤ C_d (ε/m²)^{a_d/(1+a_d)}.

Only v has the nonvanishing-gradient assumption, over the whole open ball. This is not a boundary-gradient estimate, a p-to-infinity theorem, or a stability result through critical points of v.

The normalized convention is essential: at an upper test with p≠0, −X[p]/|p|²≤f; at p=0, −λmax(X)≤f. Lower tests use ≥ and λmin. Multiplying the nonzero-gradient equation by |p|² does not preserve this full critical-gradient convention. In particular, Lindgren's unnormalized theorem cannot simply be relabeled as R.

## 2. Exact overlap with the stipulated source

The pinned [main statement](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections/01-introduction.tex), `thm:main`, concerns exact Δ∞u=0, d≥3, and a dimension-dependent nonexplicit exponent. It does not assert R. Its lower operations, however, contain almost the entire submitted mechanism:

* [02-flatness.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections/02-flatness.tex): linear lift; cone slopes and fixed-center affine blow-ups; theorem of sums; the three-point penalty, its localization, bounded contact gradients, and its negative Hessian divergence.
* [03-reduction.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections/03-reduction.tex): slow-scale transfer to uniform family flatness, worst bad-parameter modulus, factor-two running maxima, all-nearby-center/all-fixed-scale fits, cylinder comparison, anisotropic normalization, compactness, passage of every required shear fit, nonaffinity, and summable slope extraction.

The exact Liouville contract in `thm:liouville` is an entire continuous solution of D²V[(D_xV,1)]=0 on R^m×R, m≥1, with one C0 and affine fits at every center and every R>0 on |l|≤R, |h−pl|≤R. The time coefficient q is unrestricted: q=a−|p|²/2. The theorem is not an inhomogeneous Liouville theorem. The candidate does not claim that it is: Section 3.6 attempts to produce precisely this homogeneous limit with C0=256.

`lem:cylinder-comparison` is explicitly equation-independent. Its inputs are fits for the same function, common parameter θ², comparable radii or the specified overlapping centers, and positive uniform upper/lower bounds for slope norms. The geometry and compactness portion of `prop:nonaffine-limit` then consumes those fits. Reusing it does not require solving a new geometric or Liouville problem. The source's PDE verification must still be replaced, rather than treating the whole proposition as a black box for forced functions.

The complete family-377 path list contains one manuscript; the matching README, main file, bibliography and sections 01–03 were read. No forced companion statement was found in that bounded same-family check. This is not a semantic search of every other manuscript.

## 3. The genuinely relevant changes, assessed as submitted

### 3.1 Preliminary forcing and flatness steps

The candidate uses the closed inequalities X[p]≥−F|p|² at upper tests and X[p]≤F|p|² at lower tests for the lifted function. The affine graph test and the vertical test at horizontal gradient zero are the source lift calculation with an error bound retained. Its cone calculation inserts quadratic curvature F and gives L_r^±≤L_R^±+FR. Linear blow-ups eliminate this O(rF) error. These are useful checks, but almost-monotone slopes and affine blow-ups for bounded inhomogeneities already have close primary precedent in Lindgren; quadratic comparisons for the normalized equation are explicit in Lu–Wang.

### 3.2 Three-point extension

The important submitted observation is that the **same** source penalty still yields

    A[σ] ≥ −C(F0,L,δ),
    A[σ] = −3B a²/(8√r) + O(1) → −∞.

The lower bound accounts for all three jets, including the factor 2 for −2W. No derivative of f is used. This is stronger than assuming C¹ bounds on u, and I do not dismiss it as final interpolation. But the source already supplies the entire penalty, r→0, h=O(r²), bounded test gradients, a≥δ/4, and the divergent negative term. Replacing its lower bound zero by a fixed negative constant leaves the contradiction unchanged. No new penalty, coercive direction, compactness topology, or cancellation is introduced. Under the stipulated lower operations, this is the standard robustness check for bounded lower-order jet errors.

### 3.3 Scale selection and the limiting equation

The completed proof explicitly asks its existing factor-two running maximum to exceed i:

    b(s_i)/s_i^{γ_i} ≥ i,   0<γ_i≤1/2,
    λ_i > b(s_i)/4,   r_i≤s_i D(z_i).

Consequently

    r_i/λ_i ≤ 4D(z_i)s_i/b(s_i) ≤ 3s_i^{1−γ_i}/i → 0.

This is an actual payment of the forcing residual, not a missing estimate. But failure of every power bound already gives an unbounded running maximum near zero. Requiring it to exceed i is free within the source selection; it is not a new estimate on solutions. The nearby fit bound remains the source's 8λ_i(2M)^{γ_i}<32λ_i for each fixed M.

Under the source's anisotropic change of variables the error is

    r_i/(c_i λ_i) · {λ_i|D_xφ|²+(1+λ_i φ_t)²},   1/2≤c_i≤L+1.

Thus it vanishes on compact jet sets. The remainder of the argument uses the unchanged source fit passage, same shear, same C0=256, same nonaffinity contradiction, and same exponent conversion a_d=γ/(2+γ). The candidate has correctly identified the place where naive isotropic perturbation would be inadequate; nevertheless its repair uses only slack already present in the stipulated running-maximum construction.

Taken together, these changes establish a plausible **robustness corollary of the source proof**, conditional on the separate proof gate. Calling the resulting theorem important does not make these modifications a new independent method. Under a looser standard accepting useful new corollaries, R would merit recording; under the original express exclusion of standard transfers, I would not nominate it as the tenth substantial finding.

## 4. Primary literature comparison and limits

**Lindgren (Proc. AMS 142 (2014), 277–288).** The accessible [manuscript transcription](https://doczz.net/doc/7566335/on-the-regularity-of-solutions-of-the) states Δ∞u=f with the unnormalized cubic-in-amplitude operator. Theorem 1 gives linear subsequential blow-ups for bounded continuous f; Theorem 2 assumes f∈C¹∩L∞ and gives uniqueness of the linear blow-up/differentiability, in arbitrary dimension. Its Section 2.1 raises dimension by adjoining linear and |t|^{4/3} variables to arrange slope and sign assumptions; Section 3 uses almost-monotone slopes and homogeneous blow-up limits. It does not state uniform Hölder gradient bounds. The author-page PDF link and AMS retrievals failed, so the retained evidence is an explicitly identified transcription, not an authenticated published PDF. Its malformed Definition 1 is not used to resolve viscosity conventions. This limits the bibliographic certainty, not the independent source-overlap calculation above.

**Crasta–Fragalà (arXiv:1506.05305v1).** [Definition 1 and introduction](https://arxiv.org/html/1506.05305v1) use the normalized critical-gradient convention stated above. Their main problem has source +1, zero boundary trace, and a bounded convex domain in R^N. Power concavity supplies local semiconcavity; [Section 4](https://arxiv.org/html/1506.05305v1#S4) supplies C¹. Theorem 16 separately requires local semiconcavity. Its displayed general operator notation and the proof's Δ∞^+ notation are not perfectly aligned; neither reading removes semiconcavity or supplies R's uniform Hölder estimate. Thus R's arbitrary interior solutions and arbitrary continuous sign-changing forcing are real differences.

**Lu–Wang (Comm. PDE 33 (2008), 1788–1817).** The [author-hosted article](https://www2.math.uconn.edu/~guozhenlu/papers/cpde_lu_wang_published.pdf), Theorems 1.7/2.2/2.4, provides normalized polar-quadratic comparison with continuous f in arbitrary dimension. Theorem 5.3 concerns uniform value stability around forcing bounded away from zero with one sign. Theorems 1.9/5.4 allow forcing tending uniformly to zero (no sign required for that sequence) and give uniform convergence of values, with the specified Lipschitz boundary data for the zero-forcing limit result. No gradient rate is asserted there. S has stronger gradient information conditional on R, but different boundary/gradient hypotheses; it should not be described as directly containing their whole theorem.

**Perturbation after homogeneous regularity.** [Imbert–Silvestre, arXiv:1201.3739v1](https://arxiv.org/abs/1201.3739), Theorem 1, assumes |Du|^γ F(D²u)=f, γ≥0, **uniformly elliptic** F with F(0)=0, and bounded f. Lemma 2's flatness improvement is uniform in every affine shift p; the proof identifies homogeneous limits. This is a primary example of the standard perturbative mechanism, not a theorem applicable to normalized infinity-Laplace. The latter's directional matrix has rank one: even at a nonzero gradient, there is no positive ellipticity constant in transverse directions. Replacing finite-p estimates by their p→∞ limit also lacks uniform constants. The full pinned anisotropic proof package, rather than this general theorem alone, is what makes I224's particular extension routine.

**Sobral–Teixeira–Urbano, October 9, 2026, arXiv:2610.13137v1.** [Theorems 1.1, 1.3, 1.4 and Section 3](https://arxiv.org/html/2610.13137v1) were checked. Theorem 1.1 concerns fixed p>2 and homogeneous p-harmonic functions; constants depend on p. Theorem 1.3 concerns homogeneous planar infinity-harmonic functions, every β<1/3. Section 3 expressly notes the one-direction large-shift obstruction and uses homogeneous C¹ compactness plus a separate quantitative near-affine result. Theorem 1.4 is a different nonlocal equation with its own differentiability/tail hypotheses. None automatically states R in d≥3 with forcing. The overlap is compactness, variable scales and slope reconstruction, not an identical forced theorem.

Therefore I do **not** assert that one of these external papers has already published R or S, or that homogeneous C¹,α regularity by itself entails R through an off-the-shelf uniformly elliptic theorem. The narrower conclusion is that the completed I224 argument is a routine extension **once the specified pinned lower operations are granted**. The alternatives “not explicitly in these papers” and “substantial independent contribution” are not equivalent.

## 5. S, proof separation, and record

For S, T_±'(s)≥1 and T_±''=∓2κ, κ=ε/m², give strict comparison barriers through Δ∞^N T(v)=T'(v)Δ∞^N v+T''(v)|Dv|². R then supplies common C¹,a_d bounds and the difference quotient gives 2κ/h+Ch^{a_d}. These are exactly the technical parts acknowledged by I224. The upper-exponent examples delimit stronger claims but do not provide a new positive regularity mechanism or establish optimality of the submitted exponent.

I checked the contribution-relevant use of the lower-operation hypotheses and the residual scaling, not the truth of any pinned theorem. I raise no alleged contradiction to the stipulated homogeneous source. My negative contribution verdict stands even if the separate proof gate passes; conversely it does not imply that proof gate passes. No I228 output or other active work was consulted.

A partial review was written before the final literature comparison. Exact input/output/source hashes, byte counts, and reading scopes are in `frontier/experiments/i229_forced_infinity_contribution/input-authentication.json`; the manifest's own hash is returned detached. No research code, numerical experiments, scans, tests, snapshots, seals, historical replay, shared edits, staging, commits, or publication were performed. Scripts were limited to retrieval, extraction, bounded source lookup, and hashing. An initial catalogue display was overly broad and truncated; only the family-377 catalogue passage was used, and no other review content was opened.
