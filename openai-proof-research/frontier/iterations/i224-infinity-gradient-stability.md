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
