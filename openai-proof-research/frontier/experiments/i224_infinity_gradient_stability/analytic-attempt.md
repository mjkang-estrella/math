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
