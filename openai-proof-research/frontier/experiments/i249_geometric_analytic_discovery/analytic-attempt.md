# I249: nested ball–tube perimeter and its linearized obstruction

2026-10-12. **Final status: unresolved; no substantial nomination.** The exact quadratic calculation below is a proved auxiliary result, not a theorem about arbitrary finite-perimeter interfaces. Pinned OpenAI results are stipulated true. External results are separately identified. No independent gates have been run by this research sub-agent.

## 1. Exact ambient contract

Let T = R^3/Z^3 with its unit flat metric, Lebesgue volume one, and De Giorgi perimeter P. Pinned family 354, `paper.tex`, Theorem `intro:main`, gives

I(v) = min{(36π)^(1/3) min(v,1-v)^(2/3), 2 sqrt(π min(v,1-v)), 2}.

At v < 4π/81 every minimizer is a translated embedded ball. At 4π/81 < v < 1/π every minimizer is a circular tube about one of the three shortest axial geodesic directions. The endpoints have both adjacent types; they are excluded below. The pin is fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

Fix R in (2/9,1/π). In particular R < 1/3. Set a=4πR^3/3. For ε>0 sufficiently small set r=R-ε>2/9 and b(r)=πr^2. Then a is strictly inside the ball branch and b(r) strictly inside the tube branch. Define

D_R(ε) = inf { P(E)+P(F)-4πR^2-2πr : E,F finite-perimeter subsets of T, |E|=a, |F|=b(r), E⊂F a.e. }.

No connectedness, smoothness, symmetry, topology or graph assumption is imposed on E,F. This is a sum of perimeters, not the usual equal-tension double-bubble area: a contact interface, if present, is counted with the multiplicity implicit in this sum.

The prospective new bridge is a sharp small-ε asymptotic for D_R. It would measure the cost of requiring two individually optimal phases to be nested. This is more specific than a coarea strictness observation.

## 2. Paid elementary geometric obstruction

For every embedded ball B of radius R<1/2 and every axial circular tube C of radius r<R, r<1/2, in T,

|B\C| ≥ δ(R,r) := (4π/3)(R^2-r^2)^(3/2).                         (2.1)

Equality is attained when the ball center lies on the tube axis.

Proof including the periodic issue. Project onto the transverse two-torus. A ball centered at zero has fiber-length density
w(x,y)=2 sqrt((R^2-x^2-y^2)_+),
using representatives x,y in [-1/2,1/2]. This is even and nonincreasing in each coordinate separately. For every fixed y, the indicator of a radius-r disk centered at (h,k) is either zero or a circular interval in x centered at h. The integral of an even decreasing function over a circular interval of fixed length is largest when centered at zero: by layer cake this reduces to the intersection of two circular intervals, bounded by the smaller length, which the concentric intervals attain. Applying this first in x eliminates h; applying the same argument in y eliminates k. Thus transverse alignment maximizes |B∩C|, even when a translated disk meets a fundamental-domain seam. In the aligned case Euclidean cylindrical coordinates give

|B\C| = ∫_r^R 2 sqrt(R^2-ρ^2) 2πρ dρ = (4π/3)(R^2-r^2)^(3/2).

Axial translation has no effect. Coordinate permutation treats all shortest tube directions.

For any nested pair E⊂F with these volumes, and any such B,C, put e=|E△B| and f=|F△C|. Equal volumes imply |B\E|=e/2 and |F\C|=f/2. Since B\C⊂(B\E)∪(F\C) up to null sets,

e+f ≥ 2δ(R,r).                                                   (2.2)

Taking separate infima over ball and tube translations/orientations preserves this inequality. This factor two uses the exact volume constraints.

The direct method plus the stipulated equality classification proves D_R(ε)>0 for every fixed ε in the stated range: existence follows from BV compactness on the compact torus; inclusion and volumes pass to the L1 limit; equality would require a nested minimizing ball and tube, contradicting (2.1). This is a compactness-only corollary and is expressly rejected as a substantial finding.

## 3. Paid explicit nonlinear upper bound

Let q=r/R and suppose R q^(-2)<1/2. Apply A=diag(q,q,q^(-2)), with determinant one, to the Euclidean radius-R ball in an embedded chart; call the resulting ellipsoid E. Let F be the coaxial radius-r tube. The transverse semiaxes of E equal r, so E⊂F. Its axial semiaxis is Rq^(-2), and the stated condition ensures embeddedness. The volumes are exactly a,b(r).

By the linear area formula, with n the unit normal of the sphere,
P(E)=R^2∫_{S^2}|cof(A)n| dσ.
The squared integrand equals q^(-2)(1-n_z^2)+q^4 n_z^2. Cauchy–Schwarz and the spherical average of n_z^2=1/3 give

0 < D_R(ε) ≤ 4πR^2 [ sqrt((2q^(-2)+q^4)/3)-1 ].                 (3.1)

In particular limsup_{ε↓0} D_R(ε)/ε^2 ≤ 8π. This uses an analytic Taylor expansion at q=1, not a numerical experiment. It is an elementary competitor bound, not the sharp asymptotic.

## 4. Exact linearized constrained problem: proved

At ε=0 use the concentric nested pair S_R=∂B_R and Z_R=∂C_R. They are tangent along the equatorial circle Γ. Write θ for its angular coordinate, z for the axial period-one coordinate of Z_R, and t=cos(φ) for latitude on S_R. For u∈H^1(S_R), v∈H^1(Z_R), impose separate zero area means (first-order volume constraints) and the trace inequality

v(θ,0)-u(θ,t=0) ≥ 1 for almost every θ.                         (4.1)

Traces are H^(1/2) traces on the interior smooth circle, not point evaluation of arbitrary two-dimensional H^1 functions. Define

Q_B(u)=∫_{S_R} (|∇u|^2-2R^(-2)u^2)dS,
Q_C(v)=∫_{Z_R} (|∇v|^2-R^(-2)v^2)dS.

The following is a theorem about this explicitly defined Hilbert-space problem:

inf_{(u,v) satisfying (4.1) and the two zero means} (Q_B(u)+Q_C(v))/2
 = K(R) := 4πR/(R+4G_R),
G_R := R^2-(R/2)cot(1/(2R)) > 0.                              (4.2)

No nonlinear conclusion is included in (4.2).

Proof. On mean-zero functions the spherical form is nonnegative: the spherical harmonic eigenvalues are l(l+1)/R^2, l≥1, and l=1 is its translation kernel. On the cylinder, the Fourier eigenvalues are
(m^2-1)/R^2+(2πk)^2, (m,k)∈Z^2\{(0,0)}.
They are nonnegative because R>2/9>1/(2π); the zero modes are m=±1,k=0, namely transverse translations. Averaging both functions under common rotations in θ preserves (4.1) and the means and cannot increase either form. Indeed Fourier decomposition makes the discarded angular blocks nonnegative. Thus it is enough to minimize among axial functions u(t),v(z).

Let A=u(0). The least possible spherical energy with this trace and zero mean is
Q_B(u)/2=4πA^2.                                                   (4.3)
It is attained by u_A(t)=A(1-2|t|). This is an H^1 function, allowed to have a derivative jump along Γ. Its mean is zero. Direct integration gives Q_B(u_A)=8πA^2. To see optimality, subtract u_A from any admissible axial u. The difference h has zero mean and zero trace at the equator. On each hemisphere (-Δ-2/R^2)u_A is constant. Integration by parts gives Q_B(u_A,h)=0: the boundary term contains the zero trace of h, and the interior term its zero total mean. Then Q_B(u)=Q_B(u_A)+Q_B(h)≥Q_B(u_A). An axial l=1 translation can be added without changing energy or trace.

For the cylinder let D=v(0). Set L=-d^2/dz^2-R^(-2) on mean-zero periodic functions. This is positive because 2π>1/R. Its periodic Green function for δ_0-1 is, for |z|≤1/2,

g_R(z)=R^2 - R cos((|z|-1/2)/R)/(2 sin(1/(2R))).

It is continuous, periodic with matching derivative at ±1/2, has derivative jump -1 at zero, and satisfies Lg_R=δ_0-1 distributionally. Integration gives zero mean. Hence g_R(0)=G_R>0 (also follows from positivity of L). For every mean-zero periodic v,

∫(v'g_R'-R^(-2)vg_R) dz=v(0).

Cauchy–Schwarz in the L energy implies ∫(v'^2-R^(-2)v^2) dz≥D^2/G_R, with equality at v=Dg_R/G_R. Multiplying by the circumference gives

Q_C(v)/2 ≥ πR D^2/G_R.                                         (4.4)

After rotation averaging the trace constraint is D-A≥1. Put c_B=4π and c_C=πR/G_R. Minimizing c_B A^2+c_C D^2 under that constraint gives

A_*=-c_C/(c_B+c_C), D_*=c_B/(c_B+c_C),
minimum c_B c_C/(c_B+c_C)=4πR/(R+4G_R).

The displayed u_{A_*},v_{D_*} attain equality. This proves (4.2) without any symmetry assumption on the admissible pair: averaging justified the reduction. Positivity and K(R)<4π are immediate. This calculation is auxiliary and has no contribution review.

## 5. The precise unpaid bridge

The interesting prospective theorem is

lim_{ε↓0} D_R(ε)/ε^2 = K(R), for each fixed R∈(2/9,1/π).       (TARGET; UNPROVED)

Even the lower bound liminf D_R(ε)/ε^2≥K(R) is not established here. No assertion that TARGET is true or novel is made.

A proof must take every finite-perimeter pair with deficit O(ε^2), choose compatible ball/tube centers and tube direction, and derive H^1 displacement compactness at scale ε and the trace inequality (4.1), with liminf of rescaled perimeter at least the corresponding Jacobi energy. Separate translations may not be discarded independently: relative displacement changes the contact circle. At ε=0 nested exact minimizers force the ball center onto the tube axis, but this qualitative fact does not give the needed O(ε) transverse alignment. Transverse shifts can enter the trace obstacle as first angular modes; their treatment is part of the unpaid liminf.

A separate recovery construction is also needed for the exact K(R), because u_A has a crease and a trace inequality only on Γ does not directly ensure nonlinear inclusion near Γ. One would smooth, add an obstacle buffer, solve both exact volume constraints and pass to a diagonal limit. That work is not silently assumed. Formula (3.1) is the only nonlinear quantitative upper bound proved here.

Acerbi–Fusco–Morini gives separate single-interface local L1 squared-deficit estimates modulo translations. It does not directly supply an inclusion-preserving regularization of a nested pair or contact-trace convergence. Their penalized competitors are constructed for one set and need not preserve a second obstacle. Independent application of the two scalar inequalities plus (2.2) yields a lower bound proportional to δ(R,r)^2 if appropriate constants are supplied, but δ^2 is of order ε^3. It misses the proposed ε^2 scale. Uniformity of such constants along the varying tube family is not claimed here from the theorem's stated quantifiers alone.

## 6. Attacks, failed shortcuts and limits

* Set ε=0: D_R(0)=0, so no uniform positive gap independent of ε is possible.
* A mere displacement/L1 estimate sees the missing belt volume of order ε^(3/2); squaring it loses a power. It cannot prove (TARGET).
* Independent centering of the interfaces risks erasing the very obstruction. The common circle and the relative translations must survive normalization.
* At R=1/(2π) the axial cylinder Jacobi mode degenerates. Our interval stays strictly above it. At branch endpoints the full equality class changes; none is included.
* Rotational averaging is legitimate for the quadratic form because the discarded blocks are nonnegative. Averaging characteristic functions does not preserve sets, volume and nesting in the needed nonlinear form. There is no nonlinear symmetrization assertion here.
* Small tentacles, perforations, touching regions, disconnected components and concentration of displacement near Γ are allowed by D_R. Excluding them at the ε^2 scale is part of the unpaid regularization, not a technicality removed by the exact source profile.
* A standard direct-method positive gap, ordinary Sobolev/coarea transfer, or local stability of each separate ball/tube would not count as a substantial discovery.
* The scalar curvature and RCD directions were screened and set aside; no width boundary-completion theorem, quantitative RCD radius, smooth harmonic chart regularity, MTW stability, flow conclusion, or operator theorem is asserted.

## 7. Prior-art comparison and verdict

Pinned family 354 already proves a quantitative nesting improvement for slices of a single CMC minimizer: `nest:bottom-calibration`, `nest:shape-gain`, `nest:area-bound`. Its Δ^3-type integrated slice gain cannot be relabeled as new. Milman, arXiv:2403.06602v3, Proposition 2.5 and Corollary 2.8, already explains how nonnested base minimizers obstruct sharp product-profile transfer. These observations reject the initial broad coarea/nesting direction. AFM 2013, Theorem 1.1/Corollary 1.2 and Theorem 3.9, supplies quantitative local perimeter stability, also not new here.

The remaining prospective bridge is the exact constrained-pair contact asymptotic, not any of those established operations. The linearized capacity in (4.2) identifies a concrete candidate constant and a specific missing nonlinear passage. Bounded searches found no exact match, which is not a novelty certificate. No independent contribution review has occurred.

**Verdict: unresolved, with proved technical auxiliary calculations (2.1)–(4.2); zero nomination and no count change.** The next useful task is the inclusion-preserving second-order liminf for arbitrary near-optimal pairs, not another compactness proof of positivity.
