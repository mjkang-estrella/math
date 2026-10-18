# T143D45: full target unresolved after three proof routes

No nomination and no contribution count. frozen-scope.md is unchanged. The companion's finite B(5) bound applies, and the lower bound two is easy, but the global upper bound two is not proved. Neither a local cyclicity statement nor a small-damping replacement is submitted.

## Exact coordinate interface and lower bound

Write Gβ(x)=x²/2+βx⁴/4. This is strictly increasing from zero on x>0, with derivative gβ(x)=x(1+βx²). On either open half-plane, energy height u=Gβ(x) gives exactly

u_y=F(x)−y=φ±(u)−y.

Indeed du/dy=gβ(x)(y−F(x))/(−gβ(x)). Let zβ(u)>0 be the inverse of Gβ on x>0. Then φ±(u)=F(±zβ(u)). The half-plane coordinate map is smooth and invertible at every positive height. No division by gβ is made on the axis. Global physical coordinates X=sgn(x)√(2Gβ(x)), Y=y are smooth and invertible even there, and the positive time change ds/dt=gβ(x)/X, extended by1 at x=0, converts the system to X_s=Y−F(x(X)), Y_s=−X. On every compact periodic orbit this time change is bounded above and away from zero. It therefore preserves periodic-orbit images and their isolation. Its transformed primitive need not be polynomial.

For β>0 the additional linear rescaling X=√β x, Y=√β y normalizes β to1 and transforms F to √β F(X/√β), still an arbitrary polynomial of degree≤5. Thus β>0 is one equivalent full family, not a small-parameter restriction. Small β does not make the perturbation uniformly small over unrestricted amplitudes and coefficients.

The lower bound two for each β is already paid by elementary hyperbolic persistence. The source sharpness proof constructs a fixed quintic F0 for β=0 with two simple hyperbolic cycles. Smooth dependence of the two transverse return maps and the implicit function theorem preserve these cycles when the restoring force is changed to X+δX³ for every sufficiently small δ>0. Fix one such δ. Given β>0, put a=√(δ/β), x=aX,y=aY, and F(x)=aF0(x/a). This gives exactly restoring force x+βx³, degree≤5 and two distinct hyperbolic cycles. β=0 is the source. This proves only the lower-bound clause, not the proposed upper bound or exact maximum. It is not nominated separately.

## Route A: source's energy-profile sign partition

The source's application has φ±(u)=d0u+b0u²±p(u), p=e√u+cu^(3/2)+au^(5/2). Its four coefficient cases use constant common curvature, opposite third-derivative signs, curvature separation, or a fixed slope-intercept comparison. The general profile comparisons are actual propositions in transport.tex, not conjectured black boxes.

For β>0 the common even part becomes f2 zβ(u)²+f4 zβ(u)⁴. It is not generally quadratic in u. This is not a harmless change of coefficients. Normalize β=1 and set x=z1(u), so d/du=[x(1+x²)]^−1 d/dx. For the common term E(u)=x², direct differentiation gives

E'=2/(1+x²), E''=−4/(1+x²)³, E'''=24/(1+x²)^5>0.

Thus arbitrary even coefficients contribute nonzero third derivatives to both profiles. The source's cancellation of that contribution is lost.

Even with no even coefficients, the old coefficient cases do not preserve their signs. For p(u)=x⁵−x³ (the source's e=0,c<0,a>0 case),

p'''(u)=[3+39x²−75x⁴−15x⁶]/[x³(1+x²)^5].

It is positive near zero and equals −3/2 at x=1. For x⁵ alone the third derivative is 15(1−4x²−x⁴)/[x(1+x²)^5], also sign-changing. This agrees with the large-u growth x⁵∼(4u)^(5/4), whose third derivative is negative. The source's Proposition third-derivative consequently cannot be invoked with its old global sign. These examples refute the attempted interface, not the two-cycle question.

A replacement comparison might subtract a nonquadratic common part or retain a weighted reference model. No proof that fitted curvature differences remain monotone under that replacement has been obtained.

## Route B: Hamiltonian energy averaging

For F=εP, the equivalent scalar equation is x''+εP'(x)x'+gβ(x)=0. Let f=P'. At ε=0, E=(x')²/2+Gβ(x) is conserved. Every positive energy is a periodic oval. On a compact energy interval away from zero, the first return displacement has its first-order term proportional to

I(h)=∮ f(x)z dx=4√2∫_0^{a(h)} f_even(x)√(h−Gβ(x)) dx,

where z=x', a(h)>0 solves Gβ(a)=h, and f_even(x)=A+Bx²+Cx⁴. The odd damping part integrates to zero. Put t=x², v=t/2+βt²/4, and let t=t(v). Then exactly

I(h)=4√2∫_0^h [A+Bt(v)+Ct(v)²]/[√t(v)(1+βt(v))] · √(h−v) dv.

A tempting route was to use the at-most-two sign changes of the quadratic numerator and a third-order total-positive integration kernel. The kernel K(h,v)=√max(h−v,0) does not have that property. At rows h=2,3,4 and columns v=0,1,2 its determinant is

2(1+√2−√6)<0,

because (1+√2)²=3+2√2<6. By continuity one can move the last column slightly below2 and still obtain a negative minor with every entry positive. Thus a generic order-three total-positivity assertion is false. This does not show that this particular three-dimensional Abelian-integral family fails a Chebyshev property; a dedicated Picard–Fuchs or Wronskian argument could still prove it.

Even a complete bound on I would not prove the frozen global claim: the displacement expansion is local in ε and on a fixed compact annulus. It provides no uniform control of cycles at amplitudes escaping to infinity, at the center as ε varies, or for arbitrary non-small coefficients. The actual primary comparison Sun–Yu2020 expressly distinguishes first-order annulus cyclicity from global cycle counts. We did not treat its different quintic restoring system as a result about this target. No unproved continuation principle from ε=0 to ε=1 is used.

## Route C: preserve polynomial profiles with a weighted quadratic model

Instead put u=x²/2. Then the exact half-arc equation is

(1+2βu)u_y=φ±(u)−y,

and the original polynomial decomposition φ±=d0u+b0u²±p(u) returns. At base h the shifted weight is a+2βz with a=1+2βh>0. The appropriate reference family would therefore be

(a+2βz)z_y=λz+κz²/2−y, z≥0.

This is a concrete new reference model, not supplied by the source's Riccati calculation. Write H(a,λ,κ,r) for its base-zero midpoint, where defined, and P=Hλ,Q=Hκ,R=P_r,S=Q_r,G=PS−QR. A global fit would require G>0, the complete range |H|<r, |H_r|<1, and the reference comparison properties used in the source.

There is some exact algebraic progress. With α=r/(r²−M²), endpoint differentiation for the weighted arc gives

dr/dh=−aα, dM/dh=aM/(r²−M²)−φ'(h).

For a quadratic reference, base translation has a_h=2β, λ_h=κ, κ_h=0. Its model transport operator is therefore

D_model=2β∂a+κ∂λ−aα∂r.

The corresponding actual operator is D=∂h−aα∂r. If the weighted two-jet fit exists with G≠0, differentiating the matching equations and subtracting model from actual cancels the added 2βH_a and 2β(H_r)_a terms. The source's linear system survives formally:

P(Dλ−κ)+Q Dκ=λ−φ'(h), R(Dλ−κ)+S Dκ=0,

and hence Dκ=−(R/G)(λ−φ'(h)), Dλ−κ=(S/G)(λ−φ'(h)). This is conditional transport algebra, not an existence or sign theorem for the fit.

The source's proof of global reference labels cannot simply be copied. It moves the base arbitrarily far below a fixed peak in an entire quadratic profile. In the weighted model a+2βz changes sign at z=−a/(2β). Already λ=κ=0 with peak z=0,y=0 gives az+βz²=−y²/2; the weight-zero barrier is reached at finite half-width a/√(2β). Thus that particular entire-profile reference construction is unavailable. This does not disprove a base-zero weighted fit built from positive peaks, but such a fit needs a new proof with appropriate changing peak weights. Its curvature comparison and fixed-parameter derivative (R/G)_r also remain unpaid.

explore_model.py independently integrated six β=1,a=1 weighted reference examples. Its approximate G values were positive and central-difference estimates of (R/G)_r negative. This is only a small floating feasibility experiment, with no rigorous error enclosure, no derivative certification, and no claim of parameter exhaustion. The script's RK4/linear crossing interpolation and finite peak bisection cannot validate an inequality. Its samples therefore leave the weighted-model direction open; they do not justify a theorem.

## Honest stopping point

Three full-proof routes have been attempted. The first loses an exact hypothesis; the second has an explicit false kernel assertion and remains perturbative; the third isolates a new weighted global interpolation/comparison problem and derives its conditional transport algebra, but does not solve that problem. The full frozen upper bound remains unresolved. The lower-bound persistence observation is technical and not substituted for the full result. No source audit, counterexample to the frozen target, independent proof pass, or literature novelty verdict is claimed.
