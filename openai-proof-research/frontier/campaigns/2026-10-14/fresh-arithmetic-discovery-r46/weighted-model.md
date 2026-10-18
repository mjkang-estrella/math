# Weighted reference model: proved supporting statements, unresolved global fit

The full T143D45 problem remains frozen and unresolved. This report advances one exact interface from r45; it does not replace the full target with a local, symmetric or small-damping theorem. No substantial nomination is made. All partial conclusions below are independently derived author-side and have not received independent proof review.

Fix a>0 and β≥0. Consider positive arches of

(a+2βu)u_y=λu+κu²/2−y,

with base u=0. Let H(a,λ,κ,r) be the midpoint of the two endpoints of its unique arch of half-width r>0. Partial derivatives below hold a,β fixed. Write P=Hλ,Q=Hκ,R=P_r,S=Q_r,G=PS−QR, and W=RS_r−SR_r.

## 1. The model exists globally and the midpoint alone can be fitted

Put v=au+βu² and let u=U(v) be its inverse on [0,∞). It is smooth near every nonnegative v because a>0. The equation becomes

v_y=ψ(v)−y, ψ(v)=λU(v)+κU(v)²/2.

The source's general arc construction (arcs.tex, lem:arc-data and its proof) applies to each compact interval from base0 to a positive peak. The profile extends smoothly slightly below0, so base0 is a regular base, not the singular square-root boundary of the original physical Liénard problem. Its proof gives two finite transverse endpoints and strictly increasing width as the peak increases. It gives r²≥2v_peak. Width tends to0 as the peak tends to0 and to∞ as the peak tends to∞. Thus H is defined and smooth for every real λ,κ and r>0, with |H|<r and |H_r|<1.

The actual fixed-height/width variation formula, arcs.tex lem:variation, applies on a neighborhood of these compact arches. Its positive kernel and positive denominator show P>0,Q>0: the two profile variations U(v), U(v)²/2 vanish at the base and are strictly positive inside the arc. This does not prove R,S,G positive.

For fixed a,β,r,κ, the function λ↦H is a smooth increasing bijection onto (−r,r). Here is a direct range argument that avoids the source's unavailable entire peak-reference family. Let Umax=U(r²/2). Every relevant peak is at most r²/2 in v-coordinates. On this compact interval,

v/(a+βUmax)≤U(v)≤v/a.

For λ>|κ|Umax/2, one has ψ(v)≥L v with L=(λ−|κ|Umax/2)/(a+βUmax). Compare these profiles by linear interpolation. All intermediate fixed-width peaks also lie below r²/2, so the compact-arc variation formula proves H(ψ)≥H(Lv), even though the comparison need not hold outside this interval.

For L>0, the endpoints A<B of v_y=Lv−y, v(A)=v(B)=0, satisfy A<0<B, B−A=2r and

(A+1/L)e^(−LA)=(B+1/L)e^(−LB)>0.

Hence −1/L<A<0, so r−1/L<H(Lv)<r. Therefore H→r as λ→∞. Reflection (λ,κ,y)↦(−λ,−κ,−y), or the reversed compact comparison, proves H→−r as λ→−∞ with κ fixed. The implicit function theorem supplies a unique smooth midpoint-fit slope λ*(a,β,r,M,κ), for |M|<r. Differentiating gives λ*κ=−Q/P.

This only fits M. The second-jet derivative ∂κ H_r along this fit is G/P. Its global positivity and its complete range (−1,1) remain unproved.

## 2. Complete all-width determinant and derivative estimates at λ=κ=0

At the zero profile the energy arch is exactly

au+βu²=(r²−y²)/2, −r≤y≤r.

Use t=y/r, and write u=u(r,t). Let E denote uniform probability averaging over −1≤t≤1. First variation at the zero profile gives

P=E u, Q=(1/2)E u², R=E u_r, S=E(uu_r).

These identities and their derivatives are justified by the smooth inverse U: at t=±1, u and u_r vanish smoothly, and on compact r-intervals all integrands and their needed derivatives are bounded. No numerical quadrature enters this argument.

At interior points u>0,

u_r=2u(a+βu)/[r(a+2βu)],

and therefore u/r<u_r≤2u/r. The upper equality holds when β=0; the lower inequality is strict because a>0. Integrating yields

R≤2P/r, S>2Q/r, hence G=PS−QR>0.

Also R>0. Define T=S/R and use the probability measure having density u_r/R relative to E. Then T is its mean of u. Its logarithmic density derivative before normalization is

L=∂r log u_r=a²/[r(a²+2βr²(1−t²))], 0<L≤1/r.

The endpoint values are understood by continuous extension and do not affect the integral. Differentiating the weighted mean gives

T'=E_weight u_r+E_weight(uL)−T E_weight L.

Since u_r>u/r, L≥0 and E_weight L≤1/r, we have T'>0. More quantitatively, if Amax=√(a²+2βr²), then u_r−u/r=a u/[r(a+2βu)]≥a u/(r Amax), so T'≥aT/(r Amax)>0.

Now R/G=1/(PT−Q). Because P'=R and Q'=S=RT,

(PT−Q)'=P T'>0,

and consequently

(R/G)_r=−P T'/(PT−Q)²<0.

This proves both G>0 and the strict desired model inequality at λ=κ=0, simultaneously for every a>0, β≥0 and r>0. It does not extend them to nonzero model parameters. The proof is an elementary weighted-mean estimate following the source's general first-variation interface; it is supporting progress, not a substantial replacement theorem.

For a=β=1 a closed-form control is available. With z=√2r,

P=[(z+z^−1) arctan z−1]/4, Q=(r²/3−P)/2.

Ordinary differentiation determines R,S,G and (R/G)_r. At r=8 the latter is approximately −0.03231014846. This decimal is an illustration of an exact analytic formula, not the proof of its sign.

## 3. Exact transport beyond the anchor

Let α=r/(r²−H²), γ=(r²+H²+2rHH_r)/(r²−H²)². Translation of the base changes a at rate2β, slope at rateκ, and leavesκ unchanged. Therefore

D=2β∂a+κ∂λ−aα∂r,

DH=aH/(r²−H²)−λ.

Differentiating while accounting for parameter derivatives of D gives

DP=aγP−1, DQ=aγQ−P,
DR=a(γ+α_r)R+aγ_rP,
DS=a(γ+α_r)S+aγ_rQ−R.

The commutator is D(f_r)=(Df)_r+aα_r f_r. Two differentiations and cancellation give the exact identity

DW=a(2γ+3α_r)W+aγ_r G_r−aγ_rr G.

Also (R/G)_r=−PW/G² wherever G≠0. These are identities of the globally defined H; no global-fit inverse is assumed to obtain them. The same source's cancellation algebra applies because a is independent of r, while its transport derivative is retained in D. Omitting 2β∂a would be incorrect.

At a point where W=0 and R≠0, put σ=R_r/R. Then G_r=σG and

DW=−aG(γ_rr−σγ_r).

Thus, even assuming the unproved global inequalities G>0,R>0, excluding a first zero of W still requires the sign γ_rr−σγ_r>0 there. The zero-profile result does not establish this sign for nonzero λ,κ. A characteristic of a nonzero weighted reference does not generally pass through λ=κ=0. Its initial positive small-width data cannot by itself prohibit a later zero. This is the exact remaining sign mechanism in the attempted transport proof.

There is another potentially useful invariant, but no comparison theorem is inferred from it. For a general profile k=φ'(h), c=φ''(h), a=1+2βh, set b=ac−2βk. Then b_h=aφ'''(h). For a quadratic reference b=aκ−2βλ is constant under base translation. With j=k/a and outward characteristic width s,

a'=−2βs sech²θ/a, j'=−s sech²θ b/a³,
θ'=j−sinh(2θ)/s, L'=sinh(2θ)/s.

The extra state a couples to the angle. The source's reference comparison does not become a scalar comparison merely because b is constant. No sign for the derivative of the new reference labels with respect to peak slope has been proved.

## 4. The model is not a new dynamical class

For β>0 set X=u+a/(2β), and shift the endpoint coordinate by the constant q(−a/(2β)), where q(u)=λu+κu²/2. The associated physical system u_dot=y−q(u), y_dot=−(a+2βu) becomes a classical Liénard system with linear restoring force2βX and quadratic primitive

q_shift(X)=κX²/2+(λ−κa/(2β))X.

The relevant section is X=a/(2β)>0. After ordinary time and endpoint scaling, its energy profiles lie in span{V,√V}, at a positive base, rather than the source reference span{V,V²}. This equivalence is an elementary change of variables, not a new construction. The source's theorems on cycle counts of quadratic primitives do not state the global two-parameter interpolation or the above derivative estimate at an arbitrary positive section.

The r45 finite-boundary observation remains correct for a reference started at peak u=0 and extended to negative u: the weight vanishes at −a/(2β). It does not obstruct the global base-zero arches proved in Section1 here. This distinction repairs a proof-method limitation, not the full missing fit theorem.

## 5. Numerical control and disposition

The coarse12-case sweep produced four apparent positive estimates of C_r, including the anchor λ=κ=0,r=8. The exact result in Section2 rules that one out. The refined script uses RK4 endpoint-root bisection,43 peak-bisection steps, successively smaller integration steps and parameter differences. All three tested positive-sign cases then gave negative estimates, including the anchor. Both scripts and both logs are retained. In the logs G is evaluated at r−dr, the lower width used in the central C difference, not at the displayed center r. No rigorous numerical error enclosure is claimed. Untested coarse signs are not counterexamples; all coarse positive locations are covered up to reflection by the three refinements.

The global H, midpoint-fit range, and zero-profile inequalities are proved above. Global G>0/R>0, complete second-jet range, the sign-at-zero inequality, and the ensuing nonlinear profile comparison remain unpaid. The full T143D45 upper bound remains unresolved and unchanged. Nothing in this packet is nominated as a substantial new result or counted toward the campaign target.
