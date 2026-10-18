# T143D45 continuation: existence of weighted fits, unresolved uniqueness and sign

The frozen full global two-cycle problem is unchanged and unresolved. The assertions proved here are supporting deductions, not a nominated result. They have not undergone independent proof or contribution review. Original prose CC BY 4.0.

## Setup and exact dependencies

Fix a>0, β≥0, and the base-zero weighted reference

(a+2βu)u_y=λu+κu²/2−y, u≥0.

Write H(a,λ,κ,r) for its midpoint at width r>0, P=Hλ, Q=Hκ, R=P_r, S=Q_r and G=PS−QR. The r46 proof retained in private/context/r46-weighted-model.md proves global smooth existence, |H|<r, |H_r|<1, P,Q>0, and the unique smooth midpoint fit λ=λ*(a,β,r,M,κ) for every |M|<r. No global sign for G is assumed. Its proof uses the pinned source's general arc and positive-variation lemmas, not the unproved weighted second-jet inverse.

Put v=au+βu², U(v)=u, w=a+2βu, and ψ(v)=λU(v)+κU(v)²/2. Then v_y=ψ(v)−y and

ψ''(v)=b/(a²+4βv)^(3/2), b=aκ−2βλ.

Every relevant arch has 0≤v≤r²/2. In particular all the curvature comparisons below concern a fixed compact energy interval, with a smooth extension through the regular base v=0. No entire weighted profile below its singular boundary is required.

The source comparison used is fitting.tex, Lemma lem:curvature-comparison: an actual smooth profile whose curvature is bounded below by a constant k has final angle L=atanh H_r at least the angle of the ordinary quadratic reference of curvature k fitted to the same r,M. Inequalities reverse for an upper curvature bound. The source's fit:conditional-derivative gives a strictly positive derivative for that ordinary conditional angle, and fit:properness gives its limits ±∞ as k→±∞. Denote this ordinary conditional angle by L0(r,M,k). This is the source's quadratic energy family, not the weighted family.

## Route 1: fixed-endpoint one-crossing variation

Fix a,β,r,M and vary κ, always adjusting λ=λ*(κ). At a selected parameter let d=Q/P>0, so λ*κ=−d. The profile variation at fixed energy is

f(v)=U(v)²/2−d U(v),
f'(v)=(u−d)/w,
f''(v)=(a+2βd)/w³>0.

Let A=M−r<0<B=M+r, and K(y)=exp(−∫_A^y ψ'(v(s)) ds). The positive fixed-width variation formula gives

d=[∫_A^B K u² dy]/[2∫_A^B K u dy].

Thus c=2d is a strict weighted mean of u with positive density K u on the interior: 0<c<u_peak. The arc is strictly increasing then strictly decreasing in height. Indeed at each critical point v_y=0 one has v_yy=−1, so its sole critical point is a strict maximum. Consequently f(v(y)) is negative, then positive, then negative on three successive open intervals of (A,B).

The arc variation z(y)=∂κ v(y) with its endpoints held fixed satisfies

z'=ψ'(v)z+f(v), z(A)=z(B)=0,
K(y)z(y)=∫_A^y K(s)f(v(s)) ds.

Its cumulative integral is negative at the end of the first interval and positive at the beginning of the last (the full integral is zero and the last contribution is negative). It increases strictly in the central interval and decreases to zero in the last. Hence z has exactly one interior zero, with z<0 before and z>0 after. This is a complete one-crossing statement for every weighted model parameter, not a numerical observation.

It does not yet prove the required slope sign. Differentiating a fixed-profile arch by width gives the homogeneous variation v_r'=ψ'(v)v_r, and its endpoint values are A(H_r−1), B(H_r+1). Both are positive. Therefore

2 atanh H_r=log(−A/B)+∫_A^B ψ'(v(y)) dy.

At fixed r,M the endpoints are fixed, and ordinary smooth differentiation yields the exact conditional derivative

2∂κ Lhat = ∫_A^B [(u−d)/w + b z/w³] dy,
Lhat(κ)=atanh H_r(a,λ*(κ),κ,r).

The second term contains a sign-changing z; the weighted centering that fixes d uses K u, not the weight 1/w in the first term. Neither the one-crossing statement nor f''>0 alone has supplied the sign of this sum at nonzero b. No counterexample to that sign is claimed. This route stops at an explicit unpaid integral, rather than replacing it with an assumption that the arc crossing orders endpoint derivatives.

## Route 2: constant-curvature barriers

Along the same midpoint fit,

b'(κ)=a+2βQ/P≥a>0.

Thus b is a strictly increasing smooth bijection of R onto R. The unique b=0 member is the linear-energy reference ψ(v)=ℓv, where ℓ is uniquely chosen for the prescribed r,M: λ=aℓ and κ=2βℓ. This also covers β=0, where κ=0. Let D=(a²+2βr²)^(3/2)>0.

For b>0 the full arch has ψ''≥b/D. For b<0 it has ψ''≤b/D. Direct application of the actual source comparison therefore gives

Lhat(κ)≥L0(r,M,b(κ)/D) when b(κ)>0,
Lhat(κ)≤L0(r,M,b(κ)/D) when b(κ)<0.

In particular Lhat is above the linear-energy conditional angle when b>0 and below it when b<0. The inequalities are strict by the source strict comparison with curvature zero. At b=0 there is equality with L0(r,M,0).

Since b(κ)→±∞ and the source's ordinary conditional angle has limits ±∞, these barriers prove

lim_{κ→+∞} Lhat(κ)=+∞,
lim_{κ→−∞} Lhat(κ)=−∞.

Continuity and the intermediate value theorem now prove the following full-range supporting statement:

For every a>0, β≥0, r>0, |M|<r and |q|<1 there is at least one finite real pair (λ,κ) with H=M and H_r=q.

This is existence for the entire weighted second-jet data domain, with no small-parameter or amplitude restriction. For fixed r,M,q the set of curvature solutions is nonempty and compact: the displayed limits bound it, and it is closed by continuity. We claim neither uniqueness, regularity of a chosen inverse, nor uniform compactness as r,M,q vary. The argument is a direct quantitative curvature bound followed by the source comparison and range theorem; it is technical support and does not qualify independently as substantial research.

The same argument gives G>0 along the whole linear-energy locus b=0, extending the r46 zero-parameter anchor but still not proving global G. At such a point let m=b'(κ0)=a+2βd>0. For sufficiently small ε>0,

b(κ0+ε)≥mε/2,
Lhat(κ0+ε)≥L0(r,M,mε/(2D)).

Subtract Lhat(κ0)=L0(r,M,0), divide by ε, and use smoothness and the source's strictly positive ordinary derivative. It follows that

Lhat'(κ0)≥[m/(2D)] ∂k L0(r,M,0)>0,
G=P(1−H_r²)Lhat'(κ0)>0.

This derivative argument supplies a positive first-order bound; it does not incorrectly infer a strictly positive derivative from strict monotonicity alone.

## Why the two routes do not finish T143D45

The source compares an actual profile with constant-curvature reference characteristics. At two different nonzero values of b, both weighted profiles have nonconstant energy curvature b/(a²+4βv)^(3/2). Their characteristic heights differ. Pointwise curvature ordering at a common energy coordinate does not, without a new theorem, compare these two evolving reference characteristics by the source's scalar error equation. That equation uses the special ordinary quadratic reference slope field. Replacing it with the weighted field assumes the missing inverse/comparison structure.

The proven limits, barrier relative to b=0, and derivative sign at b=0 do not logically imply global monotonicity. As an abstract diagnostic only, t+2 sin t has limits ±∞, has the sign of t, and has positive derivative at zero, but derivative −1 at π. This is not a weighted-model example; it identifies the insufficiency of those qualitative conclusions for uniqueness.

The r46 identity remains the exact unpaid model-sign route. With α=r/(r²−H²), γ=(r²+H²+2rHH_r)/(r²−H²)², W=RS_r−SR_r, and Dchar=2β∂a+κ∂λ−aα∂r,

Dchar W=a(2γ+3α_r)W+aγ_r G_r−aγ_rr G.

Where G≠0, (R/G)_r=−PW/G². At W=0 and R≠0, writing σ=R_r/R gives Dchar W=−aG(γ_rr−σγ_r). Global G,R positivity and the sign γ_rr−σγ_r>0 at these zeros remain unpaid. Surjective fitting does not authorize differentiating a chosen inverse through possible folds, and cannot replace the source's smooth global fitting coordinates in its shape transport proof.

The full nonlinear-restoring-force cycle-count upper bound remains unproved and unrefuted. No restricted substitute has been frozen, nominated, or counted. A next continuation on this lane needs a mechanism proving the nonzero-b integral sign or controlling the weighted reference characteristic field, followed by the separate W estimate and actual-profile comparison. Merely repeating the curvature barriers will not pay those steps.
