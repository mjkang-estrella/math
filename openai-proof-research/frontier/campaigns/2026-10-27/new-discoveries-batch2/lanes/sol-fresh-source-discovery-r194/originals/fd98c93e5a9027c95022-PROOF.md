# Ordinary proof candidate: the full planar equality characterization

Status: EXCLUDED, credit 0. The exact full source question already has a public proof by Kenta Kitamura at c646c668c0568b8533bf5534abcf02aab4d2df72. This independently developed ordinary argument is preserved as uncredited work, not a discovery nomination. NOT independently cleared, accepted, formalized, or established new to literature. No manuscript is supplied. See discovery.md for actual-body comparison and chronology.

Target: Fradelizi–Manui–Meyer–Ndiaye, arXiv:2607.03582v1, Conjecture 5, printed p39, with Corollary 29 on p38. For every compact convex K in R² with nonempty interior, a center of symmetry and 0 in K, and every finite real p>1, equality in that corollary implies that K is a parallelogram with vertex 0. Its converse is already source Corollary 29. Write q=p/(p−1) and k_p=2+2 Gamma(1+1/q)^2/Gamma(1+2/q).

The argument uses classical planar mixed area V, normalized by |A+tB|=|A|+2tV(A,B)+t²|B|, its symmetry, bilinearity, monotonicity, and Hausdorff continuity (also for segments). These tools and the source's already-proved sharpness example receive no separate credit.

## 1. A segment-hull estimate, including arbitrary convex bodies

Let C=−C be a planar convex body, c in C, S=[−c,c], A=|C|, M=V(C,S), and C_u=conv(uC,S), 0≤u≤1. We claim

    0≤M≤A,
    |C_u|≤u² A+u(1−u) M.                         (1)

If c=0 these follow immediately, with M=0 and C_u=uC. Otherwise use an invertible linear map to set c=(1,0). Both sides scale by its absolute determinant. Put h=max{y:(x,y) in C}>0. The segment mixed-area formula gives M=2h: adding tS increases every nonempty horizontal chord by 2t, and the vertical projection has length 2h. If b=(x,h) is in C, then D=conv(±c,±b) is contained in C and has area 2h. Thus M≤A. Moreover M=A forces C=D: a proper convex-body inclusion D⊊C has strictly larger area. In particular equality M=A forces c to be a vertex of the parallelogram C.

To prove the second assertion, first take C a symmetric polygon containing ±c. For t≥1 set P_t=conv(C,±tc). Its area is a continuous piecewise affine function of t. Indeed, away from finitely many collinearity values the cyclic list of fixed polygon vertices and the possible moving vertices ±tc is fixed, and the determinant area formula is affine. If (t,0) is a hull vertex, its preceding and following fixed vertices have y coordinates in [−h,h], so differentiating its two adjacent determinant terms gives an area derivative of at most h. The same holds for (−t,0); absent moving vertices contribute zero. The two moving vertices cannot be adjacent along an edge, since C contains points on both sides of y=0. Consequently d|P_t|/dt≤2h=M on every affine interval. Since P_1=C,

    |P_t|≤A+(t−1)M.

For 0<u≤1, C_u=uP_(1/u), proving (1). The u=0 case follows by continuity. For general C, choose symmetric inscribed polygons C^(j) containing ±c and converging to C in Hausdorff distance (convex hulls of symmetric finite nets together with ±c). Their areas, segment mixed areas and all the relevant convex hulls converge. Passing to the limit proves (1) for every C. This approximation is used only for an inequality, not to infer rigidity from polygon rigidity.

For 0≤v≤u≤1 with u>0, convexity gives

    C_v ⊆ (v/u) C_u + (1−v/u) S.

Both vC and S are contained in the right side, which is convex. Also V(C_u,S)=uM, because C_u has exactly u times C's vertical projection. Thus, by (1),

    V(C_u,C_v)
      ≤ (v/u)|C_u|+(1−v/u)V(C_u,S)
      ≤ uv A+(u−uv)M.

By symmetry, including u=v=0,

    V(C_u,C_v) ≤ uv A+(max(u,v)−uv)M.             (2)

Finally C_u⊆C, so V(C,C_u)≤A.

## 2. A positive Minkowski-integral identity for the exact Firey body

For the fixed p>1 define

    F(t)=((1+t)^p+(1−t)^p)^(1/p),  0≤t≤1,
    w(t)=F''(t)
        =4(p−1)(1−t²)^(p−2)
          ((1+t)^p+(1−t)^p)^(1/p−2),  0<t<1.

This derivative follows by twice differentiating. In particular w>0 and is integrable: its only possible singularity at 1 has exponent p−2>−1. Direct endpoint differentiation gives F(1)=2, F'(1−)=1, F'(0)=0. Hence

    ∫_0^1 w(u)du=1,
    ∫_0^1 u w(u)du=F(0)−1,
    F(t)=1+∫_0^1 max(t,u) w(u)du.                (3)

The last identity has derivative ∫_0^t w=F'(t), and agrees at t=0; this also proves it at the endpoints.

For the source body write K=c+C, where C=−C. Since 0 in K, −c in C and hence c in C. For any nonzero dual direction z, put s=h_C(z)>0, a=⟨c,z⟩; then |a|≤s. The literal support function of K⊕_p(−K) is

    ((s+a)^p+(s−a)^p)^(1/p)
      =s F(|a|/s)
      =s+∫_0^1 max(|a|,us)w(u)du.

The integrand is exactly h_(C_u)(z). Therefore, as an equality of compact convex bodies determined by all their supports,

    K⊕_p(−K)= C + ∫_0^1 C_u w(u)du.              (4)

Here the integral is a Minkowski integral. No measurable-selection theorem is needed: u↦C_u is Hausdorff continuous on [0,1], and w(u)du is a finite positive measure, so finite positive weighted sums converge uniformly in support functions. All C_u lie in C, giving a common compact bound. Mixed area continuity and bilinearity, first on the finite sums and then in the limit, give

    |K⊕_p(−K)|= A + 2∫ V(C,C_u)w(u)du
                      +∫∫ V(C_u,C_v)w(u)w(v)dudv.       (5)

## 3. A strict deficit that forces the whole body to be a parallelogram

Define the finite p-dependent constants

    T=∫∫ max(u,v)w(u)w(v)dudv,
    J=∫∫ (max(u,v)−uv)w(u)w(v)dudv.

They are finite because w has mass one; J>0 because w is positive throughout (0,1), and max(u,v)>uv there. Substituting (2) and V(C,C_u)≤A into (5) gives the quantitative estimate

    |K⊕_p(−K)| ≤ (3+T)A − J(A−M).               (6)

To identify 3+T, take the reference diamond D=conv(±e1,±e2), with c=e1. Then D_u=conv(±e1,±u e2). Its area is 2u, V(D,S)=2=|D|, and direct polygon mixed areas give

    V(D,D_u)=2,
    V(D_u,D_v)=2 max(u,v).

For example, when u≥v, D_u+D_v has vertices (2,0),(1,u),(0,u+v),(−1,u),(−2,0),(−1,−u),(0,−u−v),(1,−u), with redundant collinear vertices harmless. Its area is 6u+2v; subtracting |D_u|+|D_v|=2u+2v and dividing by 2 gives 2u. Thus equality holds in the bound (6) for D+c, and (5) gives its ratio exactly 3+T. The reference body D+e1 is a parallelogram with a vertex at 0. Source Corollary 29's already-proved sharpness calculation gives its ratio k_p. Therefore

    3+T=k_p.                                    (7)

Only the known explicit reference example is used here, not the unknown necessity assertion of Conjecture 5. Alternatively (7) can be evaluated through a beta integral; this is unnecessary.

Now suppose the literal equality in Corollary 29 holds for K. Equations (6)–(7), M≤A and J>0 force M=A. The c=0 case is impossible since A>0 but M=0. In the remaining case Section 1 proves C=conv(±c,±b) with b independent of c. Consequently

    K=c+C=conv(0,2c,c+b,c−b).

This is a nondegenerate parallelogram with vertex 0 (take independent edge vectors c+b and c−b). Conversely every such parallelogram attains equality by source Corollary 29. This treats every admissible convex body, every allowed position of the origin, and every finite p>1. No smoothness, polygonality, strict convexity, or uniform bound away from p=1 is assumed.

## Review limits and decisive falsifiers

No ordinary mathematical bridge is intentionally left as an assumption. The most delicate independently unchecked steps are the piecewise-affine hull-area derivative estimate in Section 1, the exact positive representation (4), and its quadratic mixed-area expansion (5). A legal symmetric polygon with |conv(uC,±c)|>u²|C|+u(1−u)V(C,S), or a direction violating (3)–(4), would falsify the argument immediately. A pre-existing theorem giving this same all-p rigidity, or a generic hull-integral rigidity theorem with the exact positive-measure hypotheses, would defeat substantive novelty even if this proof is correct. No independent clearance or complete current-registry clearance has been obtained.
