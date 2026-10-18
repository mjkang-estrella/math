# R94 quantitative radial geometry: exploration, not a candidate

Status: no frozen theorem target and no nomination. Full prospective question is a dimension-free explicit radial modulus for every onto ε-isometry between the unit spheres of arbitrary nonzero real Banach spaces. The unspecified modulus is already paid by I12 and source322. No continuity, injectivity, smoothness, reflexivity, or finite-dimensional restriction may silently replace this scope. A universal power-law modulus would be a natural strengthening, but no exponent or constant has been proved here.

## Exact source boundary

The entire canonical main.tex and references.tex have now been read (main ranges 1–180, 181–229, 230–500, 501–end). Source322 gives exact onto sphere isometries, maximal radial defect attainment, common-face propagation, a Darbo return-map fixed point, and the final chord contradiction. It does not give a quantitative ε-isometry theorem. The complete canonical family has three non-PDF blobs; identity receipts are separate. This is use of stipulated source truth, not source review.

## A one-step error calculation

Let f:S_X→S_Y be onto with distance error at most ε. Put
M=sup{| ||f(x)−t f(y)||−||x−ty|| |:x,y∈S_X,0≤t≤1}.
Fix 0<t<1, y∈S_X, b=f(y), and write a=1−t, U=1+t. For a direction v∈S_X, let x=ty+pv be its positive ray contact, so a≤p≤U. Write f(x)=tb+sw, and choose the opposite contact tb−uw∈S_Y and any preimage z. Set r=||ty−z|| and g=(ty−z)/r. All four radii lie in [a,U]. No continuity of this selected return map is claimed.

Assume s−p≥M−δ. The radial defect bound gives r−u≤M, while the sphere distance error gives
s+u−ε≤||x−z||=||pv+rg||≤p+r.
Therefore
M−δ−ε≤r−u≤M,
0≤p+r−||pv+rg||≤δ+ε.
Choose a norm-one supporting functional φ for pv+rg. (If the vector is zero, the same following inequality follows from any norm-one functional; the nontrivial small-error situation excludes this.) Then
p(1−φ(v))+r(1−φ(g))≤δ+ε.
Both summands are nonnegative, so each individual support loss is at most (δ+ε)/a.

For any l∈S_X with φ(l)≥1−η, let x_l=ty+p_l l and s_l=||f(x_l)−tb||. Since r(1−φ(g))≤δ+ε,
||x_l−z||≥p_l(1−η)+r−δ−ε.
On the other hand this norm is at most ||f(x_l)−f(z)||+ε≤s_l+u+ε. Hence
s_l−p_l≥r−u−p_lη−δ−2ε≥M−2δ−3ε−Uη.
This is a proved estimate, not the full desired rate.

## The missing convex core

In the exact source, a positive convex combination A=Σ λ_i v_i has norm one. A supporting functional at A taking value one must take value one on EVERY v_i. With error τ, the only general deduction is
Σ λ_i(1−φ(v_i))≤τ, hence 1−φ(v_i)≤τ/λ_i.
This division is sharp already in ℓ∞²: take φ(x,y)=x, v_1=(−1,1), v_2=(1,1), λ_1=τ/2, λ_2=1−τ/2. Their combination has norm one and φ(A)=1−τ, but φ(v_1)=−1. Thus no coefficient-independent transfer follows from an approximate support value. This is an obstruction to that proof step, NOT a counterexample to a universal radial rate.

Choosing equal weights avoids very small coefficients only for a bounded number N of vertices, and loses a factor N. Source Darbo does not supply a dimension-independent bound on the number of vertices or covers. Replacing dense combinations by a fixed finite mesh therefore leaves a separate quantitative dimension/entropy obligation.

A fixed initial support functional also does not stay preserved merely because consecutive vectors have a common support: in ℓ∞², v=(1,1), g=(−1,1) share the support y-coordinate, although the x-coordinate support of v takes −1 on g. Thus selecting one support at the start does not repair the issue.

The source return-map estimate uses an exact invariant closed convex subset of the sphere. In the approximate setting both the existence of a suitable convex set and continuity of the selected return map remain unpaid. A quantitative noncompactness fixed-point lemma alone cannot supply these assumptions.

## A paid comparison in Hilbert spaces

For unit vectors in real Hilbert spaces, put d=||x−y|| and d′=||f(x)−f(y)||. At every 0≤t≤1 the radial distances equal h_t(d) and h_t(d′), where h_t(s)=sqrt((1−t)^2+t s^2). Its derivative is bounded by sqrt(t)≤1 (the t=1 endpoint is h_1(s)=s). Thus the original sphere error immediately yields radial error≤ε, with no dimension dependence. No source322 input is used. This elementary Hilbert calculation is not a candidate and does not settle arbitrary Banach spaces.

## Current limits

No uniform power-law exponent, linear rate, optimality result, continuous approximate invariant core, or full quantitative chord-alignment theorem has been obtained. No replacement by Hilbert spaces, Lindenstrauss spaces, finite dimensions, a prescribed polytope, or a known unspecified modulus is proposed for acceptance.

## Further attempt: quantitative Darbo itself is not the central obstruction

Suppose C is a nonempty closed bounded convex subset of a Banach space, g:C→C is continuous, and χ(gH)≤γχ(H)+b for every H⊂C, where 0≤γ<1. Then inf_{x∈C}||x−g(x)||≤b/(1−γ). Indeed put C_0=C and C_{n+1}=closedconv(g(C_n)). The sets are nested and invariant, and χ(C_n)≤γ^nχ(C)+b/(1−γ). Given a positive tolerance τ, choose n so that χ(g(C_n))<b/(1−γ)+τ. Cover g(C_n) by finitely many sets of diameter less than this bound and choose a representative P_i in each nonempty set. For radius R>b/(1−γ)+τ, the usual positive distance-to-P_i weights give a continuous map P from g(C_n) into conv{P_i}, with ||P(z)−z||<R. The finite convex polytope conv{P_i} lies in C_n; P∘g maps it continuously to itself. The finite-dimensional fixed-point theorem gives x=P(gx), hence ||x−gx||<R. Let τ and the excess in R decrease to zero. No compact intersection claim is needed. This is a routine approximate version of the source appendix, not a candidate.

For the near-maximal return map above, assume M>δ+ε. For two directions v,v′ with defect at least M−δ, marking all radii by primes gives
r||g(v)−g(v′)||≤|r−r′|+|u−u′|+u||w−w′||+ε,
s||w−w′||≤|s−s′|+|p−p′|+p||v−v′||+ε.
The product up/(rs) is at most γ=(1−(M−δ−ε)/U)^2<1. Partition ALL FOUR radius coordinates into intervals of arbitrarily short length; their error terms disappear in the definition of χ. Since u/r<1, the remaining additive error ε/r+uε/(rs) is at most 2ε/a. Thus for any subset H of these near-maximal directions,
χ(g(H))≤γχ(H)+2ε/a.
If there were a suitable invariant convex C contained in these directions and the return map were continuous, the preceding lemma would yield displacement at most 2ε/[a(1−γ)]. This is an explicit conditional alignment estimate. No such C is constructed. The small-coefficient obstruction above is exactly at that missing input, not at the Darbo estimate. Moreover the final chord contradiction still needs a uniform error budget; its exact strict support inequalities cannot simply be asserted quantitative.

## Continuation: continuity removed, conditional on the same convex core

Parent author assistance suggested the following smoothing route and supplied the same explicit coarse constants derived in this lane. This is collaborative author work, not independent review. It resolves the continuity condition in the preceding conditional result, not the full target.

For c=ty, the translated unit ball K=B_X−c contains aB_X and lies in UB_X. Its gauge q is positively homogeneous and subadditive, although K need not be symmetric. Consequently q(z)−q(z′)≤q(z−z′)≤||z−z′||/a, and exchanging z,z′ proves |q(z)−q(z′)|≤||z−z′||/a. For unit v, q(v)≥1/U. Hence the positive contact radius ρ(v)=1/q(v) satisfies |ρ(v)−ρ(v′)|≤U²||v−v′||/a. The contact map R_c(v)=c+ρ(v)v is therefore R-Lipschitz for R=U+U²/a=2U/a. Normalization N_c(z)=(z−c)/||z−c|| on the unit sphere is 2/a-Lipschitz, by adding/subtracting the normalized first vector and using the reverse triangle inequality. The same constants apply in Y about tb.

Choose a right inverse σ:S_Y→S_X of f. It need not be continuous or injective, but the ε-isometry inequality gives ||σ(z)−σ(z′)||≤||z−z′||+ε. The return map is
g=−N_c ∘ σ ∘ R_{tb} ∘ (−N_{tb}) ∘ f ∘ R_c.
Successive distance bounds, with d=||v−v′||, are Rd, Rd+ε, (2/a)(Rd+ε), (2R/a)(Rd+ε), (2R²/a)d+(2R/a+1)ε, and finally
||g(v)−g(v′)||≤L d+B ε,
L=16U²/a⁴, B=8U/a³+2/a.

Now ASSUME there is a nonempty closed bounded convex C⊂{v∈S_X:D(v)≥M−δ} with g(C)⊂C, and M>δ+ε. For any η>0 choose a locally finite continuous partition of unity on the metric space C subordinate to its cover by balls of radius η/L, recording a center v_i for each subordinated set. Put ĝ(v)=Σ_i λ_i(v)g(v_i). Local finiteness gives continuity; convexity gives ĝ(C)⊂C. Whenever λ_i(v)>0, the preceding coarse estimate bounds ||g(v_i)−g(v)|| by η+Bε. Thus sup_C||ĝ−g||≤e:=η+Bε.

For any H⊂C, a diameter cover of g(H), pulled back pointwise to H, enlarges by at most2e when its images are taken under ĝ. Thus χ(ĝ(H))≤χ(g(H))+2e≤γχ(H)+2ε/a+2e. The approximate Darbo lemma gives
inf_{v∈C}||v−g(v)||≤(2ε/a+2e)/(1−γ)+e.
Letting η decrease to zero yields the explicit bound
ε[(2/a+2B)/(1−γ)+B].
All constants are dimension independent; no continuity or injectivity of f was added. The missing invariant convex near-maximal C is still assumed, and no uniform terminal chord contradiction has been established. The earlier statement that continuity was unpaid is superseded by this continuation.

## Terminal sign warning: an explicit norm profile

Fix 0<B<1 and θ=1−B. In ℓ∞² put v=(1,B) and y=(−h,1), where 0<h<1. Both vectors are unit. Along 0≤s≤θ,
F_h(s)=||v+s y||∞=max(1−hs,B+s).
At s=0 the unique supporting coordinate gives derivative −h, while at s=θ the unique active coordinate is the second one and every support functional there takes value B on v. The support-intercept gap 1−B is fixed, yet the initial decrease and its maximum depth tend to zero: the minimum occurs at θ/(1+h) and equals 1−hθ/(1+h). Thus a fixed endpoint intercept bound together with the conclusion that all initial supports are strictly negative on y does not, by itself, give a uniform positive improvement in the norm.

This profile is NOT asserted to satisfy the complete aligned-chord equations, every radial defect inequality, or any global sphere near-isometry. It does not refute a power-law rate. It only shows why the source's qualitative support-sign perturbation cannot be assigned a quantitative margin without using additional constraints. No source theorem is challenged.

## Bounded terminal attempt: what fixed-scale compactness can and cannot supply

Parent requested one further attempt to replace the small support-slope interval by finite difference quotients at an M-dependent scale. The following compactness reduction isolates the issue but does not produce an explicit scale or solve the core problem.

Encode the two planes by seminorms N_X,N_Y on R² with N_X(e_1)=N_X(e_2)=N_Y(e_1)=N_Y(e_2)=1. This includes linearly dependent v,y or w,b by quotienting the kernels. These seminorms are bounded above by the ℓ1 norm and are equi-Lipschitz in that norm; their restrictions to every bounded square form a compact family, and limits remain seminorms with the same normalized axes. Thus no arbitrary coordinate condition number is silently imposed.

An exact aligned terminal configuration can be encoded by t,p,r,s,u,M, with a≤p,r,s,u≤U, p+r=s+u≤2 and s−p=r−u=M>0; four unit contact equations
N_X(p,t)=N_X(−r,t)=N_Y(s,t)=N_Y(−u,t)=1;
the two sphere distance equations
N_X(p,t−1)=N_Y(s,t−1),
N_X(−r,t−1)=N_Y(−u,t−1);
and for every q∈[0,1] the two radial bounds
|N_Y(s,t−q)−N_X(p,t−q)|≤M,
|N_Y(−u,t−q)−N_X(−r,t−q)|≤M.
The source terminal argument uses precisely these data, normalized axes, and convexity/support functionals; its inverse configuration merely exchanges the planes and negates the first axes. Hence the exact system has no solution with M>0. This is a use of the source terminal proof, not a new Tingley proof.

Fix m>0 and confine M to [m,2], t to [m/4,1−m/4], and the four radii to [m/4,2], also imposing their source bounds and the radius equalities exactly. The parameter set and seminorm family are compact. The maximum violation of the four contact equations, two distance equations, and the two radial inequalities is a continuous function: the supremum over q is continuous uniformly because the seminorms have a common Lipschitz constant. If the parameter set is nonempty, its minimum violation is strictly positive by the preceding exact contradiction. Therefore for each fixed m some positive robust terminal tolerance exists, even for degenerate coordinate planes. This conclusion does not rely on a lower bound for the initial support slope.

Each radial difference is 2-Lipschitz in q, so a grid of mesh h approximates its supremum within2h. This explains how a known positive terminal tolerance would lead to a finite test. It does NOT give the tolerance as a function of m, an explicit mesh, an algorithm with a proved runtime, or a power law. Attempting to use a fixed finite-difference interval simply replaces the missing slope margin by this uncomputed tolerance. No complete new quantitative interface was obtained.

In particular this reduction cannot repair the earlier invariant-convex-core assumption. It also cannot be promoted to the already paid all-space unspecified modulus as a new nominee. The full explicit-rate question remains unresolved, and no target was frozen.
