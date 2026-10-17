# Family 353: affine completeness feasibility and contribution risk

Author: Myeongjin Kang, no affiliation. Original prose CC BY 4.0. This is a feasibility record, not a frozen nominee, independent verdict, acceptance, or priority claim. Source truth is stipulated at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The full intended possible target is affine-metric completeness of the smooth nonquadratic entire classical affine maximal graph in dimension ten constructed by the pinned source. It is not merely Euclidean completeness, which is automatic for an entire graph. No stronger asymptotics or global Hessian lower bound for the graph function u is claimed.

## Exact source interfaces

In `Smooth-Nonquadratic-Affine-Maximal-Graph-in-Dimension-Ten-October-5-2026/build/source/main.tex`, use Proposition `prop:reduction`, Lemma `lem:local`, equations `eq:radial`, `eq:hessian`, `eq:det`, Lemma `lem:box`, and Proposition `prop:global`. They give smooth positive radial F,P on R^9 with F(0)=P(0)=1, H=D²F positive, H(0)=I, y=F'>0, y'>0 for r>0, and

    y^8 y' = r^8 F P^(-12/11),
    (y^8 P')' = -11 r^8 P^(-1/11),
    0 <= -rP'/P <= 33/2.

The origin regularity and integrated second equation imply P'<0 for all r>0. The source gives u(x,t)=sqrt(F(x)^2+t²), D²u>0, and the classical affine maximal equation with determinant exponent -11/12. It explicitly does not assert affine completeness. That omission is not itself evidence of substantiality.

## Exact metric calculation, including the origin

The Berwald–Blaschke metric in dimension ten is

    g = (det D²u)^(-1/12) D²u.

Set ζ=t/F(x) and v=asinh ζ. Since F is positive and smooth on all R^9, (x,v) -> (x,F(x)sinh v) is a global smooth diffeomorphism, with smooth inverse; this includes x=0. The Hessian identity is an identity of quadratic tensors before changing coordinates, not an assertion that Hessians transform as Hessians of a new scalar function. Its pullback and the determinant identity give

    D²u = (1+ζ²)^(-1/2) H + F(1+ζ²)^(-3/2)dζ²,
    det D²u = P^(-12/11)(1+ζ²)^(-6),
    g = P^(1/11) [H + F dv²].

The determinant on the second line remains the determinant in the original affine coordinates (x,t); it must not be recomputed as a coordinate-dependent metric determinant. In particular the power 1/11 is exact, and all tensors extend smoothly across r=0.

## Lower bound obtained from source operations

Put a(r)=F(r)P(r)^(-12/11). It is increasing and a(r)>=1. Integration from the regular origin gives

    y(r)^9 = 9 integral_0^r ρ^8 a(ρ)dρ,
    r^9 <= y(r)^9 <= r^9 a(r).

Consequently y/r>=1 and y'=r^8 a(r)/y^8>=a(r)^(1/9)>=1. Thus H>=I on R^9, including the origin. This is a lower bound for D²F, not D²u.

For r>=1 integration of -rP'/P<=33/2 yields P(r)>=P(1)r^(-33/2); for r<=1 monotonicity gives P(r)>=P(1). Let c=P(1)^(1/11)>0. The base metric h=P^(1/11)H therefore satisfies

    h >= c max(1,r)^(-3/2) |dx|².

A radial exhaustion is

    R(r)=sqrt(c) integral_0^r max(1,s)^(-3/4) ds,

which tends to infinity. For every piecewise smooth base path, |dR/ds| is bounded by its h-speed almost everywhere, including passages through x=0. Hence h-distance controls the difference of R. Every h-metric bounded set has bounded Euclidean radius. On every Euclidean compact set, smooth positivity gives uniform upper and lower metric bounds. A Cauchy sequence for h is consequently confined to a Euclidean compact set and converges, so h is complete. This argument does not assume existence of an escaping radial geodesic or exact asymptotics of F or P.

## Fiber direction and the full metric

Write g=h+q(x)dv² with q=P^(1/11)F>0 smooth. Projection to the base decreases lengths. A g-Cauchy sequence has h-Cauchy projections, which converge. To control v without assuming minimizing paths stay in an arbitrarily chosen compact set, fix a base h-ball containing the projected sequence and enlarge its radius by 1. Its closure is Euclidean compact by the preceding radial exhaustion. For sufficiently late pairs, choose paths of g-length less than twice their distance and less than 1. Their base projections stay in this enlarged ball. If q>=q0>0 there, then |v_j-v_k|<=length/sqrt(q0). Thus v_j is Cauchy. Smooth local metric bounds give convergence in g. Equivalently, any finite-length escaping path must have bounded base and then bounded fiber, which is impossible. The full metric is complete.

This proves the desired additional property of the exact source example at feasibility level. Nonquadraticity, strict convexity, and the PDE remain the stipulated source conclusions; this note does not reprove or audit them.

## Actual primary operation comparison and limits

Trudinger–Wang, Inventiones 2000, Section 7 (extracted lines 952–1110; rendered printed pages 419–420 inspected): the singular dimension-ten profile and its affine coordinate change reduce the PDE to a power profile; their extension argument is for a weak singular solution. That construction has no smooth positive Hessian on the axis and does not prove this smooth example's affine completeness.

Trudinger–Wang, Inventiones 2002 (extracted lines 1–300 and 431–475; rendered printed pages 47 and 49 inspected): affine completeness implies Euclidean completeness. Their metric/Legendre formula and Lemma 2.1 use bounded gradient images to produce finite affine arclength when Euclidean completeness fails. They explicitly distinguish the two completeness notions; their theorem does not reverse the implication. Our exact warped metric identity and source logarithmic derivative bounds are extra information, but radial integral divergence and positive warped-fiber completion are elementary metric arguments.

Sun–Xing–Xu, arXiv 2608.25330 (extracted lines 70–250; rendered page 4 inspected): Section 2 constructs Euclidean-complete examples for a different determinant-exponent range using a power on a parabolic domain. Its range does not include the classical exponent in dimension ten. The later Calabi-metric arguments were not fully read and are not used. The download URL was unversioned, so its retained SHA256, rather than an inferred version, identifies the inspected bytes.

Primary PDF byte receipts are in private/primary-receipts.json. Their bodies are private inputs, not original output or licensed for republication. These bounded comparisons do not establish worldwide priority or exclude all other treatments of affine completeness.

## Historical screen and contribution assessment

Iteration i140 was read in full; i143 lines 1–65 and the focused matching paragraphs in task records i143/i146 were inspected. Those developed a normalized cubic-defect route and explicitly observed that affine completeness was not supplied by the source. No prior affine-completeness target was found in the bounded focused history search. This is not a claim to have semantically reread every older file.

The additional property is a mathematically complete consequence using an exact tensor cancellation. However, the source has already paid for the smooth example and the logarithmic box; the remaining lower bound, divergent integral and warped-product completion are short standard deductions. There is serious risk that this is TECHNICAL under the campaign's substantiality threshold. No target was frozen before this feasibility deduction, so this document must not be retroactively presented as a pre-proof freeze. Parent subsequently assessed this completion as TECHNICAL and directed preservation as an unfrozen screen. It is not being nominated. No gate or count is changed.
