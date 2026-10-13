# I201 analytic record: elliptic finite covers and the remaining bridge

2026-10-12. **NO SUBSTANTIAL NOMINATION.** The corrected finite-cover estimates below are proved; the optimal general elliptic cost and a stronger convex-body consequence are not. Eight findings remain accepted, two remain. No research code, numerical experiment, child agent, upstream audit or acceptance review was performed.

## 1. Contracts and exact objectives

Put

    E(D,V,L) = {(s,p+sV(p)): p in D, |s| <= L},
    F_h(s,x,y) = (s,x,hy),
    J_h(g) = (1+g_1^2+h^2 g_2^2)^(-1/2).

D is compact in R²; V is C¹ on an open neighborhood of D; L,h>0 are fixed before choosing errors or meshes. A cylinder with intercept tile T and velocity g has physical perpendicular area h|T|J_h(g). This is the accepted ruled-set paper's `b:projection`.

The accepted `b:approximation` already proves the bound h integral_D J_h(V)+epsilon if tr DV=0 and -L^(-2)<det DV<=0 on D. It includes all compact label sets, positive-area boundaries, zero-area sets, arbitrary nilpotent shear, and mixed hyperbolic/nilpotent derivatives. Its orthogonal zero-diagonal lemma and nonlinear finite-retention argument are paid operations. We do not challenge or re-prove their source truth.

The new question is the positive-determinant part. For an affine frozen field W(p)=v+A(p-b), a common intercept shape F and label lattice Gamma give transverse covers

    R² = F + (I+sA)Gamma,    |s|<=L.

Define c_L(A) as the infimum of |F|/covol(Gamma) over bounded measurable F and full-rank lattices Gamma for which these are actual covers at every height. This is a restricted periodic affine optimization problem, not the infimum over arbitrary finite cylinder covers of E. For tr A=0, det A=d>0, set k=L sqrt(d).

A necessary bound is c_L(A)>=1+k². At s=L, integrate the multiplicity of F+(I+LA)Gamma over one fundamental domain: its mean is |F|/[(1+k²)covol(Gamma)], at least one. This is a planar density bound, not a new arbitrary-axis cylinder lower bound.

Two serious routes were pursued:

* **Route A:** build simultaneous affine covers, then prove actual finite nonlinear covers and boundary retention. Extended squares give a quadratic determinant correction. Convex rotational cells give the density optimum at three resonances.
* **Route B:** use bounded common fundamental domains at the two extremal heights to attain the density optimum for every k. A concrete polytopal counterexample shows that endpoint tilings and all intermediate density inequalities do not imply intermediate coverage. The needed all-height selection remains open here.

## 2. Route A1: extended squares give a complete corrected finite theorem

### 2.1 Exact affine construction

Let tr A=0, d=det A>0. By the accepted orthogonal zero-diagonal lemma, in orthonormal coordinates

    A = [[0,b],[c,0]],       bc=-d<0.

Let Q=[-1/2,1/2]² and a=(1/2,1/2). For s≠0 set

    R_s = {a+(t_1 sb,t_2 sc): 0<=t_1,t_2<=1}.

Kolountzakis, *Lattice Tilings by Cubes: Whole, Notched and Extended*, §2.3, equations (17)–(21), with delta_1=-sb and delta_2=-sc, gives a tiling almost everywhere

    (Q union R_s) + (I+sA)Z² = R².

Here delta_1 delta_2=s²bc<0, so the signed formula is an indicator **sum**, not the subtractive notched-square formula. The matrix in that paper is transposed in the lattice formula: its transpose is exactly [[1,sb],[sc,1]]. This sign/transposition check is essential. Its determinant is 1+s²d; the tile has that same area.

All tiles are closed and bounded, and the lattice is discrete. Their union is therefore closed and locally finite. An almost-everywhere cover by that union is a cover of every point: a missing point would have an open missing neighborhood of positive area. This explicitly retains boundaries.

For 0<s<=L, R_s is contained in R_L; for -L<=s<0, R_s is contained in R_(-L). Thus the single compact shape

    U_A = Q union R_L union R_(-L)

covers R² under every center lattice (I+sA)Z². At s=0, Q alone covers. Since b and c have opposite signs, Q, R_L and R_(-L) have pairwise disjoint interiors. Therefore

    |U_A| = 1+2L²d.                                      (A1)

Their distances from the origin are uniformly bounded by K=2(1+LM) when ||A||<=M. For d<=0 in the accepted spectral range, take U_A=Q and use `b:affine-cover`. For d=0 this includes either zero off-diagonal coefficient without any limiting argument. Altogether the cost multiplier is

    Phi_L(A)=1+2L²(det A)_+ .                            (A2)

U_A is a union of at most three rectangles. Each rectangle can be used as a separate cylinder with the same velocity. Hence the construction yields compact nondegenerate parallelogram perpendicular bases after F_h, not merely disconnected measurable bases. In the elliptic case both extra rectangles have positive area; in the other cases they are omitted.

This is not square inflation by ||A||. The area penalty depends only on the positive determinant; arbitrarily large nonnormal shear affects the diameter and finite count, but not (A2). The ingredient producing the extra rectangles is, however, already in Kolountzakis's 1998 theorem.

### 2.2 Finite nonlinear theorem, all quantifiers and boundary retention

**Proposition A.** Suppose tr DV(p)=0 and det DV(p)>-L^(-2) for every p in D. Then for every epsilon>0 there is a finite cover of F_h(E(D,V,L)) by cylinders with compact nondegenerate parallelogram perpendicular bases, of total area at most

    h integral_D [1+2L²(det DV(p))_+] J_h(V(p)) dp + epsilon.       (A3)

No boundary regularity of D is required. There is no upper bound on det DV or on the shear beyond the boundedness that follows for the fixed C¹ field on a compact neighborhood. No count uniform as the negative spectral margin vanishes is asserted.

**Proof.** The empty set is trivial. Choose a compact neighborhood D_a in the domain, a bound M on ||DV|| there, and a common modulus omega(r) for DV on that neighborhood. Let

    sigma = min(1, min_D(1+L² det DV)) > 0,
    C = (1+LM)/sigma,     K=2(1+LM).

Cayley–Hamilton gives, for every frozen A=DV(b), b in D,

    (I+sA)^(-1)=(I-sA)/(1+s² det A),
    ||(I+sA)^(-1)|| <= C,               |s|<=L.          (A4)

Take all closed squares S of side delta in a fixed grid that meet D and choose b_S in S intersect D. Put A_S=DV(b_S) and W_S(p)=V(b_S)+A_S(p-b_S). For sufficiently small delta these squares lie in D_a, and

    |V(p)-W_S(p)| <= eta_delta delta,
    eta_delta=sqrt(2) omega(sqrt(2)delta) -> 0             (p in S).

For each S use its orthogonal affine construction above with fine spacing tau=delta² and lattice b_S+tau Z² in that construction's coordinates. Its intercept shape at l is l+tau U_(A_S), with velocity W_S(l). This infinite family covers each entire transverse plane for all allowed heights, because its centers are l+sW_S(l).

Fix an actual target p+sV(p), p in D intersect S. Some l satisfies

    p+sV(p) = l+sW_S(l)+tau u,       u in U_(A_S).

Consequently, using |u|<=K and (A4),

    |l-p| <= C(K tau+L eta_delta delta) =: R_delta = o(delta).  (A5)

Retain all l at distance at most R_delta from S. This is a finite list independent of p and s. Equation (A5) proves coverage at every height, including endpoints, for every label, including the boundary of D. There are no exceptional labels discarded by a measure argument.

The ordinary fine squares l+tau Q have disjoint interiors, even though the actual U-tiles need not. These fine squares for retained l lie in the (R_delta+tau)-neighborhood of S. Hence their number N_S obeys

    N_S tau² <= (delta+2R_delta+2tau)² = delta²(1+o(1)).

The sum of actual intercept areas from this S, including multiplicity, is exactly N_S tau² Phi_L(A_S). Every retained l has |l-b_S|=O(delta), so W_S(l)=V(b_S)+O(delta). Uniform continuity of J_h and boundedness of Phi_L give the weighted patch estimate

    sum_(l retained) tau² Phi_L(A_S) J_h(W_S(l))
        <= delta² Phi_L(A_S) J_h(V(b_S))+o(delta²).

The errors are uniform in S: K,C,M,L,h and omega are fixed, and Phi_L is continuous. No continuous choice of orthogonal zero-diagonal bases is needed. Split each U-tile into its one or three rectangles; the area estimate is unchanged.

There are O(delta^(-2)) coarse squares. Their union U_delta satisfies D subset U_delta subset D_(sqrt(2)delta). The continuous function Phi_L(DV)J_h(V) is bounded on D_a. Continuity from above of Lebesgue measure implies |U_delta minus D|->0, even for positive-area boundaries. Thus the patch sum tends to the integral in (A3). Select sufficiently small delta to make the physical error at most epsilon. Projection gives the stated parallelogram bases and areas. QED.

**Dependence.** The count and permitted delta depend on a, a bounded container of D, L,h,M,sigma, the modulus omega, and the outer-neighborhood measure convergence of D. The proof gives a finite count O(tau^(-2)) with these fixed data, not a boundary-independent rate in epsilon.

### 2.3 Specified C¹ stability

On the same fixed neighborhood suppose ||W-V||_infinity<=gamma and ||DW-DV||_infinity<=gamma, and suppose **both** fields are trace free on D. If

    L²(2M gamma+gamma²) < sigma/2,

then W remains in the allowed negative spectral range. Indeed

    |det DW-det DV| <= 2M gamma+gamma².

Let H=max(1,h), so |J_h(W)-J_h(V)|<=H gamma. The difference between the two integral upper bounds, before multiplying by h, is at most

    |D| {2L²(2M gamma+gamma²) + (1+2L²M²)H gamma}.        (A6)

This follows from the 1-Lipschitz property of t->t_+, J_h<=1, and the preceding determinant estimate. Proposition A applies separately to W with any requested finite error. This is stability of a proved **upper-bound functional**, not continuity of the optimal covering cost. Perturbations which lose the trace condition are outside (A3); no such extension is silently assumed. This elementary stability estimate is not a finding.

## 3. Route A2: convex rotational cells and sharp periodic resonances

For d>0 write A=S(omega J)S^(-1), omega=sqrt(d), J(x,y)=(-y,x). A real S exists since A²=-dI. For example use columns e,Ae/omega with any nonzero e; they are independent. Its orientation is irrelevant to area ratios. Let P_n be the centered regular n-gon, n=4 or 6, of circumradius one. P_4 tiles by a square lattice; P_6 is the Voronoi cell of the triangular lattice. Their images Q=S P_n tile by the correspondingly transformed lattice Gamma.

Use the common compact convex shape

    T = conv((I-LA)Q union (I+LA)Q).

For every |s|<=L, (I+sA)Q subset T, since I+sA is the convex combination of the two endpoint maps. Therefore, for an affine field, each complete label cell l+Q is covered by the cylinder with intercept l+T and velocity W(l). This is an actual cover at all heights, not an endpoint-only assertion.

Put k=L omega, theta=arctan(k), alpha=2pi/n. The two endpoint polygons in S-coordinates have common circumradius sqrt(1+k²) and angular displacement 2theta. Reduce this displacement modulo alpha to d_n in [0,alpha). Their hull has alternating angular gaps d_n and alpha-d_n. Summing the areas of the triangles from the origin yields

    q_n(k)=|T|/|Q|
          =(1+k²)[sin(d_n)+sin(alpha-d_n)]/sin(alpha).    (A7)

At d_n=0 this is interpreted by continuity. Explicitly,

    q_4(k) = 1+2k-k²                    (0<=k<=1),
             k²+2k-1                    (k>=1);

    q_6(k) = 1+(2/sqrt(3))k-k²          (0<=k<=1/sqrt(3)),
             4k/sqrt(3)                  (1/sqrt(3)<=k<=sqrt(3)),
             k²+(2/sqrt(3))k-1           (k>=sqrt(3)).   (A8)

At k=1 the square gives q_4=2=1+k². At k=1/sqrt(3) and sqrt(3), the hexagon gives q_6=4/3 and 4 respectively, again 1+k². The endpoint polygons then coincide, and their hull is just one endpoint polygon. The density lower bound in §1 proves

    c_L(A)=1+k²   for k in {1/sqrt(3),1,sqrt(3)}.          (A9)

This is sharp for the stated periodic affine model, including arbitrary bounded measurable common shapes in its lower bound. It is not sharpness for arbitrary finite cylinder covers of E. No claim that (A8) optimizes all shapes or all k is made.

**Finite nonlinear realization of (A7).** If tr DV=0 and det DV>=d_0>0 on D, one obtains finite convex polygonal-base covers with cost

    h integral_D min(q_4(k(p)),q_6(k(p))) J_h(V(p)) dp + epsilon,
    k(p)=L sqrt(det DV(p)).                              (A10)

Here is the retention and error argument, which differs slightly from §2 because it assigns entire label cells. Since ||DV||<=M and det DV>=d_0, the similarities S can be chosen with ||S||, ||S^(-1)|| uniformly bounded after area normalization. To check this directly, in fixed coordinates A=[[a,b],[c,-a]] has |c|>=d_0/M; use columns e_1,Ae_1/omega and normalize its nonzero determinant. All polygon cells then have uniformly bounded diameter and positive uniformly bounded area, as do their endpoint hulls.

On each coarse square freeze A and the same affine field W_S as in §2, choose n attaining the minimum in (A10), and use cells l+tau Q of that tiling. Retain every cell meeting S. A retained center is at distance at most C_0 tau from S; its entire cell lies in the 2C_0 tau collar. Thus N_S tau²|Q|<=delta²(1+O(tau/delta)). Every p in S is in a retained cell, including cell edges. For its assigned l the actual intercept differs from

    l+(I+sA)(p-l)

by at most L eta_delta delta. Enlarge l+tau T by a closed disk of that radius, for all s simultaneously. Choose

    tau=delta sqrt(eta_delta+delta).

Then tau/delta->0 and eta_delta delta/tau->0. The parallel-body area formula gives

    |tau T+B(0,L eta_delta delta)|
      =tau²|T|+tau Per(T)L eta_delta delta
                     +pi(L eta_delta delta)²
      =tau²(|T|+o(1)),

uniformly in S. These are compact convex bases with interior. The retained list covers every point and height; the same outer-neighborhood summation proves (A10). If polygonal rather than rounded intercept bases are desired, enclose the added disk by a square of comparable radius; the same o(1) bound follows by polygonal parallel expansion.

For a fixed elliptic field with det>=d_0, small C¹ perturbations retaining trace zero and det>=d_0/2 preserve (A10), by uniform continuity of q_n on the bounded k-range. For the *fixed templates* the explicit containment T_B subset T_A+B(0,L||B-A|| max_Q |x|) gives the same area estimate. Template conditioning and constants depend on M,d_0,L,h. This does not claim uniform template conditioning as d_0 tends to zero.

Combined comparisons give, for d>0,

    1+k² <= c_L(A) <= min(1+2k²,q_4(k),q_6(k)).          (A11)

The left bound and the resonant equalities are local periodic statements. Proposition A separately handles mixed derivatives without d_0. Near k=0, q_6=1+(2/sqrt(3))k-k² has a linear excess, whereas 1+2k² is better. This is why the initial convex-envelope construction alone would have been an unsatisfactory perturbative bridge.

## 4. Route B: common endpoint tiles and an explicit all-height failure

Grepstad–Kolountzakis (2025), Theorem 1, proves that any two lattices of equal covolume have a bounded common fundamental domain, even a finite union of polytopes. Applied to

    Gamma_-=(I-LA)Gamma,    Gamma_+=(I+LA)Gamma,

this supplies an endpoint tile F of area (1+k²)covol(Gamma), exactly the lower bound in §1, for every k. Taking closures of the finitely many polytopes changes no area and upgrades endpoint almost-everywhere tilings to covers by local finiteness. That genuine theorem eliminates an endpoint-only obstruction. It does **not** supply coverage at intermediate heights.

### Explicit failure of the endpoint interpolation shortcut

Set A=J, L=1 and Gamma=(I+J)^(-1) Z². Then Gamma_+=Z² and Gamma_-=-J Z²=Z². At s=1/2 the center lattice is

    Lambda = T Z²,
    T=(I+J/2)(I+J)^(-1)=[[3/4,1/4],[-1/4,3/4]],
    covol(Lambda)=5/8.

Let Q=[0,1]² and z=(2,0). Since T^(-1)z=(12/5,4/5), z is not in Lambda. The finite set P=Q intersect Lambda has positive distance from Lambda after translation by z. Choose a sufficiently small union E of relative-open axis-aligned squares in Q around every point of P such that

    (closure(E)+z) intersect Lambda = empty.

This is possible because P is finite, z not in Lambda, and Lambda is discrete. Define

    F=(Q minus E) union (closure(E)+z).

F is compact and a finite union of polygons; the two pieces have disjoint interiors because Q and Q+z do. Boundaries have area zero, so |F|=1. Also F+Z² covers the whole plane: every representative q in Q was either left in place or translated by the integer vector z. Thus F tiles/covers both extremal lattices at their exact covolume. But F intersect Lambda is empty by construction, so

    0 not in F+Lambda.

The intermediate height is missed even though its lattice has strictly smaller covolume 5/8. The gap has positive distance from the closed locally finite union, so this is not a boundary convention issue. All steps are symbolic; no search or experiment was used.

This refutes the implication “a bounded common endpoint tile plus a determinant maximum at the endpoints covers the entire affine path.” It does not refute the existence of a specially selected all-height tile of optimal area. At this very k=1, §3 in fact constructs such a tile. Choosing the *right* common tile is the unpaid part of the proposed general-k route.

Grepstad–Kolountzakis–Spyridakis (2025) adds bounded polytopal tiling/packing for two unequal-covolume lattices. Its conclusion is packing for the larger-covolume lattice, not the simultaneous-cover property needed here. Reversing that implication would be an error. Pairwise applications to more heights do not construct one common F for the continuum, and the literature explicitly distinguishes two-lattice results from multiple-lattice problems. No equivalence with the full Steinhaus problem is asserted.

## 5. Rotation check, geometric consequences attempted, and contribution decision

For V(p)=omega Jp on the radius-rho disk, put k=L omega. The existing I198 lower bound, generalized only for comparison, is

    sum base areas >= pi rho² (1+k²/3)
                     /sqrt(1+(rho²/L²)(1+k²)).           (G1)

It follows from the stated slice areas pi rho²(1+omega²s²), their volume integral and the diameter upper bound. This known volume/chord argument is not counted as new work. The exact integral weight for h=1 is

    I=2pi/omega² [sqrt(1+omega²rho²)-1].

Proposition A costs (1+2k²)I+epsilon; (A10) costs min(q_4,q_6)I+epsilon. At k=1 the latter is 2I, consistent with the I198 radius-1/10 obstruction, which is strictly above pi rho² and hence above the unchanged I. As rho/L tends to zero with k fixed, I/(pi rho²)->1, while (G1)'s normalized factor tends to 1+k²/3. The periodic density lower factor is instead 1+k². These are different admissible-cover classes; conflating them would falsely claim global sharpness. A nonzero gap remains even at the periodic resonances.

The rotational sweep itself is not a convex-body application. Its end sections are disks of radius R=rho sqrt(1+k²), while its middle section has radius rho. The points (L,R e_1) and (-L,R e_1) are in the sweep and their midpoint (0,R e_1) is not. Indeed its convex hull is the full cylinder [-L,L] times the radius-R disk. A cover of the sweep need not cover this hull. Thus neither (A3) nor (A9) supplies an improved covering of a new convex body merely by taking a convex hull.

For a prospective small-tilt tetrahedral construction V=tW, the determinant correction in (A3) is quadratic, not linear:

    [1+2L² t²(det DW)_+]J_h(tW)
     =1+t²{2L²(det DW)_+-(W_1²+h²W_2²)/2}+O(t^4)

uniformly for bounded W,DW. This identifies the penalty that any such construction must pay, in addition to overlap/cap corrections. It does not furnish a wall-compatible field, an improved overlap budget, or a better coefficient. A strict improvement would require these additional geometric proofs. Perturbing an already successful nilpotent construction by a tiny elliptic field and preserving its strict saving would only be a continuity consequence, not evidence that ellipticity improves the problem.

Comparison with every companion:

* The ruled-set theorem already supplies zero penalty for hyperbolic/nilpotent derivatives. Proposition A reduces exactly to its cost there and borrows its retention operation. It does not improve that theorem on its old domain.
* The slope-field paper already provides regular rational, singular hyperbolic and nilpotent tetrahedral constructions, with both compact parallelogram and open-base versions and affine transport of normalized costs. No new field improving them was constructed.
* The angular paper already has explicit finite triangular covers, controlled remainder, and the cubic-buffer family with normalized cost 1/2-t²/240+(25/2)t³+O(t⁴). The recorded elliptic constructions give no smaller verified coefficient.
* The radial companion already includes the apex, arbitrary tags, one triangular cylinder per interval and actual projected-base convergence. Its `sec:freezing` already embodies freezing a direction and enclosing its intercept error. Our polygon envelopes are not a new general principle of that kind.

Bezdek–Litvak's Theorem 3.1 gives the directionwise lower bound 1/3 for arbitrary three-dimensional convex bodies and 1 for ellipsoids; its proof also gives the 1/3 absolute minimum-shadow bound. These are the relevant established primary bounds read here. Our estimates neither improve them nor supply a convex-body example beyond the source's [1/3,1/2) tetrahedral situation. No assertion about an exhaustive worldwide best bound is based on a failed keyword search.

**Verdict.** Proposition A is a useful corrected finite elliptic theorem, but its core is an explicit combination of the 1998 extended-square identity with the accepted finite-retention construction. The resonant optimal periodic cells are a sharp restricted mechanism with an elementary convexity proof; no substantive additional convex-body result has been established. Route B exposes a real selection gap, not a universal obstruction to the optimal cost. Thus neither a globally sharp corrected cost nor the requested stronger geometric consequence is proved. These results are retained as technical deductions and failed routes, not offered as the ninth finding. Both independent acceptance gates remain with the parent and were not run.
