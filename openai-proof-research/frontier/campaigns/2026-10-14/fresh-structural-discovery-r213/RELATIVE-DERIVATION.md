# Complete compatible reduction: integral relative fillings by convex doubling

These are prefreeze compatibility calculations, not a frozen nominee or a claim of substantial contribution. They integrate the stipulated Source337 companion with classical gluing, projection, slicing, compactness and reflection. The initially recorded zero-mass-seam restriction was unnecessary for the relative objective; the full argument below supersedes that incomplete feasibility discussion without erasing it.

## 1. Conventions and constants

Let n≥2 be the boundary-current dimension, q=(n+1)/n, s_n=(n+1)ω_(n+1), c_n=1/((n+1)s_n^(1/n)), and K_n=2^(1/n)c_n. X is a proper CAT(0) space, C⊂X is nonempty closed convex, and U=X\C. All currents have integer coefficients and Ambrosio–Kirchheim mass. I_k(X) means integral currents of finite total mass and finite boundary mass; compact support is stated separately. A locally integral relative n-cycle T on U has ∂_U T=0 and finite total mass a=M_U(T). No globally finite trace on C is assumed.

For such T define

    V_rel(T)=inf { ||Q||(U): Q∈I_(n+1)(X), (∂Q)|U=T }.

This definition measures exterior mass, permits mass on C, and requires a globally integral representative Q. It is stronger on representatives than merely asking for a locally integral filling in U. It does not identify ambient mass with relative mass. Restrictions to U in this definition mean equality on tests supported compactly inside U; the resulting local currents need not have finite global boundary mass in U's completion.

The completed reduction establishes V_rel(T)≤K_n a^q, with attainment, and an exact equality with half an absolute filling volume in a convex double. If T extends globally as a compact integral current with boundary supported on C, the construction gives a compact Q with an explicit projected cap. For general finite mass, supports need not be bounded. The steps proving this are below; no compactness or tightness assumption is suppressed.

## 2. A local compactness consequence with no assumed tightness

We need the following standard consequence of AK compactness and closure. Suppose X is proper and Q_j∈I_k(X) have uniformly bounded M(Q_j)+M(∂Q_j). There is a subsequence converging on compactly supported tests to a locally integral Q. Its global mass is at most liminf M(Q_j), after first taking a subsequence realizing this liminf. If ∂Q_j converges locally to a fixed finite-mass integral current A, then ∂Q=A globally and Q∈I_k(X).

Here is the localization argument, rather than an invocation of global tight compactness. Fix o∈X. The slicing inequality bounds the integrals of M(<Q_j,d_o,r>) on each interval (l,l+1) uniformly. Fatou gives a radius r_l∈(l,l+1) at which the liminf of these slice masses is finite and each restriction is integral. Pass to a subsequence with bounded slice mass at this radius. The restrictions Q_j⌞B_(r_l)(o) now have bounded normal mass and common compact support. AK Theorem 5.2 and integral closure 8.5 give a further subsequence and a limit on this ball. Repeat at larger radii and take a diagonal subsequence. On the interior of any smaller ball the limits agree, since evaluation there is evaluation of the original currents. This defines Q on compactly supported tests. Boundary commutes with this convergence on such tests. Lower semicontinuity on each open ball and monotone convergence give M(Q)≤liminf M(Q_j).

To extend Q to all bounded Lipschitz current tests, use bounded radial cutoffs equal to one on B_R, supported on B_(2R), with Lipschitz constant ≤1/R. Finite mass makes evaluation Cauchy as R→∞. The local continuity axiom extends by first fixing R and then controlling the tail by ||Q||(X\B_R). Local integer rectifiability on a countable exhaustion yields global integer rectifiability. In the boundary identity, the extra cutoff term is bounded by M(Q)/R times the product of the other Lipschitz constants. It vanishes; the prescribed finite boundary A therefore remains the global boundary. This proves the claim. This is local convergence, not global weak convergence claimed in the absence of tightness. Escaping positive mass may be lost, which only helps a minimization upper bound.

Consequently, any finite-mass integral cycle with some finite-mass filling has an absolute mass minimizer: apply this argument to a minimizing sequence with fixed boundary. No common support ball is needed for this conclusion in a proper ambient space.

## 3. Extending the paid absolute bound beyond compact support

The companion states its sharp bound for compactly supported cycles. We can pass to every A∈I_n(X) with ∂A=0 and finite mass. This is a classical truncation-and-repair composition, not an unpaid hypothesis removal.

Choose r_j∈(j,j+1), tending to infinity, at which A⌞B_(r_j)(o) is integral and its boundary Z_j is the slice of A. The slicing integral over (j,j+1) is bounded by ||A||({d_o>j}); choose r_j so that M(Z_j)≤2||A||({d_o>j}), which tends to zero. Z_j is a compact integral (n−1)-cycle. Since n−1≥1, Wenger's Euclidean-type filling inequality gives an integral repair R_j with

    ∂R_j=Z_j,  M(R_j)≤D_(n−1) M(Z_j)^(n/(n−1))→0.

Only a finite dimensional constant is needed; n=2 uses the ordinary one-cycle inequality. Projection onto the compact convex closed ball B̄_(r_j)(o) makes the repair compactly supported without increasing mass or changing its boundary. Set A_j=A⌞B_(r_j)(o)−R_j. Then A_j is a compact integral cycle and

    M(A_j−A)≤||A||(X\B_(r_j))+M(R_j)→0.

Apply the paid sharp source to obtain S_j with ∂S_j=A_j and M(S_j)≤c_n M(A_j)^q. Their boundary masses are uniformly bounded. Section 2 gives a global integral S with ∂S=A and

    M(S)≤c_n M(A)^q.

The same local compactness argument gives an absolute minimizer. This proves the noncompact extension while accounting for all slice repairs and mass possibly escaping to infinity. For compact A, projection of any filling onto a compact convex ball containing spt A proves that the infimum over all finite-mass fillings equals the compactly supported infimum, and that a minimizer can be confined to that ball.

## 4. Double, fold and projected cap for a globally normal relative cycle

First assume T∈I_n(X) globally and spt∂T⊂C. Put a=||T||(U). Form D=X_+∪_C X_- using two copies with their common C identified. The metric between different copies is

    d_D(x_+,y_-)=inf_(c∈C) [d_X(x,c)+d_X(c,y)].

The copies are isometric and convex. Reshetnyak's gluing theorem makes D CAT(0). It is proper: for c_0∈C, a closed ball about c_0 is the union of the corresponding two compact closed X-balls with their common closed subset identified; every bounded set lies in one such ball. No finite ambient dimension is used.

Let i_± denote inclusions and P_C the nearest projection. Define

    A=i_+#T−i_-#T.

Then ∂A=0, since the two pushforwards of ∂T coincide on C. The pieces of T on C cancel exactly, with their integer orientations and multiplicities. Outside C the copies are disjoint and the inclusions are isometries. Hence

    M(A)=2a.

This is an equality of mass measures on the two disjoint open copies; it is not a no-cancellation assertion about an arbitrary contraction.

Define F_+:D→X as identity on X_+ and P_C on X_-; define F_- oppositely. Both are 1-Lipschitz. For cross-copy points, for every c∈C,

    d_X(x,P_Cy)≤d_X(x,c)+d_X(c,P_Cy)
                 ≤d_X(x,c)+d_X(c,y),

and take the infimum. The within-copy statements are the projection contraction. The maps agree on C, so they are well-defined. They satisfy

    F_+#A=T−P_C#T,  F_-#A=P_C#T−T.

Take an absolute minimizing filling S of A in D. Then Q_+=F_+#S and Q_-=−F_-#S are globally integral, with the same exact boundary T−P_C#T. The crucial relative mass estimates are

    ||Q_+||(U)≤||S||(X_+\C),
    ||Q_-||(U)≤||S||(X_-\C).

Indeed, the full preimage of U under each fold lies in its selected open copy. Apply the pushforward mass estimate there. We never assert that S restricted to one copy has finite boundary mass. Thus

    min{||Q_+||(U),||Q_-||(U)}≤M(S)/2
        ≤K_n a^q.

Also M(Q_±)≤M(S)≤2K_n a^q and M(∂Q_±)≤2M(T). There is no division of a current by two. One selects a fold. If H^(n+1)(C)=0, rectifiability implies ||Q_±||(C)=0, so the selected Q satisfies the same sharp bound for total mass. No such ambient-mass conclusion is asserted for a thick C.

If T is compactly supported, choose c_0∈C and R with spt T⊂B̄_R(c_0). The doubled boundary lies in the compact convex D-ball of radius R. Its minimizer can be projected to that ball; the folds map this ball into B̄_R(c_0). Thus the selected Q is compact with the stated support confinement. This is the paid source confinement plus projection.

## 5. Recovering a globally integral representative from a possibly infinite trace

Now let T be only locally integral on U, with ∂_U T=0 and finite total mass a. Extend its finite-mass integer rectifiable functional by zero on C; global boundary mass is not yet asserted. Let f=d_C. For almost every ε>0, T_ε=T⌞{f>ε} is globally integral, has M(T_ε)≤a, and spt∂T_ε⊂{f=ε}. This follows by local slicing on the sets separated from C and then exhaustion. The global slice mass is finite for almost every ε by the coarea inequality and finite M(T). A radial cutoff in the distributional boundary identity introduces an error ≤a/R; letting R→∞ gives no additional boundary at infinity. This justifies global normality at such ε.

The sublevel C_ε={d_C≤ε} is closed convex: distance to a convex set is convex along geodesics in CAT(0), as in BH II.2.5. Apply Section 4 to (X,C_ε,T_ε). Obtain a globally integral Q_ε such that

    ∂Q_ε=T_ε−(P_(C_ε))#T_ε,
    M(∂Q_ε)≤2a,
    M(Q_ε)≤2K_n a^q,
    ||Q_ε||(X\C_ε)≤K_n a^q.

Choose admissible ε_j↓0. By Section 2, a subsequence converges locally to an integral Q with M(Q)≤2K_n a^q and M(∂Q)≤2a. The latter boundary bound follows from local lower semicontinuity and exhaustion; no prior boundary limit is needed in this instance. On tests supported a positive distance from C, the projected term vanishes for small ε_j and T_εj=T. Thus (∂Q)|U=T.

For each fixed δ>0 and sufficiently large j, {d_C>δ}⊂X\C_εj. Lower semicontinuity, first on bounded open subregions if necessary, gives

    ||Q||({d_C>δ})≤K_n a^q.

Let δ↓0. Monotone convergence gives ||Q||(U)≤K_n a^q. In particular B=∂Q is a global integral n-cycle extending T off C, with M(B)≤2a. The cap on C is not asserted to be the distributional trace of the zero extension. This is precisely how the missing trace is avoided.

If the closure in X of the support of T is compact, all T_ε, their doubled fillings and folded Q_ε can be kept in one fixed compact ball about c_0∈C. Then ordinary compact-support AK compactness applies and Q, B are compactly supported. This version has genuine tightness. The general version uses local compactness and explicitly allows mass loss at infinity.

## 6. Canonical double and the exact filling-volume identity

Choose any global integral cycle extension B of T, supplied by Section 5. Define

    ΔT=i_+#B−i_-#B.

This is independent of the choice of B. If B' is another extension, B−B' is supported on C; its two inclusions give identical currents. Likewise M(ΔT)=2a. Compact support is available when the support closure of T is compact.

For any globally integral admissible Q in the definition of V_rel(T), ∂Q is another cycle extension. Therefore

    ∂(i_+#Q−i_-#Q)=ΔT,
    M(i_+#Q−i_-#Q)=2||Q||(U).

Taking infima gives V_D(ΔT)≤2V_rel(T). Conversely, take an absolute minimizing integral S with ∂S=ΔT, available from Section 3. The two folds have boundaries ±(B−P_C#B), whose restrictions to U are ±T. Their selected relative mass is at most M(S)/2. Thus

    V_rel(T)=½V_D(ΔT),
    V_rel(T)≤K_n a^q,

and the relative infimum is attained by a global integral representative. The selection of a fold suffices; an integral symmetric minimizer is not assumed in advance. At the infimum equality, the two fold costs each equal V_D/2 and the intervening inequalities saturate. For a globally integral original T with ∂T supported on C, use B=T−P_C#T, which is a cycle and satisfies P_C#B=0; the relative minimizer then has exact boundary T−P_C#T.

For fixed support in a ball about C, the identity also holds with compactly supported admissible fillings. This proves all compatibility steps, including multiplicity, orientations, support, trace and normality, before discussing any prospective equality or stability result.

## 7. Sharpness and geometric equality interface

Take X=R^(n+1), C={x_(n+1)≤0}, and T the oriented curved boundary of the Euclidean upper half-ball of radius r. Then a=s_n r^n/2. The upper half-ball current has exterior mass ω_(n+1)r^(n+1)/2=K_n a^q.

It minimizes exterior mass: on the connected upper half-space the difference between any competitor and the half-ball current is a top-dimensional locally integral cycle, hence a constant integer multiple of the oriented upper half-space. Finite mass forces that constant to be zero. This is the classical constancy operation; no arbitrary current is being replaced by a set. Alternatively, reflect into Euclidean space and use the ball's elementary top-dimensional constancy lower bound. This proves optimality of the coefficient.

The exact identity transfers equality of relative filling mass to equality for ΔT in the double, with no loss. But an all-dimensional absolute current equality theorem is the exact full-scope old r58 target. We do not renominate it, use its disposition as a premise, or claim its complete proof as a new operation. The following metric observation describes the remaining transfer if that absolute theorem is supplied separately.

Suppose an equality double is the oriented boundary of an isometrically embedded closed Euclidean (n+1)-ball B in D, with B the closed convex hull of its boundary. Reflection of D swaps the copies and sends ΔT to −ΔT; hence it preserves B and acts on it by an orthogonal involution fixing its center. Its fixed set is B∩C. Both open-copy pieces are nonempty. Since B\C is separated into those two pieces, the fixed linear subspace has codimension one: the complement of a linear subspace of codimension at least two in a ball is connected. Thus B cuts into two metric half-balls. Projection onto C of a point of either half-ball is its equatorial perpendicular foot. Indeed the distance from x to its reflected point equals twice d_X(x,C), while in the Euclidean ball it equals twice the height; the equatorial foot realizes that minimum and projection is unique.

Conversely, an isometric half-ball H in X together with its equatorial disk E⊂C yields an isometric doubled full ball if P_C on H is the Euclidean perpendicular projection onto E. For x,y in opposite copies with heights h,k and feet p,q∈E, the CAT(0) projection Pythagorean inequality gives, for c∈C,

    d(x,c)+d(y,c)≥sqrt(h²+d(p,c)²)+sqrt(k²+d(q,c)²)
                ≥sqrt((h+k)²+d(p,q)²).

The last inequality is the Euclidean triangle inequality combined with d(p,q)≤d(p,c)+d(c,q). Choosing c on the equatorial segment [p,q] in the height ratio gives equality, including a zero-height endpoint by a limit. Within copies distances are already Euclidean. Thus the doubled ball embeds isometrically. Its convex projection followed by Euclidean constancy proves it is an absolute mass minimizer.

The projection condition is material: a half-ball merely intersecting C in its equator does not by itself rule out shorter cross-copy paths through other points of C. No unrestricted geometric classification is asserted here without the absolute equality input. No statement about global ambient flatness follows.

## 8. What this integration pays for

The doubling operation is classical. BH supplies gluing and convex projection with proofs. Stadler Appendix A.2 explicitly doubles a CAT(0) space along a flat and constructs relative minimizers by symmetry, carefully treating a possibly non-normal trace. Krummel Sections 3–4 recover global cycles by projecting caps on convex parallel sets and prove the sharp half-space bound by reflection, with arbitrary integral multiplicity; Section 13 treats convex-exterior approximation and unbounded obstacles. AK supplies the compactness, slicing and closure operations. Wenger supplies round-cycle decomposition and coarse repairs in metric spaces. The companion supplies the sharp all-dimensional bound, confinement and absolute minimization machinery.

The folds above combine these compatible ingredients while avoiding a half-integral averaging error and treating thick seams through the correct exterior objective. The finite-mass extension records the necessary exhaustion rather than assuming compactness. These are durable complete deductions; they do not isolate a separate substantial operation after the strongest comparison. In particular, neither an initially failed seam argument nor the lack of a globally normal original trace is retained as favorable evidence of novelty.
