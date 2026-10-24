# Author proof for the unchanged r216 target

This is an author-proof submission, not an independent correctness or contribution verdict. The exact frozen statement is `STATEMENT.md` (SHA256 75b55258f022d13db6995649a1ab7d7f29b80066721e560dd01cfb4ca9ddb6e3). No formalization or manuscript/release work is included. All Source340 proofs at the stipulated pin are accepted as true.

## 1. Interfaces and the additional operation

Use the stable smooth tube space T, its rigid map i:BO→T and its negative-domain map γ:T→BG in Source340, `thm:tube-fibration`. These are the same stable models compared in Álvarez-Gavela–Igusa–Sullivan, arXiv:2603.28007v2 (AIS), §3.6. Stabilization by a fixed hyperbolic plane means adding one positive and one negative square. A fixed permutation or positive change of scale of these coordinates does not affect the resulting stable class. We use stable *homotopy classes*, not their real higher-torsion images.

The additional primary interface is AIS Proposition 4.4, Definitions 4.5 and 4.7, and its proof in §4.2: for an embedded nearby Lagrangian with trivial stable Gauss map, doubling a local generating function and separating its chord-free Legendrian copies determines a natural coset of the rigid action

[Q,BO] → [Q,T].

This coset is invariant under Hamiltonian isotopy of the unmarked embedded Lagrangian. Changing the chosen Gauss nullhomotopy changes the representative by the rigid action. A global generating family supplies such local data and a Gauss nullhomotopy; see AIS §2.4 and §4.2. This latter section was checked after the target was frozen; the target was not changed. These are primary interfaces, not a claim that every generating family is already natural.

For the doubling operation and its partition-function model, use Abouzaid–Courte–Guillermou–Kragh, arXiv:2011.13178v3 (ACGK), Definitions 3.1, 3.23–3.24, Lemma 3.11, Theorems 3.13 and 3.26, and the actual proofs in §3. The model is f(q,t,w)=t+G(q,w)+ε(q,t,w), where ε has compact vertical support. The regular sublevel at zero after separating the copies represents the natural partition tube. The stable partition/domain equivalence in AIS §3.6 identifies its stable class with a class in T.

The new comparison below is explicit: for a generating family exactly homogeneous outside one common ball, its separated-double partition has the same stable tube class as its given homogeneous infinity data. Merely quoting persistence of generating families would not prove that comparison. The proof pays its transition-region and infinity compatibility.

## 2. Uniform doubling of a homogeneous-at-infinity generating family

Let Q be compact. Suppose F:Q×R^n→R is smooth, zero is a regular value of its full vertical-gradient equation, and its generating map is a diffeomorphism from Crit(F) onto a closed exact embedded L⊂T*Q. Suppose F(q,w)=g_q(w) for |w|≥R_0, where g is degree two homogeneous, smooth off zero, C^1 at zero, has smooth angular dependence on q, and

|∇_w g_q(w)|≥c|w|,  c>0.

Its angular functions lie in a fixed tube component. All constants below can be chosen uniformly over Q and over additional compact parameter sets when the stated bounds are uniform. The application will have q=(b,v), g_q=g_b.

Use exactly the one-dimensional birth of ACGK §3.2. Choose its odd smooth D_0 with D_0(t)=t³−3t for |t|≤1, D_0'(t)>0 for |t|>1, and D_0(t)=t for |t|≥2. Put

d_τ(t)=t+(1/4+τ)(D_0(t)−t),   0<τ≤1/12.

On the central interval this is (1/4+τ)t³−4τt. It has precisely two nondegenerate critical points, with opposite nonzero critical values ±s(τ), and outside that interval its derivative is positive. Fix a sufficiently small τ_0>0 as in the actual ACGK local doubling, and put s_0=s(τ_0). For s≥s_0 set

d_s(t)=(s/s_0)d_{τ_0}(t/(s/s_0)),  E_s=d_s−t.

This is a smooth path with exactly two nondegenerate critical points and critical values ±s. On a compact s-interval both the support and the supremum of E_s are bounded. Let α_A(w)=α(|w|/A), where α is smooth, nonincreasing, 1 on [0,1] and 0 on [2,∞). Write C_α=sup|α'|. Define

H_s(q,t,w)=F(q,w)+t+α_A(w)E_s(t).                 (2.1)

Fix 0<s_0≤s≤S. Choose A>R_0 beyond the entire vertical critical locus, and so large that

cA²>C_α max_{s∈[s_0,S]}||E_s||∞.                (2.2)

On A≤|w|≤2A the w-gradient of (2.1) has norm at least cA−C_α||E_s||∞/A>0. For |w|≥2A its t-derivative is 1. For |w|≤A it is F+d_s. Consequently its vertical critical locus is exactly

Crit(F)×Crit(d_s).

The full defining differential is the regular F-gradient block together with the nonzero d_s'' block. Its generated covectors are those of L and its critical values are the original primitive values shifted by ±s. These are precisely the two Legendrian lifts of L shifted in the contact coordinate. Since L is embedded in the cotangent bundle, distinct points cannot coincide after forgetting the contact coordinate; the two copies are disjoint for every s>0. Thus they give a genuine Legendrian isotopy, not an immersed one. The trace for s∈[s_0,S] is compact, so the contact isotopy extension can be chosen compactly supported near that trace, as in ACGK's separation argument.

At a sufficiently small s_0, (2.1) is the local-germ doubling construction of ACGK §3.2, using the actual global F as the extension of its germ and a cutoff constant near its critical locus. The family (2.1) is a concrete lift of the entire separation isotopy. For S>max|F| on Crit(F), zero is a regular value in every vertical fiber. Its regular partition sublevel represents a representative of the natural coset associated with this chosen germ. The natural-coset interface is used here at the level of stable tube classes, not merely cohomology.

### Removing the compact part of F

Choose a smooth radial function ρ_ε(r), zero near r=0, positive and nondecreasing after its zero plateau, and 1 for r≥ε. Define

G_{q,ε}(w)=ρ_ε(|w|)g_q(w).

This is smooth, equals g outside ε, and all its critical values are zero. Indeed for ρ>0 a nonzero angular gradient prevents a critical point; if the angular gradient is zero, regularity of the angular zero level implies h≠0, and the radial derivative (2rρ+r²ρ')h is nonzero. Points with ρ=0 have value zero. Uniformly, G_ε−g=O(ε²) and ∇(G_ε−g)=O(ε) on its support, by homogeneity.

Set F_u=(1−u)F+uG_ε. All F_u equal g outside one fixed ball. Their critical loci therefore lie in that ball; their possible critical values are bounded in absolute value by a finite M, uniformly in (q,u). Since |G_ε| is uniformly bounded for 0<ε≤ε_0 on this ball, M can also be chosen uniformly in that interval; the later choice of a smaller ε does not invalidate S or A. Take S>M, and take the common A still larger if needed. The same annular estimate proves that the only vertical critical points of H_{S,u} are critical points of F_u paired with the two critical points of d_S. Their values F_u±S never vanish. Thus H_{S,u}=0 is fiberwise regular throughout, whether or not F_u is Morse. This is a homotopy of regular partition tubes, not a proposed isotopy of the intermediate Lagrangians.

At u=1 all critical values of G_ε are zero, so we can reduce s back to s_0, retaining regularity of the zero level. We can then vary τ from τ_0 to τ_*=1/12 through the actual functions d_τ: their two critical values remain nonzero and opposite throughout. Choose A uniformly over both compact parameter intervals. The resulting partition is that of

G_{q,ε}(w)+t+α_A(w)(d_{τ_*}(t)−t).              (2.3a)

Multiplying the function by 3 preserves its signed zero domain. In the homogeneous limit, the positive coordinate change w=z/√3 gives 3g_q(w)=g_q(z). Define D=3d_{τ_*}. Then D=t³−t on |t|≤1, D'>0 for |t|>1, D=3t for |t|≥2, and D'≥−1 everywhere. Renaming z as w and enlarging the radial cutoff radius accordingly, (2.3a) becomes the partition of

g_q(w)+3t+α_A(w)(D(t)−3t).                     (2.3)

For the smooth extension G_ε the same coordinate change changes only the cutoff radius ε; the small-origin argument below justifies taking this homogeneous limit. This normalization is an exact positive scaling of the ACGK birth, not an assumption about arbitrary one-dimensional doubling choices.

These operations use a single global function at every stage. There are no independently chosen local primitives or overlap constants.

## 3. Comparison of the partition with the original homogeneous tube

Here is the decisive comparison. Temporarily use the C^1 homogeneous g in place of G_ε, and put r=|w|. Choose a smooth nonnegative nondecreasing a(r), zero near zero, equal to r² for all sufficiently large r, and at least 2 wherever α_A(r)=0. Such a choice is possible after making A>2; a can start increasing inside the plateau of α_A. For u∈[0,1] put

B_u(r)=(1−u)α_A(r)+u,
C_u(r)=3−4B_u(r)+u a(r),
P_u(q,w,t)=g_q(w)+B_u(r)D(t)+(3(1−B_u(r))+u a(r))t.    (3.1)

At u=0 this is (2.3) with g instead of G_ε. At u=1 it is g+D(t)+a(r)t.

### No zero-level critical points in any transition region

If |t|>1, D'(t)>0 and 3(1−B_u)+u a≥0, so ∂_tP_u>0; if B_u=0 the latter derivative is positive directly. It remains to consider B=B_u>0 and |t|≤1, where

P=g+Bt³+Ct,   ∂_tP=3Bt²+C.

At w=0, B=1 and a=0, so P=D(t). Its zeros 0,±1 are regular. Suppose w≠0 and a zero-level critical point exists. If t=0, the w-equation would be ∇g=0, impossible. Therefore t≠0, C<0, and t²=−C/(3B). Euler's identity w·∇g=2g, combined with P=0 and w·∇_wP=0, gives

rC'−rB'C/(3B)−4C/3=0.                          (3.2)

On the other hand,

B'≤0,   C'=−4B'+u a'≥−4B',   C/B≥−4.

Hence

rC'−rB'C/(3B)−4C/3
 ≥ −(8/3)rB'−4C/3 >0,

contradicting (3.2). This proves regularity throughout (3.1), without assuming radial monotonicity of g, injectivity of ∇g, or nondegeneracy of its fiber Hessian.

Next change D to t³−t by convex interpolation. On |t|≤1 it is unchanged, and outside that interval both derivatives are positive. For g+D(t)+a(r)t the same argument applies. Then change a to r² by convex interpolation of these nonnegative nondecreasing functions. At a potential critical point with t≠0 the corresponding expression is

ra'(r)−4(a(r)−1)/3>0,

because the t-equation requires a(r)<1. All zero levels remain regular. The endpoint is

P_*(q,w,t)=g_q(w)+t(|w|²+t²−1).                 (3.3)

### Recovering smoothness at w=0

The homogeneous family need only be C^1 at w=0. This does not hide a smooth gluing assumption. In a fixed small neighborhood of w=0, all the homotopies just used have their zero levels near t∈{−1,0,1}; there the absolute t-derivative is bounded below, uniformly over q and all homotopy parameters. Choose ε small enough that replacing g by G_ε cannot leave these neighborhoods or destroy that lower bound. Outside |w|<ε, Euler's calculation is unchanged. Thus the entire argument can be carried out with smooth functions G_ε, with regular zero levels. At the endpoint, returning from G_ε to g is a C^1-small regular homotopy supported in a bounded part of the stereographic zero set. Smooth angular approximation gives the same tube class, by the relative C^1/smooth comparison already proved in Source340's tube section. No smoothness of g at the origin has been assumed.

### Uniform control at infinity, rather than a nonproper isotopy

For r sufficiently large, α_A=0 and a=r². During (3.1),

∂_tP_u = uD'(t)+3(1−u)+u r² ≥3+u(r²−4) ≥1.

The function tends to ±∞ with t, so there is one zero t=k(q,u,w) on this exterior. It is smooth jointly in its variables by the implicit function theorem. During the later two homotopies the same conclusion holds, with ∂_t bounded below by r²−1 on this exterior. All parameters range over compact sets.

Choose R large enough for these assertions, and χ(r) equal to 0 for r≤R and 1 for r≥2R. Translate the exterior graph by using t=t'+χ(r)k(q,u,w). This is a fiber diffeomorphism: w is unchanged and the derivative in t' is 1. The resulting zero hypersurface is t'=0 for r≥2R. On r≤2R all its zero heights are uniformly bounded: g and a are bounded there, and D or the cubic have the sign of t and grow uniformly outside a large t-interval. Thus these normalized zero hypersurfaces form a smooth compactly supported family of partitions. Their coorientations are retained. A compact family of regular cooriented hypersurfaces has compatible defining functions, using normal collars and convex interpolation among defining functions of the same signed domain, precisely the domain/function comparison in Source340.

At u=0 this normalization is particularly transparent. On the exterior k=−g/3; choose the cutoff χ to start beyond supp α_A. Then (2.3) becomes

3t'+(1−χ(r))g_q(w)+α_A(w)(D(t')−3t'),

which, after division by 3, is exactly the permitted flattening of the g-term outside the perturbation support used in ACGK Proposition 3.25. Consequently the initial normalized partition represents the original ACGK class; an unbounded coordinate change has not silently changed that class.

At the final endpoint (3.3), |k| is bounded on the exterior, since the t-derivative is ≥r²−1 while |g|≤Cr². Differentiating its equation gives ∂_wk=O(r^−1), uniformly in the angular and q parameters. These estimates will identify its compactification with the usual spherical tube. We do not assert that the entire unbounded ambient coordinate translation extends smoothly to the point at infinity; only the normalized cooriented hypersurface and its local graph are used.

### Exact stereographic identification

On R^n_w⊕R_a⊕R_b consider the homogeneous regular function

G(q,w,a,b)=g_q(w)+2ab.

It is the direct sum of g and a fixed form of signature (1,1). Its full gradient has no zero off the origin. On the unit sphere S^{n+1}, the fixed point e=(0,1,0) is a regular zero, with a fixed positive b-normal. Stereographic projection from e has coordinates

w_s=2w/(1+ρ²),   b_s=2t/(1+ρ²),
a_s=(ρ²−1)/(1+ρ²),   ρ²=|w|²+t².

Homogeneity gives the exact identity

G(q,w_s,a_s,b_s)
 =4(1+ρ²)^−2 [g_q(w)+t(ρ²−1)].                 (3.4)

The multiplier is positive, so both the domain and its coorientation agree with (3.3).

To relate graph normalization to the standard partition chart, work near e on the sphere. The equation is a graph b=φ_q(w_s), because the b-derivative at e is nonzero. Uniformly φ=O(|w_s|²) and dφ=O(|w_s|), as follows either from the equation g(w_s)+2ab=0 with a close to 1, or from the exterior estimates above. Suppress φ in a sufficiently small cap by a radial cutoff in w_s. The interpolating graphs remain regular and are C^1-small changes of the original graph, uniformly in q. Away from e they are smooth; a relative angular smoothing at e preserves the gradient margin. This makes the tube standard in a fixed cap at e. In the stereographic chart it is the standard halfspace at infinity. Both this cap normalization and the exterior graph normalization above preserve the sign and interpolate through graphs on their common exterior collar; interpolation of the graph heights compares them, relative to a smaller interior region. Thus they represent the same partition-tube class. This supplies the infinity compatibility, rather than treating a pointwise chart formula as a compactly supported isotopy.

Equation (3.4) therefore identifies the partition class of (2.3) with the stable class of g⊕2ab, which is exactly the stable class of g. This concludes the additional comparison.

## 4. Consequence for the natural coset

Combining §§2–3, for the uniform homogeneous-at-infinity Morse families used here the natural coset of their embedded image is

[g:Q→T] + i_*[Q,BO].                            (4.1)

The statement is at the stable homotopy level. It is not obtained by passing to real cohomology, which would lose the finite-order classes needed below. Its derivation used the precise infinity condition above; it did not assert a closed exact Lagrangian h-principle or a uniqueness theorem for arbitrary unrestricted generating-family notions.

The partition construction in §§2–3 is over the given compact Q. If stabilizations are required to enter the conventional partition tube space, choose one fixed stabilization for the compact homotopies. AIS §3.6 compares the partition and homogeneous domain models only stably; no finite-stage equivalence has been assumed. The explicit endpoint (3.4) adds a fixed hyperbolic plane. Any additional fixed stabilizations disappear in T. No parameter-dependent rigid stabilization is introduced in the analytic comparison. Such stabilizations are allowed only in the natural-coset ambiguity in (4.1).

If a Hamiltonian isotopy carries L to L', AIS Proposition 4.4 gives equality of the cosets (4.1). This statement is about embedded images. It does not require preserving Crit(F), a parametrization of L, a primitive normalization, or a chosen Gauss nullhomotopy. Adding a constant to a primitive merely translates its Legendrian lift and does not change the natural coset.

## 5. Four classes, one cotangent bundle

Let A=π_9 H^s(*) and j:A→π_9T be the map in the paid tube long exact sequence. Source340's computation gives

A_(2)≅Z/8⊕(Z/2)^2,
π_10BG=π_9^S≅(Z/2)^3.

The preceding boundary ∂:π_10BG→A has image of exponent at most 2. Choose an integral x∈A whose localization has generator coordinate in the displayed Z/8 summand. Such a choice exists: express a generator in A_(2) as y/s with s odd; then y has an odd generator coordinate, so take x=y. In A_(2) this x has order 8. Its image a=j(x) has localization of order 4 or 8, since 2x_(2) has order 4 and cannot belong to the localized boundary image, whose exponent is at most 2. In particular

0,a,2a,3a

are pairwise distinct integrally. No finite-generation assertion about unlocalized A, and no claim that the integral a has no odd-primary component, is needed. Exactness gives γ_*a=0 integrally. This strengthening of the source's elementary group argument is not itself the new geometric operation.

The source also proves that

(BJ)_*:π_9BO→π_9BG

is injective, and γ∘i≃BJ. It follows that

ker γ_* ∩ im i_* = {0} in π_9T.                (5.1)

Indeed if i_*e lies in ker γ_*, then (BJ)_*e=0, so e=0.

By compactness of the finite set of representatives and of their parameter spheres, choose one finite diagonal tube stage T_{m,m} representing a,2a,3a, with m≥20. Increase this common stage if needed. The paid localized-family lemma, applied to each class, supplies smooth angular families g_{j,b}, b∈S^9, all equal to the fixed quadratic form on common neighborhoods U_0 of both poles of a fixed height θ. This lemma's proof is a finite-stage representative/relative smoothing construction; its use does not require a minimal-stage estimate. No explicit value of m is claimed. Put N=2m and Q=S^9×S^{N−1}.

Choose common constants c>0, C and C_1 for the three families by taking minima/maxima over this finite set. Set δ_0=min_{S^9\U_0}|dθ|>0. Choose K with Kδ_0>C_1/c, then Λ with R(b)=Λe^{Kθ(b)} satisfying the source's lower bound for all three smooth extensions G_j, then a common cutoff radius T satisfying

T>max(1,R_max/c,D_βR_max/c).

The source proposition `prop:embedded-realization` gives, for j=1,2,3,

F_j(b,v,w)=G_{j,b}(w)−R(b)β(|w|/T)⟨v,w⟩.

All critical points lie in 1<|w|<T and solve ∇g_{j,b}(w)=R(b)v. Their parametrizations are

(b,u) ↦ (b, ∇g_{j,b}(u)/|∇g_{j,b}(u)|,
                  R(b)u/|∇g_{j,b}(u)|).

They are diffeomorphisms from S^9×S^{N−1} onto the respective critical loci. Regularity follows from v-perpendicular variations and the radial w variation. Equal sphere momenta imply w−w'=tv; outside U_0 the base momenta differ by at least R|t|(Kδ_0−C_1/c), while inside U_0 the quadratic critical equation is unique. Thus each generating map is an injective immersion and, by compactness, an embedding. These are the entire source separation operations, retained with common constants, not newly claimed operations.

The Liouville pullback is exactly d(F_j|Crit), globally. Euler's identity gives the explicit primitive

f_j(Γ_{F_j}(b,v,w))=−g_{j,b}(w).

It is well-defined and smooth because Γ_{F_j} is a diffeomorphism and critical points stay away from zero. Both cutoff transitions contain no critical point. Thus no end or overlap requires an extra primitive choice. Take L_0=Q_0 with primitive 0.

The infinity class of F_j over Q is pr_1^*(ja). By (4.1), the natural coset of L_j has this representative. For the zero section, the representative is 0, as supplied by the constant quadratic family and the same comparison (or directly by rigid doubling).

## 6. Every pair is separated without markings

Assume a compactly supported Hamiltonian isotopy takes L_j to L_k, with j≠k in {0,1,2,3}. By natural-coset invariance and (4.1), their classes differ by a rigid class over Q. Restrict to the fixed inclusion s:S^9→Q, b↦(b,v_0). Then

(j−k)a ∈ im(π_9BO→π_9T).                       (6.1)

Here free versus based classes does not create an extra orbit ambiguity. Stable T is a connected grouplike homotopy-commutative H-space under direct sum (the stable tube models of AIS §3.6); connected H-spaces have trivial π_1 action on higher homotopy groups. Equivalently one may use the stable infinite-loop tube model there. The chosen families are based by the fixed quadratic germ near a pole. Restricting the rigid action is addition by the class of the restricted stable real bundle. Thus equality of natural cosets gives exactly (6.1), not an equality only after reparametrizing the sphere.

But γ_*((j−k)a)=0, so (5.1) makes (j−k)a=0. This contradicts the order of the 2-localization of a, since 0<|j−k|≤3. This argument includes every pair of nonzero examples as well as every pair with L_0. It proves conclusion 4 of the frozen statement. The common construction in §5 proves conclusions 1–3.

Orientation of the parameter S^9 fixes the sign of the chosen generator; reversing it replaces a by −a and does not affect the pairwise argument. Fixed coordinate reorderings and split stabilizations do not affect stable classes. The natural coset absorbs changes in the Gauss nullhomotopy and the corresponding stable negative bundles. No Floer grading, spin choice, local coefficient system, or real regulator is used in the comparison. Compact support is exactly that in the frozen statement. No claim about general symplectic isotopy, smooth isotopy, or formal Lagrangian homotopy follows from this argument.

## 7. Scope of the author submission

The added operation is the uniform doubled-partition comparison in §§2–3, especially the Euler identity ruling out zero-level critical points and the controlled comparison at the stereographic pole. The source already pays realization, exactness, separation, Morse/cobordism obstruction, and Hamiltonian transport. Classical products or relabeling the same embedded image would not yield §6. AIS already pays the natural-coset invariant; this proof computes that invariant for the particular tame realization rather than introducing a new name for it.

The statement is an existence result at one common sufficiently large even N. It does not produce a least N, four examples in every dimension, an infinite family on one fixed base, or a claim that every possible tube generating family lies in a natural coset without the uniform hypotheses used here. No formal theorem is claimed: the exact pinned lean/docs/340.md endpoint returned 404, and no alternate formal endpoint was guessed. The parent must arrange independent adversarial correctness and substantial-contribution reviews; all grades, adoption, and counts remain with the parent.
