# Author proof of the frozen r182 phase-lifting theorem

This is an author-proof submission for the unchanged statement in FROZEN-THEOREM.md, SHA256 62b6ad633a662a491be617e82f8eb441be8f02069a7dc5289c10996dc8d9bee8. It is not an independent review or a correctness/contribution grade. The only upstream theorem used to obtain linearity is Source322 at the stipulated pin. The additional argument first recovers an ordinary sphere isometry from the phase data. Classical covering theory and planar monotonicity are credited and proved at the needed interfaces below.

Throughout, S_E={x∈E:||x||=1}; topology is the norm topology. Every scalar and linear space is REAL. In §§1–5, E need only be normed; completeness is used when applying Source322 in §6.

## 1. The projective metric really is supplied by the hypothesis

First f is odd and bijective. Fix x∈S_X. Surjectivity supplies y with f(y)=-f(x). Applying the unordered-pair identity gives

    {||x+y||,||x-y||}={0,2}.

Thus y=x or y=-x. The former would say f(x)=-f(x), impossible for a unit vector. Therefore y=-x and f(-x)=-f(x). If f(x)=f(y), the same identity implies y=±x, and oddness excludes y=-x. This proves injectivity. This elementary operation is already Tan–Gao Lemma2.

Let P_E=S_E/(x∼-x), with q_E the quotient map. Write [x]=q_E(x). Define

    d_E([x],[y])=min{||x-y||,||x+y||}.                         (1)

This is independent of representatives, symmetric, and zero exactly on equal classes. For the triangle inequality, choose signs s,t∈{±1} attaining d_E([x],[y])=||x-sy|| and d_E([y],[z])=||y-tz||. Then

    d_E([x],[z]) ≤ ||x-stz||
                 ≤ ||x-sy||+||sy-stz||
                 = d_E([x],[y])+d_E([y],[z]).                 (2)

Thus (1) is a metric. For any x∈S_E and 0<r<1, with balls taken in the sphere or in P_E as appropriate,

    q_E^-1(B([x],r))=B(x,r) ∪ B(-x,r).                       (3)

The two balls are disjoint, since a point in both would give 2=||x-(-x)||<2r. Every antipodal class in the left side has exactly one representative in each ball, so q_E restricts bijectively from either ball onto B([x],r). The map q_E is continuous, since d_E([u],[v])≤||u-v||, and open: for an open sphere set V, any ball B(v,r)⊂V projects onto B([v],r). Consequently these restrictions are homeomorphisms. The metric topology is the quotient topology, and q_E is a two-sheeted covering map. This checks the actual hypotheses of the covering-space operation, rather than treating an arbitrary metric quotient as a covering.

Oddness makes

    Fbar:P_X→P_Y,   Fbar([x])=[f(x)]                          (4)

well-defined. Bijectivity of f makes Fbar bijective, and the given unordered identity implies preservation of (1). Hence Fbar is a homeomorphism, indeed an isometry of the projective metrics. Nothing in this paragraph asserts continuity of f.

## 2. Topological ingredients for arbitrary normed spheres

For dim E≥2, S_E is path connected. Nonantipodal unit vectors are joined by the normalized straight segment; antipodal vectors can be joined by two such paths through an independent unit vector.

It is locally path connected. At x∈S_E choose a bounded real functional φ with φ(x)=1; a norm-one supporting functional suffices. On the open hemisphere H={u∈S_E:φ(u)>0}, the map

    u ↦ u/φ(u)

is a homeomorphism onto the affine hyperplane {v∈E:φ(v)=1}, with inverse v↦v/||v||. The hyperplane has arbitrarily small convex neighborhoods. Transporting these neighborhoods gives local path connectedness at x. This uses neither separability nor completeness.

If dim E≥3, S_E is simply connected. Here are the finite-dimensional details needed also for nonseparable E. Let γ:[0,1]→S_E be a loop. By uniform continuity choose a finite partition so that every point γ(t) and both endpoint values on its partition interval differ in norm by less than1/8. Let p(t) be the polygonal interpolation of these endpoint values. Then ||p(t)-γ(t)||<1/8, so ||p(t)||>7/8 and

    β(t)=p(t)/||p(t)||,   ||β(t)-γ(t)||<1/4.                  (5)

Normalized interpolation between γ and β is a homotopy of loops; it never reaches zero because the endpoints in (5) are not antipodal. It fixes their common basepoint at this stage.

The normalized polygon β lies in the union of finitely many spaces E_i spanned by adjacent vertex pairs, each of dimension at most2. Choose a finite-dimensional subspace W⊂E containing all vertices and of dimension at least3. A finite union of proper linear subspaces cannot cover W over the infinite field R. For completeness, choose for each E_i a nonzero linear functional on W vanishing on E_i. The product of these finitely many nonzero linear polynomials is not the zero polynomial; some vector avoids all its zero sets. Normalizing such a vector gives z∈S_W outside every E_i.

Now

    H(t,s)=((1-s)β(t)+sz)/||(1-s)β(t)+sz||,  0≤s≤1,         (6)

is well-defined. A zero denominator with 0<s<1 would imply z is a scalar multiple of β(t), putting z in one of the E_i. Formula (6) contracts the polygon to z. It is a homotopy of loops, with a possibly moving basepoint; together with (5) it gives a disk filling of γ, which is equivalent to triviality of its based loop class. Thus π1(S_E)=0. Only one compact loop and a finite set of vectors were used, not compactness or separability of S_E.

We use the following precise classical covering facts. A path in the base of a covering has a unique lift after the initial value is chosen. Homotopies of paths lift with their fixed endpoints; and a map from a path-connected locally path-connected simply connected space lifts after choosing one initial value. These are the actual mechanisms of Hatcher Theorem1.7 and Propositions1.30–1.34. To recall why they work: subdivide a path into finitely many pieces lying in evenly covered neighborhoods and follow the determined sheet on each piece. For a homotopy, finite local rectangles give compatible lifts; uniqueness on overlaps makes them agree. To lift a map h:Z→B from simply connected Z, choose a path from z0 to z and define the lift value by the endpoint of the lifted h-path. Two choices differ by a nullhomotopic loop, so homotopy lifting makes the endpoint independent. In a small path-connected neighborhood mapped into one evenly covered set, the resulting map is the composition of h with the inverse of one sheet map, hence is continuous. Two lifts agreeing at one point agree on a connected domain because their agreement set and its complement are open.

A connected two-sheeted covering q:S_E→P_E for dim E≥2 has no continuous section. If s were a section, then s(P_E) and -s(P_E) would be disjoint nonempty subsets covering S_E. Each is open: near any b∈P_E choose an evenly covered neighborhood and shrink it so the continuous s lies in one sheet. There s is the inverse of that sheet's projection and its image is open. This contradicts connectedness of S_E.

## 3. Construct one global continuous odd lift

We establish that EVERY homeomorphism Fbar:P_X→P_Y arising in (4) has an odd homeomorphic lift U:S_X→S_Y. Here the topology alone does the work; preservation of both chord norms will be used only in §5.

If either sphere has two points, bijectivity of f forces both to have two points, so both spaces have dimension1. An odd bijection U=f is already an isometry of these two-point spheres. Hence assume both dimensions are at least2.

Suppose first that dim X≥3. By §2 and the covering lifting fact, the map Fbar q_X:S_X→P_Y lifts to a continuous U:S_X→S_Y with

    q_Y U=Fbar q_X.                                          (7)

At every x, (7) implies U(-x)∈{U(x),-U(x)}. The choice of sign is locally constant: the continuous function ||U(-x)-U(x)|| has values in{0,2}. Connectedness of S_X makes the choice constant everywhere. If it were always the plus sign, U would factor through q_X as a continuous map h:P_X→S_Y. Then h Fbar^-1 would be a section of q_Y, which §2 excludes. Therefore

    U(-x)=-U(x)   for every x∈S_X.                            (8)

The homeomorphism Fbar on the quotient and (8) imply U is bijective. Indeed, any y has a preimage orbit; if one representative maps to -y, its negative maps to y. If U(x)=U(x'), quotient injectivity gives x'=±x, and (8) excludes the negative case.

The lift is a local homeomorphism: shrink an evenly covered neighborhood for q_X so that U lies in a single sheet of an evenly covered neighborhood for q_Y. On this neighborhood (7) expresses U as

    (q_Y restricted to that sheet)^-1 ◦ Fbar ◦ q_X.

These maps are homeomorphisms onto open subsets, after the stated shrinking. Thus the bijection U has continuous inverse and is a homeomorphism.

If dim X=2 but dim Y≥3, apply the preceding argument to Fbar^-1:P_Y→P_X. Invert its odd homeomorphic lift to obtain the required U. No prior equality of the dimensions was assumed.

It remains to handle dim X=dim Y=2. Choose a basis in each plane and put

    e_E(θ)=(cosθ a_E+sinθ b_E)/||cosθ a_E+sinθ b_E||.

This parametrizes S_E by R/2πZ, is a homeomorphism of circles, and satisfies e_E(θ+π)=-e_E(θ). The induced parametrization of P_E is R/πZ. In these parametrizations Fbar is a homeomorphism of R/πZ. The map R→R/πZ obtained by composing the quotient with Fbar has a continuous lift h:R→R by the path-lifting fact, since R is simply connected. Because the composition is a local homeomorphism, h is locally a homeomorphism and therefore locally strictly monotone. Its local orientation cannot change on connected R, so h is globally strictly increasing or globally strictly decreasing.

The difference h(θ+π)-h(θ) is a continuous integer multiple ofπ, hence equals kπ for a single integer k. Monotonicity makes k nonzero. If |k|≥2, the intermediate value theorem gives θ∈(0,π) with h(θ)=h(0)+π or h(0)-π, contradicting injectivity of Fbar moduloπ. Hence k=±1. In particular

    h(θ+2π)=h(θ)+2kπ.

Consequently

    U(e_X(θ))=e_Y(h(θ))                                      (9)

is well-defined, continuous, odd and bijective. Monotonicity and the period relation give a continuous inverse; equivalently it is a continuous bijection of compact circles. This proves the remaining case.

In every dimension U(x) belongs to {f(x),-f(x)} by (7). Thus there is a function σ:S_X→{±1} with

    U(x)=σ(x)f(x),                                           (10)

and σ is even because both f and U are odd. Neither f nor σ was required to be continuous. Multiplying U globally by -1 allows us to impose U(x_*)=f(x_*) at any chosen x_*.

Pointwise signs preserve the unordered-pair identity: multiplying either argument by -1 merely exchanges sum and difference norms. Therefore U is a continuous, odd, surjective PHASE-isometry. It remains to prove it is an ordinary isometry. A general assertion that local sphere isometries are global is NOT used.

## 4. The exact planar monotonicity needed for orientation

Let a,c be linearly independent unit vectors in a real normed plane, and let b be a unit vector whose ray lies between their rays in their positive cone. Then

    ||a-b||≤||a-c||.                                         (11)

Here is the elementary proof, the unit-radius case of Martini–Swanepoel–Weiss Proposition31. The ray of b intersects the segment[a,c] at some p. Since p is a convex combination of unit vectors, ||p||≤1, hence p lies on[0,b]. Using collinearity on these two segments and then two triangle inequalities,

    1+||a-c||
      = ||b-p||+||p||+||a-p||+||p-c||
      ≥ ||b-a||+||c||
      = ||b-a||+1.

This proves (11), including the case ||p||=1 when the unit sphere has a flat face. Endpoints b=a,c are immediate. This argument uses only norms and convexity.

If b is in the open cone between a and c, then c is in the cone between -a and b: writing b=αa+βc with α,β>0 gives c=(1/β)b+(α/β)(-a). Applying (11) with base point -a and endpoint b gives

    ||a+c||≤||a+b||.                                         (12)

Again endpoint cases are immediate, with ||a+a||=2. Thus, for the normalized segment

    z_t=((1-t)a+tc)/||(1-t)a+tc||,  0≤t≤1,

we have simultaneously

    ||a-z_t||≤||a-c||,    ||a+z_t||≥||a+c||.                 (13)

No strict convexity, differentiability or strict monotonicity is claimed. Restricting an arbitrary normed space to span{a,c} makes (13) available there without any dimension restriction on the ambient space.

## 5. Transport orientation without crossing a branch collision

Fix x,y∈S_X with

    A=||x-y|| < B=||x+y||.                                  (14)

If y=x, ordinary distance preservation is immediate. The case y=-x cannot satisfy (14). Otherwise x,y are independent, and define z_t by the normalized segment in §4, with a=x,c=y. Put

    a(t)=||x-z_t||,  b(t)=||x+z_t||,
    h(t)=||U(x)-U(z_t)||.

All three functions are continuous. By (13),

    a(t)≤A<B≤b(t)   for every t∈[0,1].                       (15)

Since U is a phase-isometry, h(t) is either a(t) or b(t). The function

    r(t)=(h(t)-a(t))/(b(t)-a(t))

is therefore a continuous function[0,1]→{0,1}; (15) ensures its denominator is positive everywhere. At t=0, z_0=x, so h(0)=a(0)=0 and r(0)=0. Connectedness of[0,1] gives r(t)=0 for all t. In particular,

    ||U(x)-U(y)||=||x-y||                                    (16)

whenever (14) holds.

If ||x-y||>||x+y||, apply the preceding argument to x and -y. Oddness of U yields

    ||U(x)+U(y)||=||x+y||.

The unordered-pair identity then forces the other target norm to equal the other, distinct, source norm, giving (16) again. If ||x-y||=||x+y||, both elements of the unordered pair are the same number, so (16) follows directly. The cases y=±x are also immediate from (8). Therefore U is an ordinary surjective sphere isometry on its ENTIRE domain.

This proves the added interface: global continuous antipodal lifting followed by branch orientation along a path on which the two permitted chord values stay strictly separated. The strict separation comes from the endpoint pair, even on a nonsmooth or non-strictly-convex sphere. No face connectivity or triple-face intersection assumption has been imported from the C(K)/C0 primary arguments.

## 6. Apply the full stipulated source and prove the exact conclusion

Now X,Y are the nonzero real Banach spaces of the frozen statement. By §5 the map U satisfies all hypotheses of Source322 Theorem thm:main. Hence

    T(0)=0,
    T(v)=||v|| U(v/||v||)   (v≠0)                            (17)

is a surjective real-linear isometry. In the operative source proof, this is exactly the map whose cross-radius defect D_q is forced to vanish by maximal-defect attainment, common-support convex propagation, Darbo alignment and the extremal-chord contradiction. The ordinary isometry produced in §5 supplies the exact endpoint equalities required by those operations. This is why no signed return-map or continuity selection in an enlarged ultrapower is needed. The source is applied at its full all-Banach scope, not to a finite-dimensional or separable reduction of X,Y.

From (10) and σ²=1, setting ε=σ gives

    f(x)=ε(x)T(x),    ε(-x)=ε(x),    x∈S_X.                  (18)

We chose U(x_*)=f(x_*), so T(x_*)=f(x_*) and ε(x_*)=1.

For uniqueness, let (T1,ε1),(T2,ε2) be two such pairs. For every x∈S_X,

    T2(x)=ε2(x)ε1(x)T1(x).

The continuous function x↦||T2(x)-T1(x)|| takes only the values0,2. If dimX≥2, connectedness of S_X forces it to be constant; thus T2=T1 on the whole sphere or T2=-T1 on the whole sphere. Real linearity extends that equality to X, and (18) then forces ε2=ε1 or ε2=-ε1 respectively. For dimX=1, a linear map is determined by its value at one unit vector, and the same conclusion follows directly. The basepoint normalization rules out the negative choice. This proves both uniqueness statements at exactly the frozen scope.

Conversely, take any surjective real-linear isometry T:X→Y and any even function ε:S_X→{±1}. For each pair x,y, the product ε(x)ε(y) is either1 or-1, so the two target sum/difference norms are the two source norms, in the same or reverse order. Thus f=εT satisfies the unordered-pair identity. It is surjective: for y∈S_Y let x=T^-1(y). If ε(x)=1 then f(x)=y; if ε(x)=-1, then evenness gives f(-x)=(-1)(-y)=y. This proves the converse and finishes the proof of the unchanged frozen statement.

## 7. Boundaries of the submission

The proof gives no complex-linearity assertion, no min-only or max-only theorem, no approximate rate, no nonsurjective extension, and no parameter-family lift. These are outside the frozen statement. In particular (15) needs the FULL unordered pair after a continuous lift; a projective min-distance isometry alone does not supply h(t)∈{a(t),b(t)}. The source's radial extension is applied to U, not blindly to the original potentially discontinuous f.

The classical planar lemma, covering lifting and source radial/linear operation are paid ingredients. The proposed additional operation is the full arbitrary-space sign recovery linking them. Whether that completed operation is a substantial contribution or already known requires independent actual-literature review. This file assigns no grade, acceptance or count, and does not start formalization, manuscript or release work.
