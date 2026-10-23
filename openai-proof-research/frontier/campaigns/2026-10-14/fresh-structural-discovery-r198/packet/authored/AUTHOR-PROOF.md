# R198 author proof: global sign recovery on Banach spheres

This is an author-proof nominee at the exact immutable scope in SCOPE.md. No independent correctness review, contribution grade, acceptance, or campaign increment is asserted. The sole stipulated upstream mathematical input is Source322 at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, Theorem `thm:main`; its entire operative proof is accepted. All arguments before section 7 below concern arbitrary real normed spaces and do not require completeness.

Write S_X={x: ||x||=1}. A phase-isometry in this note means a map preserving the unordered set of the two numbers ||x-y|| and ||x+y||, exactly as in (P) of SCOPE.md. Multiplicities when these numbers agree do not affect any argument.

## 1. The exact statement and the residual

For nonzero real Banach spaces X,Y, every surjective phase-isometry f:S_X -> S_Y has the form

    f(x)=sigma(x) Ux,

where U:X -> Y is a surjective real-linear isometry and sigma:S_X -> {1,-1} is even. The pair is unique up to (U,sigma) -> (-U,-sigma), and every such pair gives a surjective phase-isometry.

The residual proved here is the source-free assertion that f admits exactly two continuous odd bijective lifts h:S_X -> S_Y with h(x) in {f(x),-f(x)}, and that both are metric isometries. The proof constructs the lift in every dimension and verifies its global ordered-distance identity. It does not assume an unproved sign consistency or radial phase-preservation identity.

## 2. Antipodal pairs and their metric

First f is odd and bijective. For x in S_X, surjectivity supplies z with f(z)=-f(x). Property (P) gives {||x-z||,||x+z||}={0,2}, so z=x or z=-x. The former would give f(x)=-f(x), impossible for a unit vector over R. Thus z=-x and f(-x)=-f(x). If f(x)=f(z), the same zero-norm argument gives z=+/-x; oddness excludes z=-x. This proves injectivity. This elementary operation also appears in Tan--Gao, Lemma 2, whose proof was read.

Let P_X=S_X/{x~-x}, and let pi_X:S_X -> P_X be the projection. Define

    d_X([x],[z])=min{||x-z||,||x+z||}.

It is well-defined. For the triangle inequality, fix the representative of the first class, choose a sign of the second realizing the first minimum, and then a sign of the third realizing the second minimum; the norm triangle inequality bounds the minimum for the first and third classes. Positivity and symmetry are immediate. Thus this is a metric.

For 0<r<1/2 and a in S_X, pi_X maps the relative norm ball B_S(a,r) bijectively onto B_P([a],r). Indeed, every class in that latter ball has exactly one representative within r of a. For u,v in B_S(a,r),

    ||u-v||<2r<1,       ||u+v||>=2-||u-a||-||v-a||>2-2r>1.

Consequently this restriction of pi_X is an isometry. The full inverse image of B_P([a],r) is the disjoint union of B_S(a,r) and B_S(-a,r). These explicit charts prove that pi_X is a two-sheet covering, and that its quotient topology is the displayed metric topology. They also prove that pi_X is open.

Oddness and injectivity of f make

    F:P_X -> P_Y,       F([x])=[f(x)]

well-defined and bijective. Property (P) proves that F is an isometry. In particular, F and its inverse are continuous. The map to be lifted is the continuous map q=F o pi_X:S_X -> P_Y. Continuity of f itself has not been assumed or inferred.

## 3. Elementary path and homotopy lifting

We give the required covering argument rather than assume that signs chosen on separate faces fit together.

For the explicit covering pi_Y, a continuous path gamma:[0,1] -> P_Y and an initial representative y_0 of gamma(0) have a unique continuous lift. Cover the compact parameter interval by inverse images of evenly covered metric balls and choose a finite subdivision such that the image of each subinterval lies in one such ball. On the first subinterval use the sheet containing y_0. On each subsequent subinterval use the sheet containing the already defined endpoint. The inverse chart defines the lift on that whole subinterval. Adjacent pieces agree at endpoints, so they fit continuously. Two lifts with the same starting point agree: their equality set is closed and, by the sheet charts, both it and its complement are open in the interval. Uniqueness also shows that negating a lift negates its initial and terminal representatives.

We need homotopy invariance even when the base point moves. Let H:[0,1]^2 -> P_Y be a continuous family of loops, so H(s,0)=H(s,1) for each s. A continuous lift of H exists after choosing one corner representative. To see this, pull back an evenly covered open cover to the square. Compactness gives a finite grid fine enough that each closed grid cell maps into one evenly covered set. On the first cell use the inverse sheet through the chosen corner. Extend cell by cell along a row, and then row by row. On a new cell, the already specified bottom and/or left edge determines the sheet through the common corner. The inverse chart agrees on those edges by uniqueness of path lifts. This yields a continuous lift on the square by the finite pasting property. It follows that the endpoint sign eta(s), defined by

    Htilde(s,1)=eta(s) Htilde(s,0),       eta(s) in {1,-1},

is constant: the distance between those two unit vectors is either 0 or 2 and is continuous in s. Therefore a loop freely homotopic to a constant loop lifts to a closed loop, regardless of the chosen starting sheet.

The sphere S_X is path connected when dim_R X>=2. If u,v are not antipodal, normalize the segment (1-t)u+tv. If they are antipodal, join them through a unit vector independent of u. It is also locally path connected. The normalization map N:X\{0} -> S_X is open: if w is in an open set A, then all sphere points sufficiently near N(w), rescaled by ||w||, remain in A. The image under N of a sufficiently small open convex ball centered at a unit point is therefore open and path connected, and such images form arbitrarily small neighborhoods in S_X. The latter smallness follows from ||N(w)-a||<=2||w-a|| for ||a||=1.

## 4. Construction of a continuous odd bijective lift

### 4.1. Source dimension at least three, including arbitrary infinite dimension

Every continuous loop alpha:[0,1] -> S_X is freely nullhomotopic. Here is a finite construction that works in nonseparable spaces too. Uniform continuity gives a subdivision such that the polygon p(t) interpolating the sampled alpha(t_i) satisfies ||p(t)-alpha(t)||<1/8. It follows that ||p(t)||>7/8 and that beta(t)=N(p(t)) satisfies ||beta(t)-alpha(t)||<1/4. Hence

    N((1-s)alpha(t)+s beta(t))

is a homotopy of loops: each unnormalized vector stays within 1/4 of the unit vector alpha(t), so never vanishes.

The normalized polygon beta lies in the finite union of subspaces

    E_i=span_R{alpha(t_i),alpha(t_{i+1})},       dim E_i<=2.

Since dim_R X>=3, there is a unit vector z outside this finite union. For completeness, a finite union of proper linear subspaces over R cannot be all of X. Choose a finite-dimensional subspace V on which each intersection E_i cap V is proper, by including for each i one vector outside E_i. For each i choose a nonzero linear functional on V vanishing on E_i cap V. Their product is a nonzero polynomial, and a nonzero real polynomial cannot vanish on all of V (induction on the number of variables proves this). A point where that product is nonzero avoids the whole union; normalize it.

Now

    N((1-s)beta(t)+s z)

is a homotopy of loops to the constant z. Its numerator could vanish only if z were a negative scalar multiple of a beta(t), contradicting z outside every E_i. This proves the assertion about loops without a compactness or finite-dimensionality assumption on X itself.

Fix x_0 in S_X and choose y_0 over q(x_0). For x in S_X choose a path from x_0 to x, lift its q-image starting at y_0, and let h(x) be its endpoint. This is independent of the chosen path. Indeed, concatenating one path with the reverse of another gives a sphere loop; the preceding nullhomotopy and section 3 imply that its q-image lifts closed. Uniqueness of reversed path lifts then identifies the two endpoints.

The map h is continuous. For x, choose an evenly covered neighborhood V of q(x) and a path connected open neighborhood W of x with q(W) contained in V. Paths inside W show that h on W is the continuous inverse sheet of pi_Y through h(x), composed with q. Also pi_Y h=q, so h(x) belongs to {f(x),-f(x)}.

### 4.2. Source dimension two

Choose any auxiliary Euclidean norm on X and a continuous parametrization a:[0,2] -> S_X obtained by normalizing a Euclidean circle, with a(t+1)=-a(t) for 0<=t<=1, and a(0)=a(2). Its only endpoint identification is the usual circle identification.

The path gamma(t)=q(a(t)), 0<=t<=1, is a loop. Lift it to b(t) with b(0)=y_0. For some eta in {1,-1}, b(1)=eta y_0. Define

    h(a(t))=b(t)                for 0<=t<=1,
    h(a(t+1))=eta b(t)          for 0<=t<=1.

The definitions agree at t=1, and the value at t=2 is eta^2 y_0=y_0. They therefore define a continuous h on the whole circle. Because q(a(t+1))=q(a(t)), it is a lift of q. This construction explicitly closes the potential monodromy obstruction after the two half-circle passages; it does not assume that the projective circle is simply connected.

### 4.3. Oddness, surjectivity and uniqueness in dimensions at least two

For either construction, q(-x)=q(x), so h(-x)=+/-h(x). Since S_X is connected and h is continuous, the sign is independent of x: the continuous function x -> ||h(-x)-h(x)|| takes values in {0,2}. Thus h is either even or odd.

The even alternative is impossible. First dim_R Y>=2, since otherwise P_Y and hence the bijective P_X would be singletons. If h were even, it would descend to a continuous map hbar:P_X -> S_Y. The map

    s=hbar o F^{-1}:P_Y -> S_Y

would be a continuous section of pi_Y. The image of a section is open in S_Y: near a selected point, continuity keeps the section in one sheet, where its image of a sufficiently small open base neighborhood is exactly the corresponding inverse-chart neighborhood. Its negative is open by the same argument. The two sets s(P_Y) and -s(P_Y) are nonempty, disjoint, and cover S_Y, because a section selects exactly one member of each antipodal pair. This contradicts path connectedness of S_Y. Hence h is odd.

If h(x)=h(z), applying pi_Y and then F^{-1} gives [x]=[z]; oddness rules out z=-x. Thus h is injective. For y in S_Y, surjectivity of F supplies x with [h(x)]=[y]. One of h(x),h(-x) equals y. Thus h is surjective.

Any two continuous lifts h,k of q differ by a constant sign: k(x)=+/-h(x), and x -> ||k(x)-h(x)|| is a continuous {0,2}-valued function on the connected S_X. Therefore the two lifts are exactly h and -h. They are both odd and bijective.

### 4.4. Source dimension one

S_X={x_0,-x_0}. Oddness and surjectivity of f force S_Y={f(x_0),-f(x_0)} and hence dim_R Y=1. There are exactly two odd bijections with the prescribed pointwise sign classes, namely f and -f. They are continuous and preserve the only nonzero distance, 2. This proves the lifting assertion in the remaining dimension.

## 5. Strict distance regions on a norm sphere

We require a precise planar fact, including flat portions of the unit sphere. This is the unit-radius part of the monotonicity argument in Martini--Swanepoel--Weiss, section 3.5, Proposition 31. We give its short proof, so the generalization and equality cases introduce no additional unverified dependency.

Let a,c be distinct nonantipodal unit vectors in a normed plane and let b be a unit point on the shorter radial arc from a to c, that is, a normalized positive combination of a and c. The ray through b meets the segment [a,c] in a point p=lambda b with 0<lambda<=1: convexity gives ||p||<=1. Consequently p lies between 0 and b. Add lengths along these two straight segments to obtain

    1+||a-c||
      = ||a-p||+||p-b||+||p||+||p-c||
      >= ||a-b||+||c||
      = ||a-b||+1.

Thus ||a-b||<=||a-c||. Endpoints are included by continuity. If c=-a, the same conclusion follows directly from ||a-b||<=2=||a-c||. Therefore, as a point travels along either planar half of a norm circle from a to -a, its distance from a is nondecreasing. Strict convexity is not needed; intervals of equality are allowed.

Fix x in S_X and put

    A_x={y in S_X: ||x-y||<||x+y||},
    B_x={y in S_X: ||x-y||>||x+y||}.

The set A_x is path connected and contains x. For y in A_x with y!=x, the vectors x,y are independent (y=-x is not in A_x). Set

    c_t=N((1-t)x+t y),       0<=t<=1.

The planar inequality gives ||x-c_t||<=||x-y||. It also gives ||x+c_t||>=||x+y||. For 0<t<1, this second application can be seen algebraically: y is a normalized positive combination of -x and c_t, since

    y = (||(1-t)x+t y||/t)c_t + ((1-t)/t)(-x).

Apply the inequality with starting point -x, intermediate unit point y, and endpoint c_t. The endpoint cases t=0,1 follow directly. Hence

    ||x-c_t|| <= ||x-y|| < ||x+y|| <= ||x+c_t||,

so the whole path remains in A_x. Joining such paths through x proves path connectedness. The other strict region B_x=-A_x is path connected and contains -x. In dimension one these assertions mean the two singleton regions and remain valid.

## 6. A continuous odd phase-isometry preserves the ordered distance

Let h be the lift in section 4. Pointwise changes of sign only permute the sum and difference norms, so h still satisfies (P). Fix x in S_X and abbreviate

    a(y)=||x-y||,       b(y)=||x+y||,       D(y)=||h(x)-h(y)||.

On A_x union B_x, the continuous function

    theta(y)=(D(y)-a(y))/(b(y)-a(y))

takes values in {0,1}. It is therefore constant on each of the connected sets A_x and B_x. At x, D(x)=a(x)=0, so theta=0 on A_x. At -x, oddness gives D(-x)=2=a(-x), so theta=0 on B_x. At every remaining point, a(y)=b(y) and property (P) directly gives D(y)=a(y). Thus

    ||h(x)-h(y)||=||x-y||             for every x,y in S_X.

This supplies the missing exact global metric interface. No face-intersection condition, orientation choice on an equality plateau, common support, strict convexity, or extension of h to interior points was assumed. Together with section 4, it proves the entire source-free residual frozen in SCOPE.md.

## 7. Invocation of Source322 and classification

Assume now X,Y are Banach spaces. The map h is a surjective metric isometry between their unit spheres. Source322, Theorem `thm:main`, applies with exactly these hypotheses and gives the unique surjective real-linear isometry U extending h, with

    U(0)=0,
    U(z)=||z|| h(z/||z||)             for z!=0.

All source maximal-defect, alignment, support, fixed-point and affine-extension operations are stipulated paid; none has been invoked for a phase map before section 6 established the ordinary-isometry hypothesis.

Because h(x)=+/-f(x), there is a unique sigma(x) in {1,-1} with f(x)=sigma(x)Ux. Both f and U are odd, so sigma(-x)=sigma(x). No regularity of sigma is asserted.

If another pair (V,tau) has these properties, V restricted to S_X is another continuous odd bijective lift of q. Section 4 says that it is either h or -h. Real linearity then gives V=U or V=-U on all of X, and the pointwise representation gives tau=sigma or tau=-sigma, respectively. This proves the exact uniqueness assertion, including dimension one.

Conversely, let U be a surjective real-linear isometry and sigma be any even sign function on S_X. Define f(x)=sigma(x)Ux. For each pair, multiplication of the signs merely interchanges the two norms, so (P) holds. To prove onto, write an arbitrary y in S_Y as Uu. Put c=sigma(u). Evenness gives sigma(cu)=sigma(u)=c, and hence

    f(cu)=sigma(cu)U(cu)=c^2 Uu=y.

All assertions of the frozen scope follow.

## 8. Scope checks and limits

The proof includes both small dimensions, arbitrary infinite dimension, nonseparable spaces, and unit spheres with flat faces. The only topological compactness used before Source322 is compactness of a parameter interval or square; the sphere itself need not be compact. The finite union of edge planes is formed from one loop and imposes no global separability condition.

The quotient operation uses both entries of the unordered pair in two different ways: its minimum constructs the metric quotient; both entries then force theta to be {0,1}-valued. An isometry for the minimum alone is not asserted to satisfy the theorem. Exact surjectivity is used to establish antipodal bijectivity and a quotient homeomorphism, and to exclude an even lift by a section of the entire target cover. No nonsurjective extension is claimed.

Approximate identities do not give a discrete branch function, so this proof asserts no modulus or stability estimate. Real signs do not represent arbitrary complex phases. Complex spaces with their scalars restricted to R satisfy precisely the stated real theorem; this does not imply complex linearity.

No Lean proof of this nominee was written or compiled. The inspected pinned comparator `lean/ComparatorChallenges/TingleySphereIsometry.lean` ends in `sorry`; it is an interface, not formal evidence for this proof or for Source322's analytic argument. There is no remaining mathematical obligation identified by the author within the frozen scope, but independent adversarial correctness and separate contribution review remain entirely outstanding.
