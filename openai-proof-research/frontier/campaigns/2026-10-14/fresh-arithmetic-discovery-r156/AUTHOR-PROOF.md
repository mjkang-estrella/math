# Exact fundamental-group transfer for the special eightfold construction

Author-proposed proof of the immutable statement in FROZEN.md. This is a discovery packet, not a correctness or contribution decision. All source operations at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. No theorem about unrestricted quasi-projective groups is assumed.

## 1. Inputs and the extra assertion

Write R = sqrt[2](X,D), with tautological line T and T^2 = O_X(D) pulled back to R. The pinned fourfold-pair main manuscript, Proposition `prop:eightfold` and Lemmas `lem:parameters`, `lem:projectivity`, `lem:fibres-witnesses`, constructs a smooth projective eightfold Y mapping to R. It is a component of a fourfold fibre product of intersections of two diagonal quadrics in P(V), where V = O^2 + T^2 denotes the direct sum of two trivial lines and two copies of T (here the superscript in the direct-sum notation counts copies, not tensor power). To avoid that ambiguity below, write V = O ⊕ O ⊕ T ⊕ T.

In factor j the equations are

    sum_{i=1}^4 a_{j,nu,i} z_{j,i}^2 = 0,    nu=1,2.

The first two coefficient sections belong to M and the last two to M(-D); all eight equations are sections of the corresponding relative O(2) tensored with M. The twists match because T tensor T = O(D). Source conventions for projectivization and coordinates are retained. The coefficients form a finite-dimensional affine parameter space. For M sufficiently positive the source gives a nonempty Zariski open set of tuples with smooth root charts, no stabilizers in the full product, projective coarse space, connected smooth general fibre equal to a product of four genus-one curves, and the specified submersion witnesses over all base prime divisors. The root section pulls back to a section with divisor E and g^*D=2E.

These are the paid inputs. The extra assertion to prove is injectivity of pi1(Y) -> pi1(R). The proof will kill the complete integral fibre group Z^8, using one fixed curve in the base. It does not invoke residual finiteness of pi1(R) or replace its full fundamental group by a linear quotient.

The primary Lefschetz input is Daniel Halpern-Leistner, *Lefschetz Hyperplane Theorem for Stacks*, arXiv:1008.0891v1, Theorem 2.5 and Corollary 2.7. For a positive line bundle on a compact smooth complex DM stack of dimension d, the zero locus inclusion induces an isomorphism on pi1 when d>=3. Positivity means a Hermitian metric with positive curvature on all complex tangent directions. This is a theorem about stack homotopy groups. We use it only for smooth successive cuts in dimensions four and three.

The local topological operation used below is the vanishing-circle contraction for the complex Morse model xy=t, followed by Seifert–van Kampen. Its standard disc construction is given in Amorós–Bogomolov–Katzarkov–Pantev, arXiv:math/9810042v2, Section 2 and proof of Lemma 3.2. We give the needed disc and simultaneous-node argument explicitly, so neither a global section nor a theorem for irreducible singular fibres is imported.

## 2. A curve and compatible general coefficients

Choose a smooth connected sufficiently ample complete-intersection curve C in X, transverse to D, of genus at least two. Bertini gives smoothness and transversality; by taking the defining very ample powers sufficiently large, adjunction gives genus at least two. Its intersection with the nonempty effective divisor D is nonempty and reduced. Let R_C = sqrt[2](C,C∩D).

Choose M sufficiently positive after fixing C. Besides the global generation used by the source, require restriction of the coefficient spaces H0(X,M) and H0(X,M(-D)) to separate the finite jets on C used below. Such a choice is possible: for high ample powers the restriction maps to C are onto by Serre vanishing applied to its ideal, and the restricted bundles separate the required jets. Uniform one-point and two-point jet separation on a fixed curve follows, for example, by the usual degree criterion for H1 of a line bundle after subtracting a bounded-length divisor. Only finitely bounded jet lengths are needed.

Trivialize the coefficient lines locally on C. For each j, let C_j(x) be its 2 by 4 coefficient matrix, and let Delta_{j,ik} be the locus where columns i and k are dependent. Impose the following generic conditions on the restrictions to C:

- No column is zero and no two distinct pair determinants vanish at the same point.
- Every zero of a pair determinant is simple.
- Determinant zeros from different factors are disjoint.
- All pair determinants are nonzero at every point of C∩D.
- In the first row of each matrix, each coefficient has simple zeros, no two of its four coefficients vanish together, and none vanishes at C∩D.

These conditions are simultaneously achievable. In the space of 2 by 4 matrices, a zero column has codimension two. Any two distinct pair-determinant equations have joint codimension at least two: if they share a column, a zero shared column is already codimension two, and otherwise their generic rank-one conditions are independent; the remaining common-column case forces the three columns to lie in a line, again codimension two. Different factors have independent parameter coordinates. Thus evaluation transversality excludes all these simultaneous conditions on a curve. At the smooth locus of one determinant hypersurface, first-jet freedom makes its intersection with C transverse. The singular locus of the 2 by 2 determinant hypersurface is the zero matrix, already excluded. The row conditions follow in the same way from evaluation and first-jet freedom. At the finitely many points C∩D they are finitely many nonvanishing conditions. All bad-incidence projections are closed because C is proper; the resulting nonempty open parameter conditions intersect the nonempty source open conditions in the irreducible affine parameter space.

Near a marked point of R_C the root coordinate u has coarse coordinate x=u^2. Coefficients come from X and are even in u; no derivative in u is needed there, since all pair determinants and first-row entries are nonzero at the marked point. Away from those points ordinary first-jet freedom applies.

Choose a tuple in this common open set. Denote the one-factor complete intersection over R_C by S_j. Denote its first quadric by Q_j inside P(V)|R_C. The first-row conditions make Q_j smooth. Indeed, a singular point of a diagonal quadric fibre must be supported in the coordinates whose coefficients vanish. There is at most one such coordinate; at that projective point the simple base derivative of the vanishing coefficient is nonzero, making the total hypersurface smooth. At marked points every coefficient is nonzero, so the fibre is smooth and the argument works in the root chart.

If all pair determinants of C_j(x) are nonzero, S_j has a smooth connected genus-one fibre, as in the source. The only remaining fibres on C have exactly one dependent pair. We now determine them and their total-space smoothness.

## 3. The actual singular fibres and their integral relation

Suppose columns 1 and 2 become dependent. Relabeling coordinates handles every other pair. Since neither column is zero and no other pair determinant vanishes, invertible row operations put the equations at the special base point in the form

    a z1^2 + b z2^2 + c z3^2 + d z4^2 = 0,
    e z3^2 + f z4^2 = 0,

where a,b,e,f are nonzero, and the other determinant conditions ensure that both conics below are nonsingular. Over C the second equation is the union of two distinct planes. On each plane the first cuts out a smooth conic. The two conics intersect in exactly the two distinct points

    z3=z4=0,   a z1^2+b z2^2=0.

Their intersection is transverse inside the surface fibre. A local elimination of the nonsingular first equation near either point leaves a product of two independent linear forms in z3,z4 as the quadratic part of the second equation. The derivative in the base direction of its remaining constant term is nonzero: the dependent-pair determinant vanishes simply and both coordinates z1,z2 at the point are nonzero. The holomorphic Morse lemma with parameter, or solving for the base parameter and applying the nondegenerate quadratic normal form, therefore gives xy=t near each node. The total surface is smooth. There are exactly two nodes, with disjoint node neighbourhoods, over that one base value. The fibre is the reduced cycle of two rational curves (type I2).

The vanishing circles of these two nodes are parallel nonseparating circles in a nearby torus. Each represents a primitive element delta of pi1(E)=Z^2, up to sign and transport. Primitivity also follows directly: cutting the smooth torus along one of these circles leaves a connected cylinder; an embedded nonseparating circle on an oriented torus is primitive. The specialization collapses the two parallel circles and has quotient group

    pi1(E) / Z delta = Z,

equal to the fundamental group of the two spheres joined at two points. A small total neighbourhood over a disc retracts to this central fibre. One can see the retraction by using the local xy=t plumbing in the two disjoint node balls and a horizontal trivialization on their complement; the latter is a proper submersion with boundary. Thus the inclusion of a smooth fibre into this disc total space is onto on pi1 with kernel Z delta.

This assertion uses actual contractions. The monodromy is T_delta^2, whose difference from identity on Z^2 has image 2Z delta. Imposing only monodromy relations would retain a spurious element of order two. No rational homology or unipotent completion argument replaces the integral calculation above.

At points of C∩D every pair determinant is nonzero. The nontrivial root inertia acts on P(V) by [z1:z2:z3:z4] -> [z1:z2:-z3:-z4]. Its fixed locus is the union of the first and last coordinate lines. The complete intersection misses these lines exactly because the first-pair and last-pair determinants are nonzero. The action on S_j over the marked point is consequently free. Thus S_j is a smooth compact projective surface, not just a stack with residual stabilizers. It still maps to R_C, and this is the map whose stack fundamental group is used.

## 4. One-factor integral Lefschetz

We first construct a finite smooth curve cover of R_C, without making any uniformizability assertion about R itself. If C∩D consists of m points, its orbifold group presentation is

    < a_l,b_l,gamma_i | product_l [a_l,b_l] product_i gamma_i=1,
                              gamma_i^2=1 >.

For m even, send all gamma_i to the nonidentity of C2 and all handle generators to identity. For m odd, set

    c=(12)(34), a=(34), b=(13)(24),

with rightmost permutation acting first. Direct composition gives [a,b]=c. Send all gamma_i to c, the first handle pair to a,b, and the remaining handle generators to identity. The relation maps to c*c=1. Use the regular action of the finite image group. Every marked meridian has exact order two in both constructions.

The resulting connected finite covering of C minus its marked points fills uniquely at every puncture by the local map w -> w^2. Giving these discs their pulled-back complex charts produces a compact Riemann surface C' and a representable finite etale Galois map C' -> R_C. Equivalently R_C is the quotient stack [C'/H] for its deck group H. Riemann–Hurwitz, using genus(C)>=2, gives genus(C')>=2. In particular C' is aspherical. This is a curve construction and provides no finite manifold covering of the fourfold root stack.

On P(V)|C' the relative O(2) has a metric with positive vertical curvature. Choose a smooth horizontal splitting. The negative and mixed parts of its curvature are uniformly bounded on the compact projective bundle. A positive metric on the pullback of a sufficiently high base power M contributes an arbitrarily large positive horizontal term. The Schur-complement criterion for a Hermitian block matrix then makes the sum positive on all tangent directions. This is why M was permitted to be sufficiently high. Average the logarithms of this metric and its H-translates. Curvature is the average of positive curvature forms, so positivity persists. The invariant metric descends to the quadric line on P(V)|R_C.

Apply stack Lefschetz to the smooth first quadric Q_j in the dimension-four projective bundle. Then apply it to the second quadric S_j inside the dimension-three Q_j; the restricted metric remains positive. Both inclusions induce pi1 isomorphisms. The projective-bundle projection induces a pi1 isomorphism because its fibre P3 is connected and simply connected (this may also be checked after the finite curve cover and on the associated classifying spaces). Hence the natural map gives

    pi1(S_j) ≅ pi1(R_C).                                  (4.1)

The finite pullback S'_j = S_j ×_{R_C} C' is connected: by (4.1), the pullback of the connected cover C' corresponds to the same subgroup of pi1(S_j). Applying the covering-space subgroup correspondence to (4.1) gives

    pi1(S'_j) ≅ pi1(C').                                  (4.2)

The morphism S'_j -> C' is a proper genus-one fibration, smooth except for the reduced I2 fibres described above. The etale base change in root charts creates no additional singular fibre at a marked point.

## 5. All integral fibre generators are vanishing relations

Here is the precise local-to-global consequence of (4.2). Pull S'_j back to the universal covering disc B of C'. Its total space W_j is simply connected: it is the connected covering of S'_j corresponding to the kernel in (4.2). The critical values in B are a locally finite discrete set. Fix a regular value b and its torus fibre E_j.

For a compact disc K in B containing b and finitely many critical values, with regular boundary, choose disjoint small discs about these values and a tree of paths from b to their boundaries. The paths avoid critical values. Over the regular part this is a smooth bundle. Over a tree it is trivial; over a punctured disc its fundamental group is a semidirect product of Z^2 by the free group of base lassos. Such a group splitting requires no global geometric section: choose lifts of free generators; there is no relation to obstruct them.

For a critical-value disc, choose a local section through a nonsingular point of its central fibre. It kills a lift of that base lasso in the disc total space. The local calculation in Section 3 kills precisely the primitive delta in the fibre group and has no other fibre kernel. Seifert–van Kampen, gluing along the annular regular pieces and the tree, therefore yields

    pi1(W_j|K) = Z^2 / < delta_v : v a critical value in K >.       (5.1)

For completeness, the local monodromy relation remaining from the punctured disc is delta^2-transvection; it becomes the identity after delta itself is killed, so it imposes no additional relation. For two simultaneous nodes, use their disjoint balls and attach both contraction discs; they have parallel boundaries and generate the same primitive subgroup. No assumption of an irreducible singular fibre has entered. The rest of K is a regular collar of the tree-of-discs domain, and bundle trivializations over the collars add no additional relation. This is the disc van Kampen construction, not the sphere construction with a potentially nontrivial capping relation.

Take a nested exhaustion of B by such discs, with their transport paths chosen inside the larger discs. Every loop or null-homotopy in W_j has compact image, so pi1(W_j) is the direct limit of (5.1). Since W_j is simply connected,

    Z^2 = < all transported primitive vanishing cycles >.         (5.2)

In particular a finite subset generates Z^2. There is no asserted uniform bound on the number of cycles needed. This argument also explains why the asphericity of C' matters: no boundary map from a base sphere is secretly killing a fibre generator that could fail to lift to a fibre product.

The cited primary comparison is exact. Shimada arXiv:0906.1074v1, Corollary 1.1, has an irreducible-codimension-one-fibre hypothesis. It cannot be applied here. His Example 3.5 makes the distinction between vanishing and monodromy kernels explicit. Equation (5.1) instead uses the actual nodal contraction and primitive integral relation.

## 6. Killing the fibre group in the four-factor product

Let

    P = S_1 ×_{R_C} S_2 ×_{R_C} S_3 ×_{R_C} S_4,
    P' = P ×_{R_C} C'.

At any singular value on C' only one factor is singular: the different factors' discriminants were chosen disjoint on C, and a covering preserves that property. The other three maps are smooth there. It follows that P' is smooth; locally it is a smooth base change of the smooth total surface in the singular factor. It is proper and has connected fibres, so it is connected. The same holds for P. Over the common smooth open its fibre is F=E_1×E_2×E_3×E_4 and pi1(F)=Z^8.

Consider a transported vanishing cycle in factor j that appears in (5.2). Its transport path can be chosen to avoid every other factor's critical values: those are discrete, and the j-th fibration is smooth across them, so detouring around them changes no j-th transport class. In a small disc around its endpoint, the other three factors are smooth proper bundles over a contractible disc. Choose a section in each. Along the transport path choose smooth transport for the three other base points, arranged to meet these sections. Multiply the actual j-th vanishing thimble by these three sections. It is a disc in P' with boundary the transported j-th vanishing circle and all other fibre coordinates fixed at their transported base points.

Transporting back to the original fibre shows that the image of this primitive j-th cycle is trivial in pi1(P'). Formula (5.2) therefore kills the entire j-th Z^2 summand. Doing this for j=1,2,3,4 gives

    pi1(F) -> pi1(P') is zero.                            (6.1)

All these assertions concern based loops up to conjugacy. The fibre group is abelian; moreover triviality survives any base-point conjugation. Projecting P' -> P -> Y preserves the null-homotopies, so

    pi1(F) -> pi1(Y) is zero.                             (6.2)

To justify P -> Y rather than merely to the full source zero locus: P is connected and smooth, and over the common smooth open it lies in the unique dominating component selected in the source. Since the full source zero locus is smooth, its components are disjoint; the connected P lies in that component throughout. Thus the map used in (6.2) is the actual one to Y.

## 7. Exactness for the root target, with all divisors retained

We prove the required exact sequence directly from the source submersion witnesses:

    pi1(F) -> pi1(Y) -> pi1(R) -> 1.                     (7.1)

Choose a nonempty Zariski open U ⊂ X minus D over which g is smooth proper with connected fibre F. Shrink by divisors if necessary so the remaining complement has a divisorial part and a subset of complex codimension at least two. Let Gamma=pi1(g^{-1}U). The smooth bundle sequence gives a surjection Gamma -> pi1(U), with normal kernel K equal to the image of pi1(F).

The inclusion g^{-1}U -> Y is onto on pi1. Its kernel N is normally generated by meridians about all prime divisors of Y minus g^{-1}U. This follows by perturbing loops off the complement and a null-homotopy disc transversely to its smooth codimension-one strata; strata of complex codimension at least two can be avoided. Thus

    pi1(Y) / image(pi1(F)) = Gamma/(N K)
                            = pi1(U)/image(N).           (7.2)

There is already a global morphism f:Y -> R, so every element of image(N) maps trivially in pi1(R). This observation handles also prime divisors of Y whose images have codimension at least two in X; there is no assumption that every upstairs divisor dominates a base divisor.

Conversely pi1(R) is the quotient of pi1(U) by ordinary meridians of each removed base prime P other than D and by the square of the D-meridian. Removing or restoring codimension-two subsets does not change pi1 of the smooth root charts, so it adds no further generator to this description. At a general point of an ordinary P, the source supplies a submersive point of g. A local analytic section through that point gives a transverse disc upstairs whose meridian maps to the base meridian once. It lies in N. At a general point of D, take the source submersive lift to the root chart and its local analytic section. Its transverse parameter u maps to the coarse parameter x=u^2. Thus its upstairs meridian maps to the square of the coarse D-meridian and also lies in N. Choose these discs away from all other removed base divisors. Their base-point transports give the required normal generators.

Therefore image(N) is exactly the kernel pi1(U) -> pi1(R). Equation (7.2) proves (7.1), including surjectivity. Combining (7.1) with (6.2) proves that f_* is an isomorphism. This argument uses the entire integral group, and exceptional divisors have not been discarded.

## 8. Completion at the frozen scope

The source gives Y smooth connected projective of dimension eight, its generic fibre a product of four smooth genus-one curves, g^*D=2E, and the two types of divisorial submersion witnesses. Increasing M and intersecting its source generic open set with the additional curve generic open conditions leaves each of these conclusions intact. Sections 2–7 prove the additional isomorphism for that same choice of Y.

If R is special in the frozen differential-line sense, apply the source Proposition `prop:transfer` to this actual g. Its four hypotheses are exactly the retained properties above. Its proof descends plurisection ratios along the compact connected trivial-cotangent fibres, saturates the resulting meromorphic differential line on root charts, and uses the ordinary and root submersion witnesses to remove every divisorial pole. It consequently proves Y special. The definition uses the source's root differential convention, and no equivalence with a different multiplicity convention is needed here.

This proves every item of the frozen author-proposed statement. The source compact abelianity theorem then also applies to Y, but virtual abelianity of pi1(R) was already paid by the source surjection and is not claimed as an additional finding. The proof gives neither a finite cover of R by Y (the relative dimension is four) nor a bound on the degree of any abelian subgroup.

## 9. Scope and comparison for independent review

The proposed bridge is the combination of integral one-factor stack Lefschetz, primitive two-node contraction relations, lifting those relations through the remaining smooth factors, and exact root-meridian kernel identification. The direct ample-hyperplane argument on the four-factor ambient product fails because each equation line is trivial along three other projective factors. The curve construction avoids asserting such ampleness or a new semiample stack theorem.

The original OA057 scope in the eligible r12 archive concerns virtual abelianity for all finite SNC root orders and constructs a group quotient; it explicitly does not assert an isomorphism. Its arbitrary-order inertia/free-affine-action construction is not modified or retried here. The present fixed fourfold/order-two statement concerns the exact full group of a special eightfold model. No priority claim follows from the guarded project search.

The ingredients above are classical or supplied source operations. Whether their compatible combination constitutes a substantial contribution is a separate assessment, which must compare the whole frozen scope to the actual stack Lefschetz and vanishing-cycle literature. No mathematical grade, acceptance or count is assigned in this packet. No formal verification is claimed.
