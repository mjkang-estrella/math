# Arithmetic156 — independent contribution review, round 1

**Verdict: TECHNICAL, conditional on correctness of the ENTIRE unchanged frozen theorem.** This is a contribution assessment only. It assigns no correctness verdict, acceptance, campaign count, or literature-priority claim. The condition has not been discharged by this role. No finding from a correctness reviewer or another live peer was read or inferred.

The reason is an integrated full-scope reduction, rather than a list of familiar ingredients. The stipulated source already supplies the actual eightfold, its root-stack map, its surjection, the genus-one fibres, the divisor identity, every codimension-one submersion witness, and specialness transfer. On a sufficiently positive transverse curve, actual primary stack Lefschetz pays the one-factor integral fundamental-group identification. The integral disc presentation of a nodal elliptic fibration then supplies primitive killing discs. Each disc can be combined with paths in the other three smooth factors, killing each coordinate summand separately. Finally the source witnesses provide both inclusions in the precise root-meridian kernel computation, including upstairs exceptional divisors. These operations give item (1) for the same enlarged source parameter choice and retain every other assertion.

A second primary comparison is stronger than an abstract appeal to elliptic-surface folklore: Ue's actual multiple-fibre elliptic-surface theorem and proof apply to these one-factor surfaces. This comparison independently pays the same interface. The assessment does not depend on an inaccessible paper, an unread headline, monodromy coinvariants, a section of the global elliptic fibration, or a finite manifold uniformization of the fourfold root stack.

## Fixed scope, provenance, and interpretation

This review uses Codex / GPT-6 Astra / high / default service tier. Its authoritative brief is the 26,127-byte file with SHA256 `139df167e30961e9f6fa3845141756b833e9eb8e998757484a06c5556eb081bc`. The source pin is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. ALL operative upstream proofs, including compact abelianity, two-step monodromy and the conditional fourfold-pair manuscript, are stipulated true. They were read for their operations and hypotheses, not audited for truth.

The assessed target is exactly the 1,912-byte author FROZEN.md, SHA256 `91e62de24ee1198647e25cc0ee946b8043c480a6a975280bad046be581ed7e3c`. The assessed author proof is the 23,878-byte AUTHOR-PROOF.md, SHA256 `d9c17da764f4224dd02733a09a84eba9f5c47b6a37481ab68aa9e68d6b042f3e`. Their exact copies are private in this packet; the originals remain untouched.

For **every** smooth connected complex projective fourfold X and **every** nonempty smooth connected divisor D, let R be the order-two root Deligne–Mumford stack of (X,D). Its group is the topological stack group, equivalently the complement group modulo the normal closure of the squares of all D-meridians. The statement requires a smooth connected projective eightfold Y and a representable f:Y→R, with coarse composite g, satisfying all four assertions:

1. The induced map on the full discrete fundamental groups is an isomorphism, up to base-point conjugacy.
2. The smooth general fibre is a product of four smooth connected genus-one curves and has trivial cotangent bundle.
3. An effective Cartier E satisfies g*D=2E; there is a submersive point above a general point of **each** prime divisor other than D, and a submersive root-chart lift over a general point of D.
4. If R has no rank-one coherent subsheaf of Ω_R^p with Kodaira dimension p for any 1≤p≤4, with saturation and sections on root charts, Y is Campana-special.

The statement also requires that Y can be obtained from the source's four-factor diagonal-quadric construction, raising the base twist and imposing the author's extra curve conditions on a general coefficient tuple. The reduction below meets this additional requirement. It does not replace Y by an arbitrary projective realization of the same abstract group.

No uniform degree, index, polarization, canonical choice, simultaneous relative construction, finite/étale manifold uniformization of R, or claim for another root order, boundary configuration, or dimension enters the argument. The auxiliary curve cover below is not such a uniformization of R. Specialness is a conditional extra conclusion and is not imposed on X,D to obtain the construction or group isomorphism.

## 1. What the actual pinned source already pays

Write T for the tautological root line, T²=π*O_X(D), and V=O⊕O⊕T⊕T. The ambient space is the fourfold fibre product of P_R(V) over the same R. In each factor j the source imposes two diagonal quadrics

    q_jν = Σ_i a_jνi z_ji² = 0,       ν=1,2.

Columns 1,2 have coefficients in H⁰(X,M), columns 3,4 in H⁰(X,M(−D)); every coefficient is independent. A high ample power M makes both bundles globally generated. The actual `quadrics.tex`, `lem:parameters`, proves a common dense parameter open with smooth total root-chart zero locus, free diagonal inertia, three-column rank two off a codimension-two set Z, and all pair minors nonzero over a nonempty ordinary open.

The freeness estimate is specific and already paid: at a point of D, a fixed point in one P³ lies on one of its two eigenspace lines, requiring dependence of the corresponding pair of columns. A fixed point in all four factors requires four independent determinant conditions. Their codimension four exceeds dim D=3. The separate three-column rank-deficiency locus has parameter codimension two. It gives Z of codimension at least two in X and is the reason the witness statement covers every base prime, rather than merely a generic point of X.

The source's coordinate-square map is finite to an ordinary product of projective bundles with underlying bundle O²⊕O_X(D)². Finite algebraization/projectivity makes the free chart quotient projective. Smooth connected general fibres are the products of four complete intersections of two quadrics in P³: the Koszul calculation gives connectedness, and adjunction gives genus one and trivial canonical/cotangent line. There is exactly one dominating component Y; the source total space is smooth so its components are disjoint. All points where the root-chart projection is submersive belong to this component. Its dimension is 4+4=8.

The witness proof (`lem:fibres-witnesses`) is particularly useful for the proposed upgrade. If every deletion of one column leaves rank two, ker C_j contains a vector with all four coordinates nonzero. Taking its coordinate square roots makes 2C_j diag(z_ji) have rank two. Doing this in all four factors gives a root-chart submersion. Off D it is an ordinary submersion. The map to R pulls its root-divisor section back to an effective Cartier E with g*D=2E. These are actual witnesses on Y, not on a discarded auxiliary component.

The actual `transfer.tex`, `prop:transfer`, then gives the source surjection and specialness. Its specialness proof covers every p≤dim Y, not merely p≤4: on a smooth compact fibre the cotangent filtration has trivial graded pieces; a nonzero dual section shows plurisection ratios are constant there. Independent ratios therefore descend to X and force p≤4. Their wedge direction and tensor coefficients descend. The ordinary and root-chart analytic sections test all divisorial poles, followed by extension across codimension two and saturation on root charts. The resulting line on R has Kodaira dimension p, contradicting the stipulated differential-line specialness. Thus items (2)–(4) already hold for every member of this source open. Neither the compact abelianity theorem nor its strength is a new contribution of Arithmetic156.

I read the canonical wrappers and all operative main-route bodies of all three stipulated manuscripts. The two-step manuscript's representation/Malcev conclusions are not an integral injectivity theorem for f. Its retained-exceptional disc operations, and the compact manuscript's actual meridian/inertia operations, are compatible antecedents, not substitutes for the exact quotient below. The alternative inertia manuscript's last three sections are authenticated but not premises of this reduction.

## 2. Enlarged generic choice in exactly the source parameter space

Fix a sufficiently ample smooth complete-intersection curve C⊂X, transverse to D, with genus at least two. An ample complete-intersection curve meets the nonempty effective D; write the distinct marked points as d₁,…,d_m, m>0. This choice makes no positivity assumption on D. Raise M **after** fixing C. Serre vanishing gives surjective restrictions to C of both coefficient spaces; sufficiently high twists also give the bounded jet evaluations needed below, uniformly for points of the fixed curve.

In the affine space of four independent 2×4 matrices of coefficient sections, impose the author's full list: no zero column, no common zero of distinct pair determinants within a factor, simple zeros of every pair determinant, disjoint discriminants of different factors, nonzero pair determinants at all marked points, and simple pairwise disjoint zeros of the first-row entries, also nonzero at the marked points. These are finitely many open conditions on the fixed proper curve.

For the nonemptiness calculation, a zero column has codimension two. Two distinct pair dependencies also have codimension at least two: if the pairs overlap and the common column is nonzero, three columns must be collinear; if that column vanishes, its vanishing already has codimension two. For disjoint pairs the conditions are independent. Dependencies in different factors likewise have codimension two. The incidence with a one-dimensional curve therefore misses a general tuple. At a single pair dependency, the other exclusions make its determinant hypersurface smooth, and first jets impose an independent extra equation for a multiple zero. The same zero/derivative argument treats first-row entries. At the finitely many marked points all requested nonvanishings are nonempty open evaluation conditions. Surjective jet evaluation transfers these matrix/jet counts to the global coefficient space.

First-row conditions ensure the total first quadric is smooth: where no coefficient vanishes its vertical quadratic derivative suffices; at a simple zero the base derivative at the corresponding vertex is nonzero. At marked points the coefficients do not vanish, so the root coordinate causes no failure. The conditions on pair determinants give smoothness of the two-quadric surface, including the nodal fibres described next. They also prevent inertia fixed points on that surface over a marked point: its two fixed lines are excluded precisely by the nonzero determinants for the first and last pairs.

The source open and this additional nonempty open lie in the **same irreducible affine coefficient space** for the now fixed M. Their intersection is nonempty. There is no induction through mutually incompatible “generic” choices, no choice separately at each point of X, and no replacement of the diagonal system by a general complete intersection. Increasing M retains the source's global-generation hypotheses. This is the parameter compatibility required by the entire theorem, including its last construction sentence.

## 3. One-factor geometry and the primitive local relation

Let R_C=C×_X R and S_j⊂P_{R_C}(V) be one two-quadric factor. It is a smooth compact surface with trivial stabilizers; its projectivity follows either from the same finite coordinate-square map or by restriction of that construction. Over an ordinary point with all minors nonzero its fibre is a smooth connected genus-one curve.

At a simple zero of exactly one pair minor, reorder columns and perform an invertible row operation. One equation expresses a nonzero linear combination of the remaining two squared coordinates as zero; it factors into two distinct linear forms. On each resulting plane the other equation is a smooth conic, because the remaining minors are nonzero. Their intersection has exactly two transverse points. Thus the fibre is the reduced I₂ cycle of two conics. Simplicity of the determinant zero supplies the nonzero smoothing parameter at both nodes: in disjoint balls the map is xy=t. The total surface is smooth, and away from those two balls the fibration is a bundle over a small disc. No irreducible-fibre theorem is applicable to this fibre.

On a nearby torus the two vanishing circles are parallel, nonseparating simple circles. A nonseparating simple circle on a torus represents a primitive element δ of H₁(T²,Z)=π₁(T²). The two local contractions give two 2-handles with attaching classes δ and ±δ. Consequently the fundamental group of the total space over this small disc is

    Z² / ⟨δ, ±δ⟩ = Z² / Zδ ≅ Z.

This is an integral assertion. Monodromy is T_δ², whose coinvariant relation can yield only 2δ and may leave Z/2. That computation alone does not pay the author interface. The actual contraction discs do.

Amorós–Bogomolov–Katzarkov–Pantev, [math/9810042v2](https://arxiv.org/abs/math/9810042v2), §2 and the proof of Lemma 3.2, give the local Morse/vanishing-cycle attachment and van Kampen operation used here. Their global lemma is stated with a section and a sphere base, and their definition separates critical values. I do **not** import those hypotheses as if they held here. The two node balls above are disjoint; one can attach their handles separately, or perturb their critical values inside the small disc while fixing its boundary. The relative handle computation is unchanged and imposes the primitive relation twice. This is the same local operation, with its equal-value compatibility explicitly accounted for.

## 4. Actual primary payments of the one-factor group interface

### Integral stack Lefschetz on the specified positive cuts

Halpern-Leistner, [arXiv:1008.0891v1](https://arxiv.org/abs/1008.0891v1), Theorem 2.5 and Corollary 2.7, were read with their proofs and appendix. The ambient object is a smooth complex Deligne–Mumford stack with compact coarse space; positivity is the paper's curvature/type-k condition on an orbifold line bundle. The Morse attachment statement yields vanishing relative homotopy in degrees i<k and an isomorphism on π_i for i<k−1. It is a statement about the stack's homotopy type, with finite stabilizer cells retained. It is not a coarse-space or rational-cohomology substitute. The divisor inclusions here are representable closed inclusions. The theorem does not require a representable map from the line bundle to a classifying stack.

Here is a direct way to verify the positivity requirement without guessing that positivity on the whole four-factor product is enough. The root curve has a finite representable Galois cover C' by a smooth curve. In the presentation

    ⟨a_i,b_i,c_l | Π[a_i,b_i] Πc_l=1, c_l²=1⟩

send all c_l to the nontrivial element of C₂ if m is even and all handles to 1. If m is odd, use c=(12)(34), a=(34), b=(13)(24), so [a,b]=c, with only the first handle nontrivial and every c_l mapped to c. The image is the order-eight group generated by a,b; a,b are involutions and ab has order four. The kernel is injective on every local order-two isotropy group. Filling the punctured cover by w↦w² gives the connected finite Galois representable cover C'→R_C. Riemann–Hurwitz gives

    2g(C')−2 = degree(C'/R_C) · (2g(C)−2+m/2)>0.

In particular C' is aspherical. This construction imposes no parity restriction on m and no condition on π₁(X).

On P(V)|C', a metric on O(2) has strictly positive vertical Fubini–Study curvature. Horizontal and mixed curvature terms are bounded on the compact bundle. The pullback of a high positive metric on M adds an arbitrarily large positive horizontal term. In a horizontal/vertical block decomposition the vertical block is positive, and its Schur complement becomes positive after increasing the base twist. Averaging the logarithms of the resulting metrics over the finite deck group preserves positive curvature and gives a descended positive orbifold metric. Restriction preserves positivity on the smooth first quadric Q_j.

Thus the ambient projective bundle has dimension four and type k=4, and Q_j has dimension three and type k=3. Apply the cited theorem successively to Q_j and S_j. Both inclusions induce π₁ isomorphisms. The P³ fibre is simply connected, so the bundle projection gives the natural isomorphism

    π₁(S_j) ≅ π₁(R_C).

The covering correspondence then makes S'_j=S_j×_{R_C}C' connected and gives π₁(S'_j)≅π₁(C'). These are induced-map statements; no abstract isomorphism with an unidentified map is substituted. Both cuts remain the author's actual diagonal quadrics.

### Stronger elliptic-surface comparison with multiple fibres

Masaaki Ue, [*On the diffeomorphism types of elliptic surfaces with multiple fibers*, Invent. Math. 84 (1986), 633–643](https://doi.org/10.1007/BF01388750), Proposition 2, gives the natural orbifold fundamental-group identification for an elliptic surface with positive Euler number. I retrieved the publisher PDF and read the entire extracted paper, including the standard-model argument, its logarithmic transformations, and the normal-form claim proved later in the paper. The key printed pages were also checked visually.

This is applicable to the actual S_j→C. At the marked points the root-cover fibre is smooth and the inertia acts freely, so the coarse fibration has a smooth fibre of multiplicity two. Away from those points its singular fibres are I₂. The first-pair determinant is a nonzero section of M²|C of positive degree; its simple zeros avoid the marked points. Thus there is at least one singular fibre and e(S_j)>0. The I₂ components have self-intersection −2: if A,B are its components, (A+B)·A=0 and A·B=2. No fibre contains a (−1)-curve, so the fibration is relatively minimal. No global section is assumed or needed.

Ue's proof has genuine operative content. In its standard model the vanishing cycles kill both torus generators, leaving the base group for a punctured base. Filling by logarithmic transforms of multiplicities m_l then imposes precisely the powers of the peripheral base loops. In this application m_l=2, giving exactly π₁(R_C). The proof identifies the homomorphism induced by the elliptic projection, not just the isomorphism type. Ue invokes earlier classification/standard-model results of Matsumoto and Moishezon; I did not recursively acquire all of those originals. That bibliographic limit does not create an unpaid premise in the reduction above, which uses the independently fully read stack-Lefschetz proof instead. Ue supplies an additional actual primary comparison, not the only support for the verdict.

Shimada [arXiv:0906.1074v1](https://arxiv.org/abs/0906.1074v1), Corollary 1.1, requires irreducible general fibres over divisors. I₂ violates that hypothesis. Its Example 3.5 (xy:C²→C) shows directly why monodromy alone can fail to detect the killed fibre loop. Its Nori-type Proposition 3.1 uses a smooth point in the general fibre over every divisor. These readings help delimit the route; neither the irreducible-fibre corollary nor an unread extension is a premise.

Sommese–Van de Ven, [*Homotopy groups of pullbacks of varieties*, Nagoya Math. J. 102 (1986), 79–90](https://doi.org/10.1017/S002776300000043X), was read in full. Its actual proof uses k-ampleness, the homogeneous-space action and relative homotopy/quasifibration comparisons; Remark 3.2.1 records the vector-bundle zero-set Lefschetz range. It does not by itself furnish an unproved stack extension for the entire product construction. The two positive one-factor stack cuts above avoid that extra assertion.

## 5. From the one-factor group to all integral killing discs, without a section

Let B be the universal cover of C', a contractible disc, and let W_j=S'_j×_{C'}B. The natural isomorphism just proved means W_j→S'_j is its connected universal covering. Therefore W_j is simply connected. The lifted discriminant is locally finite.

Fix a regular base point b and exhaust B by compact discs K containing b, with regular boundaries and finitely many critical values inside. For each K choose disjoint small critical discs and an arc tree joining them to b. Over the complement of these discs the fibration is a torus bundle. Local sections through regular points of the singular fibres exist, and one can join their values along the tree by path lifting. This suffices to identify the boundary base loops and perform van Kampen. It does not assert a global section of S'_j→C'.

Equivalently, start with the product over a thickened tree and attach each local nodal piece. For π₁ the only added relations are the transported primitive vanishing cycles. The base is a disc, not a sphere closed by an additional capping piece, so there is no global section obstruction or extra π₂(base) relation. The resulting presentation is

    π₁(W_j|K) = Z² / ⟨δ_v : critical nodes inside K, transported to b⟩.

Choices of transport conjugate the geometric relations or change the chosen generators in the usual monodromy fashion; all paths are included when necessary. Compactness of each loop and null-homotopy in W_j allows passage to the exhaustion. Since π₁(W_j)=1,

    ⟨all transported primitive δ_v⟩ = Z²

as an integral subgroup. This is stronger than rational span and stronger than a monodromy coinvariant calculation. Since Z² is finitely generated, finitely many of these actual thimbles already suffice to generate it. The comparison does not need a uniform bound on their number.

The disc argument is the local handle operation in §3 assembled on a tree. Shimada's example concerning π₂ of the base explains why replacing the disc/aspherical base by an arbitrary base without checking capping relations would be wrong. Here that hypothesis has been explicitly supplied.

## 6. Transport through the other three factors

The four discriminant sets on R_C are pairwise disjoint. Thus

    P=S₁×_{R_C}S₂×_{R_C}S₃×_{R_C}S₄

and P'=P×_{R_C}C' are smooth: near a critical point only one factor can be critical, while the other three are smooth maps and their base changes preserve smoothness of the total product. Root inertia is free on the one-factor surfaces at marked points, so P is an ordinary projective variety. Its fibres are connected products, including the connected I₂ fibres; properness and connected base give connectedness. The same holds after the curve cover.

Take one transported thimble d:D²→W_j whose boundary is a loop in the j-th torus over b. Its projection runs along a parametrized vanishing path α from b to a j-th critical value. Detour α around the discrete critical values of the other factors. At such a value the j-th factor is smooth, so inserting a small detour changes transport only by an isotopy on the j-th fibre; it introduces no new j-th vanishing cycle. Because the discriminants are disjoint, the endpoint remains a regular value for all other factors.

For k≠j, choose the initially fixed point e_k in its torus over b and lift α to a path s_k in W_k by smooth parallel transport. In a standard thimble parametrization the base projection factors through a radial parameter t:D²→[0,1], with t=0 on the boundary and t=1 at the centre (or the reverse convention). Define the product disc by

    z ↦ (s₁(t(z)), …, d(z), …, s₄(t(z))).

Every coordinate has the same base projection α(t(z)); all other coordinates have a unique limit at the centre and are constant e_k at the boundary. This is a continuous disc in the fibre product over B. It bounds exactly the j-th vanishing loop with the other three coordinates constant. There is no diagonal relation involving other torus generators. A parametrized path suffices even if its image revisits a point; a section over the whole curve is never used. One can equivalently use local sections over a thin contractible neighbourhood of a simple chosen path.

Repeat for the finite generating collection from §5, in each j. Since

    π₁(F)=π₁(E₁×E₂×E₃×E₄)=⊕_{j=1}^4 Z²,

the map π₁(F)→π₁(P') is zero. Projection to P preserves these null-homotopies. The connected P is exactly the source zero locus restricted to C and meets the general connected fibre of its unique dominating component Y. Smoothness of the source zero locus makes its components disjoint, hence the whole P lies in Y. Therefore π₁(F)→π₁(Y) is zero. Transport between base points in the connected smooth base open changes only the specified base-point conjugacies.

This is the main proposed residual in the author narrative. Its full compatibility is now exhibited: each contraction is multiplied by three **paths**, not three global sections; it kills the coordinate generator itself; the detours use disjoint critical sets already ensured in the same parameter open. No new existence theorem, numerical estimate, lifting obstruction, or global section construction remains in this step.

## 7. Exact root-meridian kernel, retaining exceptional divisors

Choose a connected Zariski open U⊂X\D where g is a proper smooth fibration with the connected product fibre F. Put

    Γ=π₁(Y_U),   B₀=π₁(U),   K=im(π₁(F)→Γ).

The fibre-bundle exact sequence gives a surjection Γ→B₀ with kernel K; in particular K is normal. Let N=ker(Γ→π₁(Y)). General position for loops and null-homotopy discs shows Γ→π₁(Y) is surjective and N is normally generated by meridians of **every** divisorial component of Y\Y_U. Components mapping into codimension-two subsets of X are not omitted. Strata of complex codimension at least two upstairs can be avoided by the discs and add no separate generators.

Let L=ker(B₀→π₁(R)). The same complement argument, followed by the definition of the root group, says L is normally generated by meridians of the removed ordinary base divisors and squares of the D-meridians. Closed subsets of base codimension at least two do not add generators. Denote the image of N in B₀ by N_B.

First, N_B⊂L. Every upstairs meridian dies on filling Y_U to Y, and f is a global map Y→R. Its image therefore dies in π₁(R). This handles exceptional divisors automatically, even when their images lie in smaller subsets or several removed divisors meet there. It does not guess their individual multiplicities or discard them.

Second, L⊂N_B. At a general point of each removed prime P≠D the **source's actual ordinary submersion witness on Y** gives an analytic section over a transverse small base disc. Its boundary lies in Y_U and is null-homotopic in Y; its projection is the positive P-meridian. At a general point of D, the root-chart witness gives an analytic section over a root-coordinate disc u, with coarse transverse coordinate x=u². Its boundary projects to the square of the D-meridian and is again null-homotopic in Y. Conjugating paths can be lifted because Γ→B₀ is onto. These give all the stated normal generators of L. Thus N_B=L.

It follows by the elementary quotient identity that

    π₁(Y)/im π₁(F)
       = Γ/(N K)
       = B₀/N_B
       = B₀/L
       = π₁(R).

The map is the original f_* by construction. Section 6 kills im π₁(F), giving item (1) with the required base-point convention.

The actual proof of Campana [arXiv:0705.0737v8](https://arxiv.org/abs/0705.0737v8), Proposition 11.9, is the close primary antecedent. It passes from an ordinary fibre-bundle exact sequence to the orbifold quotient by peripheral loops and fibre multiplicities, using the appropriate gcd/Bézout relations. Its stated setup requires a neat divisible orbifold morphism. I have not silently asserted that our particular g is already neat. The displayed argument supplies precisely the needed divisibility/functoriality and reverse inclusion from f and the existing witnesses, with all exceptional upstairs divisors retained. This is an explicit application of that meridian operation, not an unsupported invocation of “Nori exactness.” Shimada Proposition 3.1 is an additional ordinary-interface comparison; its referenced original Nori proof was not acquired and is not an independent premise here.

## 8. Full-scope accounting and contribution judgment

The same general coefficient tuple in §2 lies in the source open, so its dominating Y remains smooth connected projective of dimension eight with the same representable f and coarse g. The fibre and divisor assertions are those in §1. Specialness transfer there applies to this Y without changing its differential-line convention. Sections 3–7 add the full **integral** isomorphism. This covers all four numbered items, the enlarged construction choice, every X,D in the frozen quantifiers, and every frozen exclusion.

The proposed operations have the following contribution status under the entire-theorem correctness condition:

| Proposed extra operation | Strongest compatible payment actually carried out |
| --- | --- |
| One-factor integral π₁ identification on the root curve | Positive two-stage stack Lefschetz with k=4,3 and the P³-bundle sequence; also Ue's applicable multiple-fibre elliptic-surface operation |
| Primitive two-node relation | Two disjoint local Morse 2-handles; both attach on a primitive δ, rather than using T_δ²−1 |
| Generation of the whole fibre lattice without a global section | Disc/tree van Kampen and exhaustion of the aspherical base cover, using the natural one-factor isomorphism |
| Passage to four factors | Explicit product of each thimble with three path lifts, enabled by the same disjoint-discriminant genericity |
| Exact root kernel rather than a quotient | Fibre-bundle sequence, all upstairs meridians, global root functoriality, and analytic sections of the source witnesses |
| Remaining frozen assertions | Source eightfold/fibre/witness construction and `prop:transfer`, retained on the intersected parameter open |

This assessment does not claim that a printed antecedent states Arithmetic156 verbatim, nor that the author did no useful work. The manuscript makes the source's surjection into an exact integral realization, and documenting the primitive relation and exceptional-divisor argument is valuable. But under the supplied acceptance rule, a routine compatible source/classical composition is technical even when its corollary has a stronger headline. The required comparison is now at the full frozen scope, with the compatibility steps performed. There is no identified closed residual requiring a nonroutine operation beyond these payments.

There is **no unresolved essential contribution-assessment step** in the route used for this verdict. The independent correctness condition remains outside this role; this statement is not a correctness grade or a certification that another role has discharged it. In particular, giving the strongest reduction is neither silently modifying the author's files nor labeling a repaired proof “PASS.” Ue is an additional comparison to an interface the author already proves by stack Lefschetz, not a repair submitted for adoption.

## 9. Original-history comparison and limits

I independently read original eligible history intervals, rather than treating the author's read log as my reading. The most relevant complete earlier construction is Arithmetic12's original OA057 scope and candidate: it treats arbitrary-dimensional SNC root orbifolds and virtual abelianity via an auxiliary manifold with an abelian general fibre and a surjection. Its affine finite-group/abelian-factor construction and local sections are different from this exact diagonal eightfold realization; it expressly does not establish this injective π₁ map. That old full scope is unchanged and is not regraded. The relevant operation already present is transfer through a manifold witness, not an exact duplicate claim.

Arithmetic17's original real-class marking and scope/transport bodies supply smooth-family/aspherical-base transport comparisons in a different geometric problem. The cross-family proposal and selected original iterations were read through their next equal-or-higher heading. Hodge-cover/cylinder and marked-cover tuple histories share genus-one or cover language but concern different representations and obstructions; they do not pay the present integral product kernel. Other hits were false admissions, including elliptic PDE/surface-immersion material, flow orbifolds, and the unbounded-word lexical match “Nori” inside “ignoring.” They are disclosed, not counted as a theorem-duplicate search success.

The guard removes many useful-sounding namespaces coarsely, and opaque aliases can escape it. No exhaustive worldwide or project-history clearance is claimed. The verdict rests on the positive integrated derivation above, not on an absence-of-hits argument. No excluded completed or live-round body, other Arithmetic156 role, peer verdict, or parent adoption/status was consulted. Exact old-scope bodies and metadata remain private/local under their original rights.

The precise extents, hashes, recovery of tool-output truncations, source authentication, access/version limits, guard predicates, and artifact-only verification are in `private/READING-AND-ISOLATION.md` and its machine-readable companions. Hashing, copying, metadata inspection, lexical scanning, and semantic reading are recorded separately. All protected source, primary, copied-original, rendered, and named metadata files remain private/local and unstaged. No downstream formalization, manuscript, release, public action, nested agent, shared edit, or git operation was undertaken. Parent alone integrates and adopts any grades or counts.
