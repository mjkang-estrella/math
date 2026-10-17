# A real Kähler marking in the source compact-factor argument

Author support only; technical, not a substantial nomination. All source references below are at the pinned revision. The lemma is deliberately conditional on the proper map whose construction is the outstanding issue for the full normal Kähler target.

**Lemma.** Let Y be a smooth projective complex variety, U⊂Y a connected smooth semialgebraic open subset, and j:U→T a proper surjective holomorphic submersion with connected fibers. Suppose T is a connected Stein manifold homeomorphic to R^b. Let Γ be a countable group acting biholomorphically on U and T, with j equivariant and the action on T proper and cocompact. Suppose there is a smooth closed real (1,1)-form ω on U such that γ*ω=ω for all γ∈Γ and its restriction to every fiber is Kähler. Then every fiber of j is biholomorphic to every other fiber. More precisely, the pairs (F_t,[ω|F_t]) are all isomorphic, with the real cohomology class retained.

No integral polarization, finite fundamental group, or simple connectivity of the fibers is assumed. Their projectivity follows from their compact analytic embeddings into Y. The lemma's parameter group is allowed finite stabilizers, as in the actual source's `cmp:closed-rigidity`.

**Proof.** Write n for the common complex fiber dimension. If n=0, connectedness makes each fiber one point, and the conclusion is immediate. Assume n>0. Choose a projective embedding of Y and write a for its Fubini–Study (1,1)-form normalized to the hyperplane integral class.

All fibers are compact connected smooth projective varieties, hence irreducible. Their degree d=∫F_t a^n is constant. Indeed proper smooth local triviality identifies their fundamental cycles, and a is a global closed form. The locus C of integral n-cycles of degree d in Y whose supports are contained in U is semialgebraic. The map

    T → C,  t ↦ [F_t]

is a homeomorphism. This is exactly the source's `cmp:chow-base` operation, which only needs the proper flat family and Steinness of T: a compact irreducible analytic subvariety of U maps to one point of T, so an n-cycle is a whole fiber. Continuity is continuity of proper analytic families of cycles; inverse continuity follows by choosing convergent points on the cycles near a smooth point of a fixed fiber. This use does not require projectivity of U/Γ.

Fix t0∈T and put F=F_t0 and κ=[ω|F]. Choose a very ample line bundle H on F with a positive curvature form h representing c1(H). Since F is compact and ω|F is positive, there is a real c>0 such that cω|F−h is positive definite. Put

    B = ∫F_t (cω|F_t + a|F_t)^n.

B is a finite positive real number independent of t. To see the independence, expand the binomial. Each integrand is the restriction of a global closed 2n-form c^i ω^i∧a^(n−i) on U. Its integral is invariant under the compact fiber isotopies supplied by proper smooth local triviality. Since T is connected, it is constant globally. No claim that these real integrals are integers is needed.

Consider an isomorphism g:F→F_t satisfying g*[ω|F_t]=κ. Its graph in F×Y is an algebraic n-cycle by Chow's theorem. In the product embedding defined by H and O_Y(1), its integral degree is

    deg Γ_g = ∫F (h+g*a)^n ≤ ∫F (cω|F+g*a)^n
            = ∫F_t (cω|F_t+a)^n = B.                    (1)

The inequality follows term by term from positivity of cω|F−h and g*a. For example the difference of two kth powers of positive (1,1)-forms factors into the positive difference times a sum of wedge products of positive forms; wedging with the remaining positive factors and integrating preserves nonnegativity. The equality uses only cohomology, closedness, compactness, and the assumed class preservation. It does not assert equality of differential forms under g.

Take the finite disjoint union of projective Chow spaces of n-cycles in F×Y of positive degree at most floor(B). In its integral-cycle locus impose:

    support(G)⊂F×U;
    projection support(G)→F is bijective;
    projection support(G)→Y is injective.

These are first-order semialgebraic conditions on the algebraic universal incidence; write P for the resulting semialgebraic parameter space. Both projections are proper on each compact graph. The first is finite birational onto normal F, hence an isomorphism. The second is finite birational onto its image. Its compact irreducible n-dimensional image lies in a fiber of j and is the whole fiber, which is smooth and normal. Thus it too is an isomorphism. P therefore parametrizes all isomorphisms F→fibers whose graph degrees obey the fixed bound. Every isomorphism preserving κ is included by (1).

The universal incidence over P is continuously identified with F×P through the first projection: it is a proper continuous bijection over F×P, hence a homeomorphism. It gives a continuous evaluation e:F×P→U. Every connected component of P is path connected, and P has only finitely many components. On any such component the maps e_p:F→U are homotopic. Since ω is globally closed, e_p*[ω]∈H²(F,R) is constant on that component. Consequently the condition

    e_p*[ω] = κ

selects a union P_κ of whole connected components. It is semialgebraic, even though ω need not be definable or integral. This is the same component-marking operation as the source's `cmp:polarized-locus`; line bundles and the injectivity of c1 are unnecessary because the retained datum is the real class itself.

Taking the second image of a graph gives a semialgebraic map P_κ→C. Its image C_κ is exactly the locus of pairs isomorphic to (F,κ). The assertion follows from the graph inclusion above and the definable support identity, just as in the source proof. In particular every equivalence class of pairs is semialgebraic.

Each such class is Γ-invariant: γ|F_t:F_t→F_γt preserves the class by γ*ω=ω. Its closure in C is nonempty, closed, Γ-invariant and semialgebraic, so it has finite CW homotopy type. Transfer it to T by the homeomorphism T→C and apply the actual source lemma `cmp:closed-rigidity`. That lemma has exactly a proper cocompact smooth action on a Euclidean contractible manifold, allowing finite stabilizers. The closure is all of T. Thus every class is dense in C.

Two disjoint dense semialgebraic subsets of C cannot occur: a dense semialgebraic subset contains a dense relatively open subset by finite cell decomposition. The two relatively open dense subsets would intersect. Therefore there is a single class, as asserted. ∎

**Classical continuation, kept separate.** The Fischer–Grauert theorem now makes j a locally trivial holomorphic fiber bundle because it is a proper submersion of complex manifolds with mutually isomorphic compact fibers. The exact statement is reproduced as Theorem1.1 in Poczobut's original research paper retained in `private/primary`; the original1965 proof was not retrieved. The automorphism group of a compact complex manifold is a complex Lie group. If T is contractible Stein, the associated principal bundle is topologically trivial, and Oka–Grauert supplies a holomorphic trivialization. Forstnerič–Prezelj's actual Theorem1.3 and Lie-group example in the retained primary body supply the section interface. This continuation does not construct j.

**Contribution limit.** KP2012 Definition19 and the complete proof of Theorem20 already use bounded graph degrees to obtain finite algebraic parameter spaces for isomorphisms. CH2013 §2.B (retained text lines354–365) explicitly defines morphism spaces by degrees against fixed Kähler forms and obtains finite components from a bounded degree. Its proof of Theorem1.5 also uses compact cycle spaces to force a fiber-bundle conclusion. The inequality (1), finite bounded-degree union, and real component marking adapt these paid operations to the source's compact-factor framework. They are not claimed as a new substantial theorem or a new-to-literature construction.
