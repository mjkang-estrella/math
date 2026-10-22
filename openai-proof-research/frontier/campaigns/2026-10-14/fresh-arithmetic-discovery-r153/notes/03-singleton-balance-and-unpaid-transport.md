# Singleton balance, attempted refinement, and the remaining operation

PREFREEZE. This note carries the gluing refinement through the strongest source test, rather than stopping with the observation that a rational Hodge isomorphism is insufficient. It is not a theorem freeze and not a proposed weaker substitute for any archived target.

## 1. Keep all K3 surface identities

Fix a large admissible d and a rank-21 Hodge lattice tau occurring in the previous note. Let I index the isomorphism classes of Picard-one K3 surfaces S with T_S(-1) isometric to tau. Birational equivalence of smooth K3 surfaces is isomorphism, so this also indexes their surface function-field classes. This is a finite partner set by the primary lattice framework, but the argument below only requires the finite subset actually occurring in a chosen factorization.

For a smooth weak factorization between cubic Mori endpoints write n_i^+ and n_i^- for the number of additions and removals of centers birational to S_i. Multiplicities are counts of centers, not degrees of residue field orbits. The full strength of sf:vanishing, applied separately to every singleton {S_i}, is

    n_i^+ - n_i^- = 0  for every i.                         (B)

The same equations hold for every finite linear combination of these singleton tests, and imply vanishing for every chosen subcollection. This is stronger than the whole-tau equation sum_i(n_i^+-n_i^-)=0. It already incorporates the surface-link Galois sets, the intrinsic-subfield argument and boundedness. It would be a false unpaid gap to demand singleton vanishing as new work: the source has paid it.

## 2. Trace the primitive idempotents, not just their number

At each stage the primitive central idempotents identify individual T blocks, even if their Hodge lattices are isomorphic. Thus a block can be followed from its birth to its death, or to the final endpoint. The identity of a block while it is present is fixed by its actual rational subspace under the blowup embeddings. There is no canonical continuation once that block is removed.

Consider the tau blocks. If the initial block survives to the endpoint, there is already a T isometry along that path, but no proof that its surrounding algebraic gluing preserves the cubic h^2 marking. If it dies, its death center is some S_a. The final block, if different, is born from some S_b. Every other complete lifetime starts at a center S_i and ends at a center S_j. Both ends have the same T, so the source's whole-block operation allows them in the same tau class; it does not identify their underlying K3 surfaces.

Let m_ij be the nonnegative number of internal lifetimes born at S_i and removed at S_j. Loops i=j are harmless. The singleton equations become the exact finite incidence system

    e_b - e_a + sum_(i,j) m_ij (e_i-e_j) = 0.               (F)

For a=b this has the familiar balanced solutions. For a != b it also has nonnegative solutions: m_ab=1 and all other m_ij=0 yields

    (e_b-e_a) + (e_a-e_b) = 0.

This is a two-path balance, checked by the 2x2 integer matrix in finite-calculation.json. It demonstrates only that the already-proved counting equations do not imply a=b. It does NOT construct a geometric factorization with these lifetimes, and does not disprove a possible geometric obstruction to such a factorization. No unrestricted realizability of an incidence solution is assumed.

The block algebras Q^m do not eliminate this solution: an internal lifetime may be inserted while the original block is present, the original may then die, and later a final block may be born while the internal lifetime dies. At the level of counts and scalar idempotents all steps have the prescribed add/remove form. Their realization by smooth centers and compatible integral algebraic lattices is exactly extra geometry, not a combinatorial consequence. Restricting to a factorization with no such internal lifetimes would be an additional unjustified hypothesis, so it is not proposed as a substitute theorem.

## 3. Why relabelling the test does not repair the construction

One might try assigning an individual gluing subgroup H to a K3 field and replacing u by a function of H. But the original test is a birational invariant of a field/MRC base, whereas H_X is an embedding of T into the cubic's primitive cohomology. The same K3 field occurs with different categorical embeddings and different choices of the cubic A2 lattice. A choice made using an ambient cubic cannot silently become an invariant of the center's field.

Even if a consistent scalar weight w_i were assigned to every S_i, pairing it with (B) yields zero. Pairing it with (F) gives the identity

    w_b-w_a + sum m_ij(w_i-w_j)=0.

Thus scalar center reweighting alone does not select the endpoint gluing. To extract a new obstruction one would need a stronger, marked transport invariant, with a precise compatibility law for the actual surface links and the auxiliary conic-subfield changes. The source field functions cannot be replaced with rational character sums: the degree-five, degree-six and exceptional r=3 identities concern actual etale sets, including the nontrivial complement involution and residue automorphisms. A decoration must survive those operations too.

The concrete gluing example in Note 02 shows what a proposed transport invariant must distinguish. The four admissible finite subgroups H_19,H_33,H_149,H_163 have identical projected transcendental quadratic module and identical final discriminant form. The sign quotient has two elements. A transport rule that depends only on the T lattice, its determinant, the scalar algebra G, or the total center count has identical input on these two elements. A new rule must carry the embedding information itself and verify condition (G) along the entire zigzag.

## 4. The stabilized-lattice route and its unpaid interface

A second attempt uses all H4, rather than scalar center weights. Every surface blowup adds H2(Z)(-1) as an integral orthogonal summand. By accumulating the local integral isometries, a weak factorization gives a stabilized integral Hodge isometry between the endpoint H4 lattices plus their respective signed collections of center contributions. Source equation (B) pairs the minimal degree-d K3 models S by actual isomorphism class, hence pairs their full integral H2(S) Hodge lattices. The actual smooth centers Z can be point blowups of S: H2(Z)=H2(S) orthogonal-sum <-1>^r. Their shifted contributions therefore include additional <+1>^r diagonal classes, whose numbers are not paired by (B). These classes must remain in the stabilized system. Pairing the minimal K3 H2 parts is nevertheless stronger than merely pairing T lattices and should be retained.

Nevertheless the desired endpoint isometry is not obtained by deleting paired terms from an arbitrary stabilized isometry. One would have to prove that this particular stabilized transport admits cancellation compatible with: (i) the primitive T projector paths, including paths that end and restart; (ii) the algebraic summands from every other center, including diagonal point and curve terms; (iii) the embedding of h^2 at both cubic endpoints; and (iv) the finite discriminant subgroup H. The source provides integral direct sums locally and scalar projectors on T; it does not provide this marked cancellation theorem globally.

No failure of universal integral lattice cancellation is asserted here. The issue is that no applicable cancellation result, with these Hodge and marking constraints and these actual birational transports, has been proved in this packet or supplied by the read primary operations. The finite-module example is not itself a counterexample to marked stable cancellation; it specifies the distinct outcomes whose identification would need proof. Conversely, asserting a canonical cancellation without proving its marking compatibility would simply assume (G).

The rational coefficient extraction in Guere's proof cannot close this step. A rational isomorphism can have arbitrary denominator and determinant; multiplying it to obtain an integral homomorphism generally changes its cokernel and does not establish preservation of a quadratic form. KKPY's read integral-enhancement discussion likewise is not a proved integral gluing-cancellation theorem. The strongest actual partner enumeration treats the gluing as extra data, while the read GM construction proves birational equivalence for specific partner families by additional geometry. None supplies the missing transport uniformly for the rank-two large-admissible situation.

## 5. Decision at the actual interface

No fully specified full-scope nonroutine operation closed. Therefore no theorem has been frozen, no author proof is tendered, and the outcome is PREFREEZE/no nominee.

What is retained is concrete reduction work: the initialized whole-block induction; the exact extension criterion (G); both discriminant congruence cases and gluing indices; the explicit two-orbit quadratic-module calculation; the unbounded admissible arithmetic compatibility check without an effective threshold; the singleton incidence equations (B) and (F); and the stabilized full-cohomology formulation with all required markings. These are feasibility derivations, not a self-assigned contribution grade.

The precise unpaid operation is a geometric integral gluing transport/cancellation law through the actual blowup/Sarkisov construction, compatible with field-level surface corrections and surviving the balanced lifetimes in (F), or another fully constructed invariant accomplishing that distinction. It has not been reduced to a numerical threshold, nor supplied by a catalogue title. No claim is made that this operation is impossible, that all neighboring directions are exhausted, or that the original source needs repair.

The paid headline, classical K3 equivalences, routine very-general transport, the source's Hilbert-square subfamily, and its universal CH0-triviality observations are not nominated. No statement about all members of a divisor, a small/specific cubic, stable irrationality, non-unirationality, effective d0, the necessity direction of the K3 criterion, or new Fano/Torelli consequences follows from these notes.
