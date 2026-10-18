# Source 244: BPI compatibility exploration

Status: pre-freeze exploration, no theorem candidate and no nomination. The full natural question under examination is relative consistency of ZF + PP + BPI + not AC from consistency of ZF. Nothing here proves or refutes that assertion. The pinned source's results are stipulated. Author work is not independent review.

## Precise localized obligation

Ryan-Smith, Local Reflections of Choice, arXiv:2412.13785v3, Proposition 3.13, attributes to Pincus–Blass the equivalence, under SVC(S), between BPI and existence of a fine ultrafilter on the finite subsets of S. Source 244 supplies SVC(A). Thus the actual missing object is a hereditarily symmetric fine ultrafilter on [A]^{<omega}; an ordering of A is insufficient. Indeed A consists of distinct subsets of omega_1 and already has a definable lexicographic linear order. With PP, the SVC presentation gives injections into A times an ordinal, so the ordering principle is already a routine source consequence, not a new target.

## Fixed-order obstruction, with its exact limit

There cannot be a linear order on the ground monoid T invariant under every left translation. By the empty two-copy prescription, choose a,b whose right cones aT,bT are disjoint. On three copies of T prescribe b in copy i followed by x to be identified with a in copy i+1 followed by x (indices modulo three). These prescriptions are valid: within each copy the two involved cones are disjoint, so each equivalence class has at most two members, and no additional overlap or within-copy collapse arises. The source's finite-merger theorem produces l_1,l_2,l_3 with l_i b=l_{i+1}a. If a<b, left invariance produces a strict three-cycle; if b<a the reverse inequalities produce a strict three-cycle. Either contradicts linearity.

This only excludes the strategy of putting a fixed left-invariant ground order on T while retaining the full merger theorem. It does not exclude orders depending on generic labels or on conditions, nor the BPI consistency target. Parent author assistance explicitly emphasized this distinction. Order-compatible amalgamation could evade the cycle, but would need a new verification of the following source steps.

## Exact merger consumers actually read

1. forcing.tex 319–370: local decision uses two independently placed extensions over one root, transported Cohen triggers compatible with a countercondition, and their common diagram extension. Ground permutations need not preserve the fixed generic filter.
2. forcing.tex 372–468 (372–420 read earlier; 420–468 read in this continuation): support descent uses three diagrams v',v'',t with prescribed pairwise intersections equal to the indicated subdiagrams. The two placements of the comparison name agree literally on their entire common supporting diagram. All three diagrams must have a simultaneous extension. The transported Cohen conditions are separately shown compatible. For arbitrary overlap, a third independent copy is placed against a proposed inequality witness.
3. quotients.tex 173–248: the fiber-supply proof uses mu probes with pairwise intersection exactly the root, and their prescribed intersections with every relevant old divisor. Countable Cohen support allows mu many active copies by a ground dense-set argument. Support descent excludes equality of different copied classes and excludes availability at forbidden old subdiagrams. Losing these exact overlaps loses the proof of exact availability ideals, not merely a cosmetic symmetry convention.

These are proof dependencies, not a claim that every alternative PP argument must use full mergers.

## Actual primary BPI criterion

Brian Ransom, On BPI in Symmetric Extensions Part 1, arXiv:2511.21684v1, Definition 6.6 and Theorem 6.8 give a sufficient virtual Ramsey property for arbitrary symmetric systems. The regular-open completion supplies meets when conditions do not have literal unions. For every name for a binary coloring of K/H and every starting condition p, one needs a strengthening q and one color such that every finite family of compatible translates pi q can be simultaneously moved by a common sigma and forced monochromatic by a condition reducible to their meet for the intersection of conjugate H-stabilizers. This reducibility transfers the finite-intersection assertion back to the original orbit conditions. Theorem 6.8 explicitly does not assert necessity of this virtual Ramsey criterion; failure of it would not refute BPI.

Definition 3.8 gives the more direct filter-extension obligation: for every supported FIP family, underlying set and proposed subset, find q and one of the subset/complement so that adjoining the entire K-orbit triggered by q preserves FIP. Lemma 3.9 explains how this fixed-stabilizer step iterates. Source quotient matching only controls sizes and availability, and supplies no such Boolean-coherence argument.

The primary generalized Cohen model is specifically a finite-support product, the group of finite permutations, and finite pointwise stabilizers (Definitions 2.25–2.28). Source 244 instead uses countable Cohen conditions, a separate diagram-forcing coordinate, the full ground permutation group, and supports up to mu. These are substantive interface differences.

## Concrete failure of a direct proof transplant

Ransom Definition 4.6 and the surrounding argument strengthen a condition to distinguish its entire finite support by pairwise incompatible coordinate values. This restricts which translated names can occur together. In source 244 a supporting diagram has mu coordinates, whereas a Cohen condition touches only countably many coordinate indices. Given any Cohen condition d and diagram r, choose two different indices i,j in D_r outside that countable set. Their coordinate restrictions are both empty and hence compatible. Moreover d alone can be extended to force either lexicographic comparison of A_i,A_j by deciding their first bits differently. Therefore the finite-support separation step cannot simply be applied to the entire diagram support. This is a rigorously identified failure of that particular transplant, not a proof that the filter extension property fails.

The finite-arity polarized Ramsey input in primary Lemma 4.3 and finite-type compatibility input Lemma 4.5 also do not state a theorem for mu-sized diagram supports. Increasing the index cardinal alone does not discharge an unstated infinite-support Ramsey assertion. No assertion about its impossibility is made here.

## Remaining full question

A viable proof still needs either (a) a supported fine ultrafilter, with all Boolean decisions coherent across compatible diagram overlaps, or (b) an independent BPI-preserving modification with a complete replacement for source support descent, exact-ideal fiber supply and PP assembly. Neither has been established. A generic-label-dependent order can help separate finitely many labels but does not by itself furnish these interfaces. No frozen target has been weakened to the ordering principle or to an isolated compatibility lemma.

## Finite-fragment test: lexical coloring does not obstruct the criterion

Take two fixed label indices a,b and H fixing them, with H contained in K. Define the name c(pi H) to be the truth value of A_{pi(a)} <lex A_{pi(b)}. It is well-defined on right cosets pi H. Starting with any product condition, strengthen its Cohen coordinate to decide the comparison at a,b, and call the resulting condition q and color c'. For every pi in K, pi q forces the corresponding comparison at pi(a),pi(b) to have the SAME truth value c'. This follows by covariance of the defining formula, not by invariance of a fixed generic filter. For any finite family of compatible pi q, their meet forces all these colors. In Definition 6.6 take sigma equal to the identity and r_delta equal to that meet: the required reducibility is reflexive. Thus this specific coloring satisfies the virtual Ramsey clause. If three diagram copies impose a directed lexical cycle, their strengthened Cohen conditions are incompatible, so that family is outside the quantifier over compatible translates.

The same observation handles any finite covariant formula of the translated generic labels, once q decides its value at the identity coset. It does not handle arbitrary names for colorings of K/H. In the primary proof the coloring is supplied by membership in a chosen OUTER, possibly nonsymmetric ultrafilter. Translating the subset does not translate that ultrafilter. Consequently c(pi H) need not equal the pi-translate of c(H), and the preceding decision argument cannot be used.

Only finitely many translates enter each FIP test. That fact alone does not make the name for the subset finitely supported: each translated name can still use an entire mu-sized diagram, and an arbitrary outer ultrafilter coloring has no established finite-fragment determination. The simultaneous separation of all mu coordinates is therefore NOT asserted to be a necessary condition of the criterion. The failure above only identifies a step in the published finite-support proof that cannot be copied verbatim. A finite-fragment replacement remains a possible genuinely unpaid route; no impossibility result has been obtained.


## Precise remaining step after completing the primary proof read

Ransom Theorem4.9 (text950–1120, now read completely) first finds homogeneous rectangular families of placements of the finite support Y minus the root support. Its terminal step considers arbitrary compatible translates and sets J_i={pi(i): pi in delta}. Full support distinction makes the sets J_i disjoint for DIFFERENT i, not merely makes each J_i finite. This allows one common permutation to shift the entire translated configuration into the homogeneous rectangle, while fixing the root. The proof also uses a support restriction lemma to transfer the outer-ultrafilter finite intersection assertion to the original orbit conditions.

For source244 one could try to replace individual coordinates by whole supporting diagrams as blocks. Compatible diagrams with the same center are indeed identical pointwise (the source's SVC orbit-map argument), so their centers encode whole supported names under compatibility. However distinct diagrams can overlap on principal subdiagrams, with different internal coordinates identified. A sufficient replacement must provide a homogeneous collection of whole-diagram placements universal for every finite compatible principal-cone overlap pattern AND a support-reduction theorem transferring each FIP assertion back to the original meet. No such block Ramsey statement has been proved here. Treating each diagram as a disjoint atomic coordinate would omit precisely the nontrivial overlaps used by PP support descent. Conversely, no argument establishes that finite-fragment refinements cannot supply the missing statement.

## A second failed obstruction: untouched coordinates do not guarantee compatibility

Suppose r and pi r have the same center and admit a common extension t. Write r=t_n and pi r=t_m. Equality of centers says t(n)=t(m); injectivity of t gives n=m, and consequently r=pi r pointwise. Thus a permutation fixing the center but changing the diagram makes the two diagram conditions incompatible, even if their Cohen coordinates are compatible or identical. In particular a transposition of untouched Cohen coordinates cannot automatically be used as an active two-element orbit obstruction: the diagram coordinate can exclude it.

This explains a limitation of the countable-versus-mu support calculation. It is a valid failure of the published coordinate-separation transplant, but it is not evidence that the source has no alternative way of restricting compatible orbit patterns. A parity coloring argument would have to produce, below EVERY strengthening, an actually compatible family of whole product conditions; that quantifier has not been discharged.
