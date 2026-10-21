# Nonresolvable design substitution: integrated feasibility calculation

PREFREEZE / no nominee. These are supporting feasibility calculations, not a frozen theorem, full LR proof, independent grade, acceptance, or count. Original prose CC BY4.0; original code MIT. Source, primary and history bodies remain private under their original rights.

## Full question and credited inputs

The actual old LR target is unchanged: there exist an integer r>=2, finite disjoint parts V_1,...,V_r, and a nonempty SET E of edges, each meeting every part exactly once, such that EVERY two distinct edges meet in EXACTLY one vertex and EVERY vertex set of size<=r-1 misses an edge. There is no bound on rank, field, degree, side size or construction. A universal negative answer would have to cover all such hypergraphs. This round neither weakens LR to a bounded-intersection variant nor presents a restricted construction obstruction as its solution.

Pinned Source162 supplies nonlinear intersecting examples with tau=r, including balanced prime-order examples. Its deterministic merge/split proof establishes intersection and excludes every mixed cover; its extension companion separately uses exceptional configurations and a weighted line/point budget. Both already supply monochromatic-component transfers. The source truth and operative operations are stipulated. Their all-cover estimates depend on their actual partitions/label maps; they cannot simply be transferred to a new linear design after arbitrary changes.

Actual r15 proves that the balanced source has no intersection-preserving linear refinement or edge-surjective part-preserving lift. Its proof uses connectivity of unique-agreement pairs on retained nonsplit lines and the consequent forced double agreement. Actual r2 proves a synchronized TD inflation has cover<=m*c_master<R, even for mixed classes, and its separate K4 pencil trade retains private labels. All those proofs and full targets remain unchanged. The present calculation avoids assuming local resolutions: it allows nonresolvable TD ingredients and arbitrary global regrouping. It is still the same full LR question, not a newly named conjecture.

Primary FHMW, arXiv:1508.00951v3, Lemmas2.1--2.2 and Theorem2.3, already pay minimum-degree, side-size and incidence-count restrictions. Stinson, arXiv:2403.17602v1, Construction1.1 and Theorems2.1/2.4, pay weighted GDD substitution and assembly of a parallel class from locally disjoint blocks. His Lemma2.5 explicitly allows TD(m+1,m), with no two disjoint blocks. Thus failure of a naive locally resolvable inflation is not evidence against nonsynchronized assembly. The field-reduction spread construction below is also classical, with an actual proof in Lavrauw--Van de Voorde, arXiv:1310.8522v2, Lemmas2.1--2.2 and Theorem2.3.

## 1. Exact object and the two independent obligations

Let X be a finite nonempty set with R>=2 partitions. Label every block by its partition, even if equal singleton sets occur in different partitions. If each distinct pair x,y belongs to exactly one common block across the partitions, their dual edges are distinct, R-partite, R-uniform and linear intersecting. Conversely, the parts of any LR object give exactly these partitions of its edge set. Selecting vertices in the dual is precisely selecting blocks covering X. This classical duality preserves all mixed covers.

For a pairwise balanced block system on X in which every point has replication R, a proper R-coloring of the block-intersection graph is exactly a resolution into R partitions. Every point lies in an R-clique, so each color occurs there once. Conversely disjoint blocks in every resolution class give such a coloring. Thus constructing the uncolored pairwise design is only one step. One still needs BOTH a resolution and block-cover number R. Its R incident blocks at any point always cover X, so the unpaid cover direction is the lower bound against every R-1 blocks.

## 2. Substitution without local resolutions

Take a master PBD on a set Z of size v, every point in exactly a blocks, every master block having size at least two. Replace z by a disjoint fiber F_z of m>=2 points. In each master block B place an actual TD(|B|,m): its blocks meet every fiber indexed by B once, and each pair from distinct fibers occurs once. Arbitrary choices of ingredients and arbitrary bijections with the fibers are allowed; there is no common-coordinate or local-resolution hypothesis.

In each F_z place an internal PBD D_z with replication b>=1, the same b for all fibers. Internal singleton block labels, if any, are retained with their incidences, though they immediately obstruct LR after a resolution by FHMW Lemma2.1. The examples below have no singleton blocks.

A different-fiber pair projects to one master block and hence occurs in exactly one ingredient block. A same-fiber pair occurs once internally and nowhere else. A TD(k,m), k>=2, has m^2 blocks and replication m: fix another group and count the m partners of a specified point. Hence output replication and total block count are exactly

    R = ma+b,
    B_out = m^2 B_M + sum_z I_z,                              (1)

where B_M is the number of master blocks and I_z counts internal blocks. This proof needs no design-existence theorem beyond the stated actual ingredients. It is the direct pair-counting content of Wilson substitution.

For any hypothesized global resolution, the class sizes sum to B_out. If B_out<R^2, at least one class has at most R-1 blocks and is a cover. Thus

    m^2 B_M + sum_z I_z >= (ma+b)^2                          (2)

is necessary for an LR witness from this construction. Reassigning colors cannot change it. It is a classical side-size/incidence budget, not evidence of a new substantial operation.

For example, suppose the master is a uniform 2-(v,k,1) design with replication a and the internal block is the whole fiber (b=1). Then v=a(k-1)+1 and B_M=va/k. TD(k,m) existence implies k<=m+1: a TD block meets k(m-1) other blocks, all distinct, among only m^2-1 others. Substitution in (1) gives

    B_out - (ma+1)^2
      = a[(k-1)-2m-m^2(a-1)/k] < 0.                         (3)

The inequality uses k-1<=m, a>=1. Thus every such uniform-master/whole-fiber model fails the LR cover requirement if resolved, even with nonresolvable ingredients and completely arbitrary global resolution. This includes affine and projective masters and is stronger than assuming synchronized local resolutions. It remains only a restricted elementary screen.

## 3. Covers that survive arbitrary global rescheduling

Fix z in Z and x in F_z. For each of the a master blocks B through z, select the m TD blocks through x. Those m blocks cover every point of every other fiber belonging to B, because each pairs with x exactly once. The master blocks through z partition Z minus{z} after deleting z. The selected ma cross blocks therefore cover exactly

    X minus (F_z minus{x}).

Write c_z(A) for the least number of internal blocks covering A subset F_z, with c_z(empty)=0. It follows that, without any resolution assumption,

    c_output <= ma + c_z(F_z minus{x}).                     (4)

The b internal blocks through x cover the whole fiber, so c_z(F_z minus{x})<=b. If ANY z,x admits c_z(F_z minus{x})<=b-1, (4) is already an (R-1)-cover. An internal candidate must retain the full residual cover obstruction for every x. Large degrees or large total block count do not provide that obstruction.

This eliminates an instructive integer-feasible test. Take a projective master of order13, local TD(14,13), and internal Steiner triple systems on13 points. Then a=14,b=6,R=188,v=183,|X|=2379. There are30927 cross blocks and4758 internal triples, total35685>188^2. Class margins alone even allow157 classes with165 cross+23 internal blocks and31 with162 cross+37 internal blocks. These numbers are not a realized resolution.

Every STS(13) has a cover by at most five triples. To see this, every triple meets15 other triples. Choose two disjoint triples; they exist because there are26 triples and only16 meeting a fixed triple including itself. Exactly nine triples meet both: the nine cross pairs determine distinct triples, since a triple containing two points of either original would repeat an already used pair. Consequently the two chosen triples and their intersecting neighbors occupy2+15+15-9=23 triples. There is a third triple disjoint from both. Their union has nine points; pair the four remaining points and use their two containing triples. This gives at most five triples. Thus (4) gives a187-cover, regardless of the local identifications or any resolution. The finite diagnostic supplies one explicit cyclic STS(13) illustration; the preceding proof covers every STS(13).

More generally one can lift a master block cover using arbitrary actual local TD covers, with a cost attached to each master block. Locally disjoint blocks from Stinson's theorem are compatible with such covers; they cannot be dismissed because a full local resolution is absent. The old m-fold cover is the special case of local cover size m. For general local TDs, a star at one group point plus one block for each of the other m-1 points in that group gives a cover of size at most2m-1. This is an upper bound available in the integrated optimization, not a sufficient LR obstruction for all parameter choices.

## 4. Coherent projective geometry has an additional small cover

Let m be a prime power. Take PG(3,m), remove a point P, and let the fibers be the m surviving points on each line through P. The master is the quotient PG(2,m), with v=m^2+m+1 points and replication a=m+1. Each plane through P supplies its m^2 lines not through P, an actual TD(m+1,m) on the m+1 fibers in that plane. Every line avoiding P belongs to exactly one such plane. Local TDs here have no two disjoint blocks inside their plane; nevertheless a compatible GLOBAL cover is available.

There is a line spread of PG(3,m). For completeness, regard F_(m^2)^2 as a four-dimensional vector space over F_m. Its one-dimensional F_(m^2)-subspaces are two-dimensional F_m-subspaces, with pairwise intersection{0}, and partition all nonzero vectors. Projectivizing yields m^2+1 disjoint projective lines covering all points. Exactly one contains P. The other m^2 lines are cross blocks and cover every point outside the corresponding fiber. Fill that fiber using its b internal blocks through one point. For arbitrary internal PBDs of replication b, the resulting cover has size

    m^2+b < m^2+m+b = R.                                    (5)

This directly defeats the coherent PG(3,m) realization, even when every internal fiber has residual cover number b and even when total block counts pass. No resolution, global parallelism theorem, or randomized argument is needed for (5). This is a classical field-reduction operation composed with an internal star, not a nominee.

Independently changing local TD identifications can destroy this PARTICULAR spread's compatibility, but failure of that spread does not exclude other spreads, partial classes, or mixed covers. Conversely, the projective geometry does not automatically provide a resolution after those changes. Both obligations remain to be proved on the same resulting object.

## 5. What an arbitrary resolution would have to do

Still take the projective master of order m and TD(m+1,m) ingredients, with arbitrary identifications. Assume internal blocks have size at least delta>=2. Each local TD has pairwise intersecting blocks, so any global resolution class can use at most one cross block from each master line. Let S be its selected master lines and T the complement, t=|T|. If d_S(z) lines of S pass through z, their selected blocks use d_S(z) distinct points in F_z. Internal blocks of that class must partition the remaining

    h_z=m-d_S(z)=d_T(z)-1                                  (6)

points. In particular T covers the entire projective master, and h_z is either zero or at least delta. This is stronger than separately counting available colors: literal internal blocks must fill these particular holes.

If the class has j internal blocks, summing holes gives

    sum_z h_z=(m+1)t-v,
    |class|=v-t+j,
    j<=((m+1)t-v)/delta.                                   (7)

If T contains a full pencil at z and exactly s additional lines, none through z, then either s=0 or

    s>=1+(m+1)(delta-1).                                   (8)

Indeed, on any extra line, every point is distinct from z and has positive hole size equal to its number of incident extra lines. This number is at least delta by (6). Its m+1 points therefore require at least(m+1)(delta-1) incidences with other extra lines. Every other extra line contributes exactly one, proving (8). If s=0, the class consists of m^2 cross blocks plus an internal partition of one fiber; its size is at most m^2+floor(m/delta)<R. So a witness cannot use that class.

Across all R classes each master line is selected exactly m^2 times (once for each of its local blocks). Hence

    sum_classes |T| = v(R-m^2)=v(m+b).                     (9)

Equations(6)--(9) retain the simultaneous local-hole and global color budget. They are necessary conditions, not sufficiency, a design-existence theorem, a complete covering classification, or a new frozen bridge. I have not proved they are inconsistent for all admissible internal designs; restricted projective-plane point sets can vary internal block counts and avoid the simple uniform screens. I have not constructed a realization satisfying them either.

## 6. Exact remaining mixed-cover problem

For arbitrary selected subsets C_B of local cross blocks, let A_z be their union of used points in F_z. Since every output block is either cross or internal, its block-cover number is exactly

    min_(C_B) [sum_B |C_B| + sum_z c_z(F_z minus A_z)].       (10)

This identity includes the local parallel-class, partial-class, weighted master-cover, residual-star and coherent-spread operations above. It does not discard a compatible operation merely because a factorized construction failed. The internal costs couple all incident master blocks at each fiber. A count or independent local lower bound cannot replace their simultaneous minimization.

Even fractional information leaves a genuine rounding issue. For the projective master, uniform weight1/[m(m+1)] on cross blocks alone covers every point fractionally and has cost

    |X|/(m+1)=m^2 + m/(m+1).

It is optimal for the cross-only fractional problem, by assigning weight1/(m+1) to every point. Since internal block sizes are at most m, the same dual is feasible after adding internal blocks, so it is also the full fractional optimum. The integral R=m^2+m+b cover budget is therefore only m+b-m/(m+1) above the fractional value. This gap is not paid merely by fractional duality, nor is it a lower bound against a compatible integral construction. No near-integral rounding theorem at the needed scale has been proved here.

The unpaid operation is to produce ONE actual finite object with both an R-class resolution and value R in(10), or to supply a different full LR construction; alternatively a universal cover theorem would settle the full opposite direction. No such operation emerged. The source's nonlinear cover rigidity does not supply the new linear resolution, and the old refinement obstruction prevents simply pushing the source cover estimate through a part-preserving lift. Classical substitution, partial-class assembly, incidence counts and spreads account for the calculations presented here. Their length or their more flexible hypotheses are not substantial-contribution evidence.

No source truth audit, full LR witness, universal refutation, independently assigned correctness/contribution grade, scope replacement, priority/current-open claim, exhaustive-search certificate, freeze or acceptance/count change is made. H138/T185R144 and every protected full/technical/failed scope remain unchanged.

Late source-detail reading, after the preceding extended calculation was drafted: the full balanced selection.tex proof and elementary.tex appendix were read. The source's selector already supplies independent transversals, cylinder bounds, occupancy and a conditioned local-lemma completion; all are credited. Its actual graph hypotheses include n=2(q+1) slots, slot sizes Theta(q), maximum degree O(q), local degree at most q^(1/8), and bounded exceptional codegrees, with extra line-injectivity hypotheses for occupancy. No encoding of all output block colors and all fiber-hole partitions satisfying these hypotheses while preserving the lower bound in(10) was produced here. The source operation is available if those interfaces can be supplied; the failed geometric realization does not rule out such an encoding. This is a late compatibility read, not backdated pre-drafting coverage or a proof that selection methods cannot work.
