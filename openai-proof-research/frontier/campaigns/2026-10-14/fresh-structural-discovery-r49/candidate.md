# A hyperbolic torsion-free group with a one-sided inverse over F₂

Author-side candidate T197H. The full scope is fixed in original-scope.txt. Upstream results at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated. This text proves the additional disk-boundary estimate; it does not audit the upstream probabilistic construction. No independent proof or contribution verdict is claimed.

## Theorem

There exist a finitely presented torsion-free word-hyperbolic group G, a finite two-dimensional classifying complex K(G,1), and finite-support elements a,b,c∈F₂[G] with

    ab=1,    ac=0,    c≠0.

Consequently ba≠1 and G is not sofic.

The group is selected from the matching model in *A Torsion-Free Group Algebra That Is Not Directly Finite*, October4,2026 (source197). The new conclusion is hyperbolicity for a suitably chosen outcome of that model. Neither an executed concrete presentation nor a uniform complexity bound is asserted.

## 1. Exact stipulated inputs and the added obligation

Source197 constructs two finite graphs Γ_A,Γ_B immersed in a fixed finite rose F; Γ is their disjoint union. Each component Λ is coned off along its label map, producing X and G=π₁(X). There are designated roots. The parameter tends to infinity through n=vm with m≡1 mod4; L=floor(c₀ log n) tends to infinity. We use the following results in their stated model.

1. The types have the intersection parities of random.tex, Proposition `prop:types`, for every matching outcome. The girth-conditioned probability space is nonempty for sufficiently large admissible parameters.
2. With probability tending to one all components have diameter at most dL for a fixed d (`prop:diameter`). On this event the short-closure lemma `lem:closure` supplies a fixed D such that every immersed segment can be extended, without cancellation of its original occurrences, to a cyclically immersed closed path by appending at most DL edges.
3. The bounded-path theorem `thm:bounded-patterns` supplies ε₀>0, independent of all fixed K,C,I, such that with probability tending to one there is no system of at most K positive cyclically immersed closed paths with total length H between L and CL, at most I disjoint interval comparisons, at most ε₀H unpaired occurrences, and distinct underlying graph edges at the two ends of every comparison. The theorem also permits one rooted interval, which is not needed in our added disk argument. The rate and parameter threshold may depend on K,C,I.
4. The source's no-arrangements theorem and cone criterion give, with probability tending to one, asphericity of X and protection of the roots. Its parity criterion then gives the displayed a,b,c. In particular the coefficient of the identity in c is one.

The source's spherical exclusion and rooted-interval theorem do not directly concern a null word with no prescribed Γ lift. Our additional obligation is a bound on its ordinary relator area. We retain the exterior boundary as a formal disk, never assign it a Γ lift, and charge all inner occurrences paired with it to its word length.

## 2. A finite presentation and the area cost of a cone boundary

For each finite component Λ choose a root o_Λ and a spanning tree T_Λ. For each oriented non-tree edge e:u→v, choose one orientation and let r_e be the label of the closed path t_u e t_v⁻¹, where t_u,t_v are tree paths from o_Λ. Let P be the presentation with the rose generators and this finite set of relators. It presents π₁(X), since these loops freely generate π₁(Λ) and coning kills exactly their normal closure. This is also the finite cone replacement used in source197's picture lemma.

For any closed path p in Λ, of length h and based at z, its label has P-area at most h. Indeed, t_z p t_z⁻¹ rewrites, in the free group π₁(Λ,o_Λ), as a word in the fundamental loops with one basis-letter occurrence for each traversal of a non-tree edge of p. There are at most h of them. Applying the label map realizes the label of p as a conjugate of a product of at most h relators or their inverses, with free cancellations costing no area. This includes repeated edges, arbitrary starting vertices and either orientation.

A cone picture filling a word w consists of finitely many disjoint inner disks, each with a specified closed boundary lift to a component of Γ, while the complement maps into F. If the sum of inner boundary lengths is H, filling those boundaries by the preceding basis-relator fillings gives

    Area_P(w) ≤ H.                                      (2.1)

This uses the usual gluing of van Kampen fillings through the complementary map to the rose. No minimality or prior isoperimetric estimate is used in (2.1).

Every null word w admits such a picture even when w does not lift to Γ: start with an ordinary van Kampen filling over P, isolate the relator disks, and use their specified fundamental-loop lifts. Equivalently the relative-to-F replacement and picture construction in the source apply with any boundary word in F. The boundary is fixed throughout this construction.

## 3. A reduced picture with an arbitrary fixed boundary

It suffices first to treat a nonempty cyclically reduced null word w. Let B=|w|. Among all cone pictures filling this fixed parametrized boundary choose one minimizing the integer H, the total INNER boundary length. Constant inner disks can be removed, and each remaining inner path is cyclically tightened in its own component; filling through the same contractible abstract cone makes this a permitted replacement. Thus every inner boundary is positive and cyclically immersed. There is at least one: otherwise w would bound in the rose and hence be freely trivial. In particular H≥L.

Cap the exterior formally by one disk; its boundary reads w or w⁻¹ according to the coherent orientation. This disk has no map into X and no Γ lift. In the complementary surface mapping to F, transverse preimages of one interior point of each rose edge give disjoint arcs and circles. Ignore circles. Every boundary-letter occurrence is an endpoint of exactly one arc; its paired occurrence has the inverse signed letter.

Every arc between two INNER occurrences pairs distinct underlying undirected edges of Γ. Otherwise apply a band surgery over their common lifted edge. For two different inner disks, merge them through the band into one disk factoring through the same abstract cone. The two matched traversals contract, lowering H by two before further tightening. For two occurrences on one inner disk, its union with the band is an annulus. In the capped sphere retain the complementary component containing the formal exterior disk, cap its new boundary through the same cone, and remove the exterior disk again. The outer word stays exactly w. The two possible cap lengths together equal the old inner length minus two, and the discarded component's other disks only reduce the retained total. Thus H again decreases by at least two. Both contradict minimality.

These are the inner cases of the source's same-edge surgery, with the minimization changed to fixed outer word and inner length only. No inner–outer surgery is performed, and no graph-edge comparison with an outer occurrence is required. No sphere-essentiality argument or asphericity is used in this reduction.

## 4. The formal-boundary interval lemma

Consider any sphere with N positive cyclically reduced disk-boundary words paired by noncrossing inverse-letter arcs. All but possibly one of the boundaries may have Γ lifts; the lemma does not require any of them. Divide the boundaries into N* consecutive pieces, counting intact boundaries once, and choose an indexing gap on each original boundary. Then all occurrence pairings can be represented by at most 6N* disjoint pairs of intervals, each interval inside one designated piece and avoiding the chosen indexing gaps.

Here is the complete combinatorial justification, following the source's planar-gap argument with its weaker actual hypothesis made explicit. Thicken disks and arcs into a regular disk-and-band neighborhood R. If E is the number of arcs, χ(R)=N−E. For each complementary planar surface Q let ℓ_Q be the number of incident band sides, with multiplicity. Every disk has positive degree, so ℓ_Q≥1. Additivity and counting band sides give

    Σ_Q(ℓ_Q−2χ(Q))=2N−4.                              (4.1)

Call a corner gap good if it lies in a disk digon with two different bands. Its opposite gap is good, and across this digon the two consecutive occurrences are paired in reverse order. Monogons cannot occur: their consecutive paired letters are inverse, contrary to cyclic reduction. A disk digon using the same band twice has a degree-one disk corner; there are at most N such faces, hence at most 2N gaps on them. Every other region has positive contribution to (4.1): a disk of boundary length ℓ≥3 has ℓ≤3(ℓ−2), and a nondisk planar surface has χ≤0 and ℓ≤ℓ−2χ. Thus the total number of nongood gaps is at most

    2N+3(2N−4) ≤ 8N.

This count also covers disconnected arc graphs, loops, parallel bands and nondisk complementary regions. Cut all nongood gaps. Mark the indexing gaps and the piece-division gaps, at most N+N* further gaps. For every marked good gap also cut its opposite. The cut set is stable under the opposite-good-gap involution and has size at most

    8N+2(N+N*) ≤ 12N*.

Every boundary has a cut; maximal remaining runs are intervals inside pieces. Stability of the cuts pairs whole runs in reverse order. A run cannot be paired to itself: odd length would fix its central occurrence, and even length would pair two inverse consecutive letters at its center. Therefore the runs pair in distinct twos, proving the bound 6N*.

This proof uses cyclically reduced WORDS on the formal exterior exactly as on the inner boundaries. Distinct underlying Γ edges are relevant later only to retained inner–inner comparisons, not to this interval count. In particular outer–outer arcs cause no difficulty.

## 5. The boundary-defect filling estimate

Put ε=min(ε₀,1), and let C_sep be the constant in the source's recursive planar-separator lemma. Choose constants in this order:

    U ≥ max{3, ceil(192D/ε)}, an integer;
    η = min{1/(32U), ε/(64U)};
    K = max{1, ceil((C_sep/η)²)};
    C = K(U+D),       I = ceil(192C).                  (5.1)

They are fixed BEFORE the matching parameter tends to infinity. Choose an outcome with girth≥L, the diameter/closure property, source asphericity/root protection, and no forbidden path system for this single triple (K,C,I). Such outcomes exist for all sufficiently large admissible parameters by the stipulated probability-one-asymptotic inputs and a finite union bound. Take L large enough that UL≥6.

We prove that the minimal picture in Section3 satisfies

    H < (32/ε)B.                                      (5.2)

Suppose instead H≥32B/ε. Leave any inner path of length at most UL intact. Divide each longer inner path of length h into ceil(h/(UL)) consecutive pieces with integer lengths differing by at most one; their lengths lie between UL/3 and UL. Close each cut piece by the short-closure lemma. All added occurrences are unpaired. Let N' be the number of inner pieces. Then

    N'L≤H,
    each piece has at most UL original occurrences,
    each closed path has length at most (U+D)L,
    H_add ≤ (3D/U)H ≤ εH/64.                         (5.3)

The first bound uses girth on every intact path and UL/3≥L on every cut segment. There is no exceptional short interval.

Before appending closures apply Section4 to these inner pieces and the ONE intact formal outer disk. It gives at most 6(N'+1) interval pairs. Delete the exterior disk and all pairs meeting it, including outer–outer pairs. At most B inner original occurrences become unpaired; no other inner positions lose a partner in this step. Whole interval pairs are removed, since the cuts respected all pieces and the exterior was one piece. The remaining comparisons are between distinct underlying Γ edges by Section3.

The multigraph on the N' inner pieces given by retained arcs is planar. Splitting a disk into consecutive sectors realizes its pieces without crossings; deleting the exterior vertex preserves planarity. Apply the source's recursive separator to delete at most ηN' piece vertices, leaving clusters of at most K vertices. If M is their total original length, then

    M ≤ ηN'UL ≤ ηUH ≤ εH/64,    M≤H/32.             (5.4)

Retain a pair exactly when both of its pieces remain. At most M surviving occurrences lose a partner; comparisons remain whole interval pairs. For each surviving cluster Z, write H_Z for its total path length including closures, b_Z for its unpaired occurrences, and I_Z for its retained interval comparisons. The preceding bounds imply

    Σ_Z H_Z ≥ H−M ≥ 31H/32;
    Σ_Z b_Z ≤ B+M+H_add ≤ εH/16;
    Σ_Z I_Z ≤ 6(N'+1) ≤ 12H/L;
    H_Z ≤ K(U+D)L = CL.                              (5.5)

The third bound uses H≥L and N'≤H/L. It is independent of the length of the formal exterior boundary. No independence between exposures, pieces or clusters is asserted or required.

Discard clusters with b_Z>εH_Z. They have total length at most H/16. Discard also clusters with I_Z>192H_Z/L. They have total length at most H/16. At least 27H/32>0 of cluster length remains. Every remaining cluster contains a positive cyclically immersed closed path, so has length at least L by girth; no further short-cluster subtraction is needed. It has at most K paths, total length at most CL, at most I comparisons, at most εH_Z≤ε₀H_Z unpaired positions, and all retained paired positions use distinct graph edges. This is precisely a forbidden system from source197. Contradiction proves (5.2).

The constants and the one forbidden class in (5.1) control every finite disk picture simultaneously, regardless of the word length or number of disks. We did not take a probabilistic union bound over null words or over unbounded diagram sizes.

## 6. Hyperbolicity and the scalar witnesses

Combining (2.1) and (5.2) gives Area_P(w)≤(32/ε)|w| for every nonempty cyclically reduced null word. For an arbitrary null word, free reduction and cyclic reduction give a conjugate of a cyclically reduced word v with |v|≤|w|. These reductions and conjugation add no relator cells. If v is empty the area is zero; otherwise apply the bound to v. Thus P is a finite presentation with a linear ordinary Dehn inequality. The standard linear-Dehn characterization implies word-hyperbolicity (for instance the criterion recalled in Gruber, Section2.3 immediately before Theorem2.16).

The selected outcome also satisfies the source cone criterion and its type parities. Consequently X is a finite aspherical two-dimensional complex, G is torsion-free and finitely presented, and source197's parity criterion supplies a,b,c in F₂[G] with ab=1, ac=0 and c≠0. If ba=1, associativity would give c=(ba)c=b(ac)=0, a contradiction. Finally the Elek–Szabó stable-finiteness theorem for group algebras of sofic groups excludes soficity of G. This last implication is already explicitly used in the source and is not an additional contribution. The full frozen theorem follows.

## 7. Dependency and contribution boundary

The probabilistic bounded-path estimate, closure construction, planar separator, cone asphericity, protected roots and scalar parity construction all belong to the stipulated source. Same-lift deletion and conversion from lifted loops to a finite set of ordinary relators have primary antecedents in Ollivier and Gruber. The source itself implements the inner band surgeries used here. The proposed additional operation is the fixed-arbitrary-boundary picture reduction plus the exterior-defect budget in Sections4–5: a formal rose-word disk is included in the interval count, removed before clustering, and its length pays exactly the resulting inner deficit. This is not an invocation of a verified C'(1/6) or Gr(7) condition, and none is claimed for these graphs.

The proof has substantial antecedent overlap; whether the boundary extension passes the campaign's substantial-contribution threshold requires an independent operation-level assessment. The striking nonsofic/hyperbolic consequence alone is not evidence for that gate. Parent author assistance checked the finite-basis area conversion, fixed-boundary inner surgeries and cluster budgets independently of this writeup; it is not an independent review. Exact source/primary reading limits and frozen-scope chronology accompany the packet.
