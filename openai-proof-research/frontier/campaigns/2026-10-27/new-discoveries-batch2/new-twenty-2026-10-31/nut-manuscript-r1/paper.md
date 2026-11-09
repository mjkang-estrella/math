# No cubic 8-circulant nut graph: a signed-quotient obstruction

DRAFT - 2 November 2026 (America/Los_Angeles)

AI-assisted research manuscript prepared in the MathDB campaign. No human authorship or affiliation is asserted. This draft awaits root paper review and a complete fresh extracted Lean replay. It has zero accepted campaign credit and makes no priority claim.

## Abstract

We give a computer-assisted nonexistence proof for cubic 8-circulant nut graphs. A cyclic automorphism acts on the one-dimensional real adjacency kernel by a single sign. Restricting to that character gives a symmetric integral matrix of order eight whose kernel lifts injectively to the graph kernel. Cubicity and fullness imply coherent neighbor contributions, absolute row sum three, connected support, and a common sign on every quotient semi-edge. Every such matrix would have determinant zero and all diagonal cofactors nonzero. We reduce the possible supports to a checked catalogue of 194 connected subcubic graphs and the matrices, modulo relabelling and spanning-tree switching, to 9,172 representatives. Exact determinant or zero-cofactor certificates exclude every representative. The Lean endpoint is `Nut8.no_cubic_8circulant_nut : Nut8.Target`. Development compilation and audit, together with independent arithmetic and enumeration checks, support the assembled proof. Final fresh replay is a separate pending acceptance gate in the evidence snapshot used here.

## 1. Statement and scope

All graphs in the theorem are finite, undirected and simple. Write A(G) for the ordinary real adjacency matrix. A vector is full if none of its coordinates is zero. A nut graph is a graph with at least two vertices such that ker A(G) has dimension one and contains a full nonzero vector. Equivalently, every nonzero vector in that kernel is full. Cubic means that every vertex has degree exactly three.

Following Bašić and Damnjanović [1], a graph is l-circulant if it admits a cyclic subgroup of automorphisms with exactly l vertex orbits, all of the same size. The subgroup need not be the full automorphism group. Its generator need not act transitively on vertices. Equal orbit lengths ensure that the subgroup acts semiregularly: each nonidentity group element fixes no vertex.

**Theorem.** There exists no cubic 8-circulant nut graph.

This is Conjecture 16 of arXiv:2411.16904v1 and Conjecture 1 of its published version [1], the target recorded as MathDB 365943. Theorem 2 of [1] excludes l in {1, 2, 4, 5}, and constructs infinitely many cubic l-circulant nut graphs for l in {3, 6, 7} or l at least 9. Consequently the theorem completes that existence classification: existence holds exactly for {3, 6, 7} and all integers at least 9. This does not solve the finer degree-order-orbit problem (Problem 17 of the preprint), which prescribes the orbit size as well.

---PAGE---
## 2. Semiregular coordinates and the kernel character

Suppose for contradiction that G is a cubic nut graph and that a generator sigma has eight equal orbits of size m. The graph is nonempty, so m is positive. Choose representatives r_i, for 0 <= i < 8. The map (i,a) -> sigma^a(r_i), with a in Z/mZ, is a bijection. Distinct representatives lie in distinct orbits, and equality within an orbit occurs exactly when the exponents differ by a multiple of m. Thus sigma acts in these coordinates by (i,a) -> (i,a+1).

For completeness, an element sigma^k fixes one vertex precisely when m divides k. This condition is independent of the vertex, so the common orbit length is also the order of sigma. This proves the asserted semiregularity and justifies taking exponents modulo m. The case m = 1 is included: it represents the identity action on eight vertices, not a family omitted from the theorem.

Let T be pullback by sigma on real vertex functions. Adjacency preservation gives A(G)T = TA(G), by reindexing the neighbor sum. Hence T preserves the one-dimensional kernel. If u is a nonzero full kernel vector, there is a real scalar epsilon with Tu = epsilon u. Since T^m is the identity and u is nonzero, epsilon^m = 1. A real root of unity is a sign: epsilon = 1, or epsilon = -1 and m is even.

Put v_i = u(i,0). Iterating the identity gives

`u(i,a) = epsilon^a v_i,     v_i != 0 for every i.`

There is one epsilon for the whole kernel line. Independent orbit signs cannot be chosen. This elementary representation-theoretic observation is the compatibility needed below; the existence of constant or alternating orbit entries is already familiar in nut-graph theory (see Lemma 5 of [1]).

The character chi(a) = epsilon^a is well-defined on Z/mZ because epsilon^m = 1. It satisfies chi(a+b) = chi(a)chi(b) and chi(-a) = chi(a). The latter identity uses that every character value is 1 or -1. Define the shift set

`S_ij = { b in Z/mZ : (i,0) is adjacent to (j,b) }.`

Translation invariance describes all other adjacency fibers from these sets. Edge reversal yields S_ji = -S_ij; looplessness gives 0 not in S_ii. These are statements about the original simple graph, not additional assumptions about an abstract quotient.

The finite vertex universe in the formal target imposes no extra hypothesis: every ordinary finite graph is representable on Fin n. Likewise, decidable equality and adjacency impose no mathematical restriction on finite graphs. Empty and singleton graphs fail the nut predicate before orbit arguments are used.

---PAGE---
## 3. The symmetric signed quotient and its kernel

Define the integral matrix C of order eight by

`C_ij = sum { chi(b) : b in S_ij }.`

Edge reversal and chi(-b) = chi(b) give C_ij = C_ji. In particular C is symmetric even when epsilon is negative. Evaluating A(G)u = 0 at the representatives gives Cv = 0, where v has every coordinate nonzero.

This alone does not prove that C has nullity one. The missing direction is provided by a lift valid for every real vector w on the eight orbits. Define (Lw)(i,a) = chi(a)w_i. Reindexing neighbors using translation invariance gives the exact identity

`(A(G)Lw)(i,a) = chi(a) (Cw)_i.`

Therefore L maps ker C linearly into ker A(G). Evaluation at a = 0 is a left inverse, so L is injective, including on kernels. Since the graph kernel has dimension one and Cv = 0 with v nonzero, C has nullity exactly one. This rules out any reduction that merely finds a full vector in a larger quotient kernel.

A nut graph is connected. Indeed, if a nontrivial partition into components existed, restrict its full kernel vector to one component and set it to zero elsewhere. No edges cross the partition, so the restricted vector remains in the adjacency kernel. It is nonzero and has a zero coordinate, contrary to the fact that every nonzero vector on that line is full. This cut argument is also used formally and does not assume connectedness in the definition of Nut.

**Cofactor criterion.** For a real symmetric matrix C of order eight, nullity one with a full kernel generator is equivalent to

`det C = 0 and (adj C)_ii != 0 for every i.`

Here (adj C)_ii is the determinant of the principal matrix deleting row and column i. To prove the forward implication without division, suppose that minor is singular. Extend a nonzero vector in its kernel by inserting zero in position i, obtaining x. Then Cx is supported only at i. Pair with the full kernel vector v: symmetry gives v^t Cx = (Cv)^t x = 0. Since v_i is nonzero, the remaining coordinate of Cx is zero. Thus x is a nonzero kernel vector with a zero coordinate, a contradiction.

Conversely, determinant zero and a nonzero order-seven minor imply rank seven. The adjugate is nonzero, its columns lie on the kernel line, and symmetry makes it a nonzero scalar multiple of vv^t for a kernel generator v. Nonzero diagonal entries then imply v_i != 0 for every i. Only the forward implication is needed by the graph reduction. Integer determinants and cofactors agree with their real images, so the necessary condition can be refuted entirely by exact integer arithmetic.

---PAGE---
## 4. Cubicity forces a coherent local grammar

At (i,0), each neighbor (j,b) contributes chi(b)v_j to the kernel equation. Two neighbors in the same orbit cannot carry opposite character signs: their terms would cancel, leaving the third neighbor's value equal to zero. Fullness excludes this. With three neighbors in the same orbit, a sum of three signs is odd and nonzero, so their common nonzero orbit value cannot satisfy the kernel equation either. Consequently each nonempty fiber has coherent character signs, and

`|C_ij| = |S_ij|,     sum_j |C_ij| = 3.`

The off-diagonal support of C is connected. Otherwise a proper nonempty subset of orbit labels would have no nonzero C entry crossing its cut. Coherence identifies a nonzero entry with the presence of an actual edge fiber. The union of those graph orbits would therefore define a nontrivial cut with no graph edge across it, contradicting connectivity of G.

These facts also bound every entry in magnitude by two. If an off-diagonal entry had magnitude three, its endpoints would have no remaining absolute row weight; they would form a component of at most two labels. A diagonal entry of magnitude three would isolate its label. Both contradict connected support on eight labels.

Internal shifts are invariant under b -> -b and do not contain zero. A singleton internal shift therefore satisfies b = -b with b nonzero. In a cyclic group this forces m even and b = m/2. Its character contribution is the SAME sign

`s = epsilon^(m/2)`

at every singleton internal fiber in every orbit. This is the quotient semi-edge. A pair of internal shifts contributes +2 or -2 by coherence and represents a quotient loop. Thus

`C_ii is in {0, 2, -2, s},     s is in {1, -1}.`

When m = 1, no internal shift exists and every diagonal is zero. When m = 2, the sole possible nonzero internal shift is the involution, so each diagonal is zero or epsilon. No exception or lower bound on m is needed. For epsilon = 1 all entries are nonnegative. The formal predicate Admissible records this positivity condition in addition to symmetry, the absolute row sum, entry bound, diagonal alternatives, signs, and connected support.

For enumeration we use a larger class, Structural, that drops only the positivity condition in the trivial-character branch. Formally Structural C s is Admissible C (-1) s. Every graph-derived Admissible matrix lies in this class. It is intentional that not every Structural matrix need arise from a cyclic cover. Excluding a larger class is sufficient, and allows arbitrary vertex-sign switching without incorrectly asserting preservation of entrywise positivity.

---PAGE---
## 5. Complete finite coverage of supports and augmentations

Let H be the simple off-diagonal support graph of a Structural matrix C: distinct i and j are adjacent exactly when C_ij is nonzero. The absolute row sum shows degree at most three, and the cut condition gives connectedness. The support catalogue has, for orders 1 through 8, respectively

`1, 1, 2, 6, 10, 29, 64, 194` representatives.

A list with the right count would not prove coverage. The formal proof instead uses induction with checked extension certificates. For a connected graph of order at least two, take a leaf of a spanning tree. Deleting that vertex leaves the tree on the remaining vertices connected; hence the induced graph there is connected too. Deletion preserves the degree bound. Transport this smaller graph to the inductive catalogue representative.

The removed vertex's neighbor mask is nonempty and has at most three selected vertices. Each selected old vertex has degree strictly below three in the deleted graph because restoring the removed edge raises its degree by one. These are exactly the eligible extension conditions. Conversely, extending a catalogue graph by such a mask describes the original transported graph. Executable bit encodings are connected to actual adjacency by proved no-carry and row-major encoding identities, so the argument is about graphs rather than unchecked codes.

For every eligible extension of each catalogue representative, stored data specifies a target catalogue code and a permutation. The checker verifies that the permutation is a bijection and preserves every adjacency bit. Checker soundness supplies an actual graph isomorphism. There are 1,722 extension witnesses across the seven induction steps, including 1,158 at the final step. Composing the inductive relabelling and checked isomorphism proves coverage for arbitrary connected subcubic graphs on eight vertices. The one-vertex base case is code zero. Redundancy in the catalogue would be harmless to this coverage theorem.

Fix one of the 194 support representatives. Put U_ij = |C_ij|. Every support edge has weight one or two. Choose exactly the subset D of edges whose weight is two. For each vertex i, its diagonal magnitude is forced by the deficit

`U_ii = 3 - sum_(j != i) U_ij.`

Discard negative or oversized deficits. This exhausts the unsigned matrices permitted by the grammar. The formal augmentation theorem recovers the doubled-edge subset from an arbitrary Structural C and proves literal membership in the finite image, rather than relying on a generator's informal completeness.

The resulting enumeration contains 669 unsigned augmentation records. These are not asserted to be 669 nonisomorphic pregraphs; [1] reports 534 after isomorphism reduction. Keeping harmless duplicates avoids an unnecessary isomorphism argument at this stage. The older route's unsigned-kernel pretest is not required: all normalized signed cases are covered below, including those that pretest would already exclude.

---PAGE---
## 6. Switching, enumeration and arithmetic obstruction

For each support, checked tree data provides a root and an ordering with parent p(i) < i for nonroot vertices, after a recorded permutation. Choose vertex signs d_i recursively, starting with d_0 = 1 and choosing d_i so that d_p(i) C_p(i),i d_i is positive. Set C' = DCD, where D is diagonal with entries d_i. Then every parent edge has positive weight one or two. This normalizes doubled edges as well as simple edges.

Because D^2 is the identity, switching preserves nullity and fullness. It also preserves absolute entries, support, diagonal entries, determinant and each diagonal cofactor: every determinant factor from the deleted diagonal matrix is squared. Relabelling permutes cofactors and preserves determinant. These identities transport an obstruction for a normalized representative back to the original matrix. Only Structural invariance is needed, as explained in Section 4.

For a fixed unsigned augmentation U and ordered tree, the free sign slots are the non-tree support edges and the diagonals of magnitude two. A doubled off-tree edge has one sign slot, not two independent signs. Diagonals of magnitude one all receive the single sign s; zero diagonals have no sign. Let E be the subset of free slots chosen negative. Giving negative slots value -U_ij and all other entries value U_ij, with magnitude-one diagonals replaced by s, reconstructs every normalized Structural matrix. Symmetry uses one shared slot per unordered off-diagonal edge.

SignedEnumeration proves this image-membership statement. Per-support finite-image equalities then connect those same labelled matrices and trees to the regenerated certificate lists. This matters because an older batch used different support labels and normalization trees: equality of raw matrices cannot be inferred merely from equality up to permutation and switching. The final packet uses certificates regenerated in the required labels.

The checked enumeration has 9,172 normalized matrices. The obstruction split is

`8,208 certificates det C = k with k != 0;`

`964 certificates (adj C)_ii = 0 for a specified i.`

Either certificate contradicts the necessary cofactor condition of Section 3. The sparse dimension-indexed Laplace evaluator in VerifiedDet is proved equal to Matrix.det in every dimension; a separate specialization identifies the principal cofactor. Its evaluated equalities are kernel-reduced proofs, not numerical approximations, external-solver assertions or native oracle results. The regenerated matrix certificates are distributed over 287 modules and assembled into 194 per-support bundles.

Now start with a hypothetical graph. Sections 2-4 produce an Admissible matrix satisfying the cofactor condition. Catalogue coverage relabels its Structural support to one of the 194 codes. Augmentation and switching put it in a finite signed image. Its certificate excludes the cofactor condition, and invariance transports the contradiction back. This proves the theorem for all positive orbit sizes, without enumerating voltage assignments or bounding graph order.

---PAGE---
## 7. Formal statement correspondence and source fixes

The proof is written in Lean 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52, against mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612. The table states the role of each named interface; declarations are in namespace Nut8. Exact types and bodies are in the byte-identical source packet.

| Declaration | Mathematical role |
| Cubic | Every vertex has degree exactly three. |
| Nut | At least two vertices; real kernel dimension one; full nonzero kernel vector. |
| Circulant | One automorphism, exactly l integer-power orbits, equal sizes. |
| cyclicGroupCirculant_iff | Equivalence with a literal cyclic subgroup preserving adjacency. |
| Target | For every finite simple graph, not (Cubic and Nut and Circulant 8). |
| Admissible | The signed symmetric quotient grammar of Section 4. |
| FiniteObstruction | Every Admissible matrix fails the determinant/cofactor condition. |
| Coverage8 | Every Structural support relabels onto a catalogue code. |
| PerSupport | Every Structural matrix on a catalogue code fails that condition. |
| finite_of_parts | Coverage8 and PerSupport imply FiniteObstruction. |
| nut8_target | Applies coverage8 and the graph bridge, conditional only on PerSupport. |
| no_cubic_8circulant_nut | Unconditional assembly: nut8_target per_support. |

GlobalLabel constructs the semiregular bijection. QuotientExtraction and KernelLift derive the actual signed quotient, kernel identities and injection. NutConnected and the counting/diagonal modules prove its grammar. FullCofactor and MatrixExtraction prove the necessary determinant/cofactor condition and integer transfer. CatalogueInduction and Coverage8 establish support coverage; augmentation, ordered switching, SignedEnumeration, finite support bundles and PerSupport finish the finite obstruction. Auditors are outside the endpoint import closure.

Six documented compilation fixes distinguish the final r7q sources from their inherited versions. In FiniteSupport162, FiniteSupport163, FiniteSupport164, FiniteSupport165 and FiniteSupport166, maxRecDepth was raised from 4096 to 8192 after strict recursion-depth failures. Only the elaboration limit changes; theorem statements and certificate branches are unchanged. In PerSupport, an unused List.mem_singleton simplification was replaced by List.mem_nil_iff and or_false, discharging a remaining empty-list membership disjunct. This repairs simplification and strict warning handling, without changing the 194 branches or endpoint type.

source-fixes.json records each failure receipt, passing receipt and before/after hash. The fixed NutInterface and all r6p sources remain byte-identical. Historical module comments may describe partial milestones; the final assembly and its actual declared type determine what is claimed. In particular Target itself is a proposition definition, while Nut8Final supplies its proof. No mathematical bridge remains as a premise of that final theorem.

---PAGE---
## 8. Verification evidence, scale and trust limits

The proof packet is exactly nut-r7q-source.zip, renamed nut-source-only.zip without changing bytes. Its SHA-256 is

`e4710a538ed6ef60e6649fcb288dd873db52ce613eeddca564627f39c96ef402`.

The endpoint import closure contains 1,024 local modules. The replay driver schedules 1,151 unified local modules, including inherited material beyond that closure. It performs a strict rebuild with warnings as errors, a separate leanchecker process for every scheduled module, 128 final audit shards, and 18 negative controls. Thus replay comprises more than 2,400 sequential steps; it is a substantial kernel-computation artifact rather than a short theorem import.

The inherited development validation reports endpoint leanchecker success, all 128 audit shards and all 18 negative controls passing. The audit has 46,045 records over 46,022 distinct printed declaration names. The generated companion Nut8.unsignedPatterns.eq_1 appears 24 times across shards, accounting for the excess 23 records. This is not 46,045 distinct declarations. Module, full type, opaque-accessible body, unsafe/partial/axiom flags and transitive axioms were inspected. The allowed axioms are exactly propext, Classical.choice and Quot.sound. No audit module occurs in the proof closure.

The independent reviewer [8] reproduced support counts by its own vertex extension, WL buckets and exact VF2 isomorphism, and found exact catalogue coverage up to isomorphism. A second enumeration recovered 669 unsigned augmentations and exact set equality for all 9,172 signed certificate matrices. Integer Bareiss elimination checked all 8,208 determinant equalities and 964 zero principal-cofactor equalities. These checks corroborate both completeness and arithmetic; they do not replace the kernel proofs. Three independent strict spot compilations passed for FullCofactor, SignedEnumeration and Nut8Final using inherited imported objects, with endpoint axioms exactly as above. Those are not a fresh closure rebuild.

The r7q snapshot explicitly reports only 12 of 1,151 strict builds completed in its corrected fresh-final extraction; later phases there were pending. The root is separately running the decisive replay in nut-parent-final-r1. This manuscript lane does NOT run that full replay or claim its PASS. The dossier's local extraction/manifest replay verifies paths, hashes and source policy only. Development PASS, extraction PASS and final Lean replay PASS are distinct claims. Root must supply the last before acceptance.

Per-process replay limits are two CPU affinity slots, 120 CPU seconds, 140 wall seconds, sampled private RSS at most 5.75 GiB and MALLOC_ARENA_MAX=2. Its driver resumes only after checking source and prior output hashes, refuses existing objects at initialization and unrecorded objects on resume, and saves unique logs and receipts. Trust includes Lean's kernel and executable, pinned library sources, integer arithmetic implementation, hardware, and integrity of the delivered bytes. Python enumeration and PDF generation are outside the logical trust base. A successful replay still does not establish novelty, source interpretation or freedom from hardware faults by itself.

---PAGE---
## 9. Relation to the source method and bounded prior work

Section 3 of [1] tests an unsigned quotient pregraph first, then permits arbitrary row signs in a matrix B with |B| equal to the unsigned adjacency matrix. Proposition 7 requires a positive vector in its right kernel and explicitly does not require B to be symmetric. The supplementary resolver [2] fixes the first nonzero entry of each row positive and uses an ILP to seek positive kernel combinations. This is a necessary local-magnitude test, with more freedom than a single global kernel character permits.

Our quotient keeps orbit representative values with their signs, obtains symmetry from edge reversal, and obtains exact nullity one from an injective lift. Most decisively, every involution/semi-edge has the same character sign. Tree switching preserves this common diagonal sign. These compatibility conditions permit the finite obstruction even though the source's weaker test left the eight-orbit case unresolved. This proof does not claim to invent cyclic characters, voltage graphs, switching or determinant certificates.

The published primary body of [1], dated 6 May 2025, retains the conjecture. The cached 2025 arbitrary-automorphism-group paper [3] constructs nut graphs with prescribed full groups, with its regular construction in degrees 8, 12, 16, 20 and 24. The 2026 orbit paper [4] concerns orbit counts of the full automorphism group without the cubic equal-orbit cyclic-subgroup restriction. The vertex-transitive order-degree classification [5] addresses even degrees and transitive/Cayley graphs. These hypotheses do not subsume the present question. The review also read v1 bodies on regular degree existence and quartic bicirculants, and the October 2026 body on bipartite edge frustration [6]; none supplied this nonexistence result.

Coverage is bounded. The Nut digraphs body was denied at its repository route and was not read; later degree/quartic versions and the final published degree body were not independently cleared. The citing-work inventory is incomplete. No denied routes were retried for this dossier. Root's adjudication [8] records complete current Omega D5 and Problems path trees at head 287b9c7da167e412b2ef577dceab38130f9a348b, with no target regex hits; a path screen is not a full-body proof search. The review's OpenAI/math head was 4eaee87548250b2682affda7d05d947c05554bae. These are dated inherited observations, not a new live screen by this manuscript lane. Acceptance requires root's registry refresh and judgment of the retained limits. We make no priority claim.

The cached MathDB record links arXiv:1808.08747 as a companion. Its actual primary abstract concerns Hadamard full propelinear codes. This is unrelated metadata; it is not related work, and no 2018 origin for the conjecture is inferred from it. The original raw line is retained unchanged, alongside this correction.

---PAGE---
## References and reproducibility notes

[1] Nino Bašić and Ivan Damnjanović. On cubic polycirculant nut graphs. arXiv:2411.16904v1, 25 November 2024. Published in Computational and Applied Mathematics (2025), DOI: 10.1007/s40314-025-03218-7. Primary preprint body and cached published body read; theorem labels differ as stated in Section 1.

[2] Nino Bašić and Ivan Damnjanović. On cubic polycirculant nut graphs: supplementary material. https://github.com/nbasic/cubic-polycirculant-nuts, snapshot a135cda6d294bef865045675ec60e0c992c87b48. The cached nuts-resolver.py was read, including the row-sign construction and ILP.

[3] Nino Bašić and Patrick W. Fowler. Nut graphs with a given automorphism group. Journal of Algebraic Combinatorics (2025). DOI: 10.1007/s10801-025-01389-4. Cached primary theorem body read; this is not a cubic eight-orbit classification.

[4] Nino Bašić and Ivan Damnjanović. Nut graphs with a prescribed number of vertex and edge orbits. Journal of Algebraic Combinatorics (2026). DOI: 10.1007/s10801-025-01492-6. Cached primary body read, particularly Theorems 5-6.

[5] Ivan Damnjanović. Vertex-transitive nut graph order-degree existence problem. arXiv:2507.02481; cached v3 and published primary body at https://dmtcs.episciences.org/17258/pdf considered in the inherited investigations. Scope comparison concerns vertex-transitive and Cayley graphs.

[6] Primary-body locators in the independent review: On the degrees of regular nut graphs, arXiv:2410.14063v1; Classification of quartic bicirculant nut graphs, arXiv:2502.06353v1; Bipartite edge frustration of nut graphs: proofs and constructions, arXiv:2610.15679v1. These locators identify the precise inspected versions; later-version clearance is not asserted. Copies, titles and retrieval receipts are in evidence/nut-review-r1/public.

[7] Irene Sciriha and Ivan Gutman. Nut graphs: maximally extending cores. Utilitas Mathematica 54 (1998), 257-272. Bibliographic background cited through [1]; its full body was not independently inspected for this draft. No theorem here is delegated to an unread body.

[8] MathDB campaign, internal artifacts (2026): nut-review-r1/REVIEW.md and review.json; nut-root-adjudication-r1.json; nut-formal-r7q source and validation records. These are internal evidence, not public publications or independent priority certifications. The review is independent of the candidate's generator, but part of the same research campaign.

**Dossier map.** paper.md is the editable manuscript source; build_paper.py renders the PDF. PROOF.md gives a continuous ordinary proof without the evidence discussion. sources/365943-raw-0.jsonl preserves the exact raw MathDB line. evidence/ contains copied source bodies, receipts, milestone summaries, review and adjudication records. nut-source-only.zip is the byte-identical Lean proof packet. REPRODUCE.md explains its resumable replay and the distinction between source extraction checks and the full kernel replay. The manifests bind dossier files and frozen external inputs; verification receipts document safe extraction, hash comparison and policy scanning. No modules were rebuilt or edited in this manuscript lane.

The manuscript and dossier remain drafts. Root alone reviews the paper, reconciles the final replay and novelty limits, and determines acceptance. Neither the theorem statement nor the campaign's current count is a license to relabel an incomplete validation phase as a completed replay.
