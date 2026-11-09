# An Euler tour of the full permutation overlap graph that no cyclic word realizes

DRAFT - AI-assisted research manuscript - 5 November 2026

This draft was prepared with OpenAI Codex assistance from the frozen research, review and formal-proof packets identified in the accompanying dossier. No human authorship or affiliation is asserted. The manuscript is submitted for root review; it is not accepted or published. No priority claim is made.

## Abstract
We give an explicit Euler tour of the clustered overlap graph on all permutations of four letters whose cyclic order is not realizable by the windows of any cyclic word over any linearly ordered alphabet. Nine windows force a strict comparison cycle. This refutes Hurlbert's ordering conjecture as stated in Conjecture 6.3 of Kirsch, Sibley and Sprangel [KSS]. The comparison-digraph method is classical: Chung, Diaconis and Graham [CDG] used acyclicity in their construction, and Albert and West [AW] explicitly stated the criterion and printed a nonrealizable Euler tour for a restricted permutation class. The contribution here is the explicit obstruction for the full permutation graph. We explain the distinction, give a direct proof, and describe the supplied Lean endpoints and the limits of the literature screen.

## 1. Setting and the source conjecture
Write S_n for the permutations of [n]. For a tuple a of distinct elements in a linear order, red(a) is its rank permutation: a_i < a_j if and only if red(a)_i < red(a)_j. Equality of reductions is order-isomorphism, written with the symbol ≅. A universal cycle for S_n is a cyclic word whose length-n windows have every type in S_n exactly once. The alphabet size is unrestricted. Symbols may repeat at distant positions, but not within a window.

We reproduce the relevant definitions from [KSS, Section 6.1], using plain typographic notation for their formulas:

> Definition 6.1. “An ordered pair of permutations (σ, τ) ∈ S_n² overlaps by s if σ_{n−s+1} ··· σ_n ≅ τ_1 ··· τ_s. An ordered pair of permutations (σ, τ) overlaps if it overlaps by n − 1.”

> Definition 6.2. “The clustered graph of s-overlapping n-permutations, denoted by O(n, s), is a directed multigraph on vertex set S_s. For each π ∈ S_n, there is a directed edge (red(π_1 ··· π_s), red(π_{n−s+1} ··· π_n)). Thus we identify the edge set with S_n. The clustered graph of overlapping n-permutations, denoted by O(n), is O(n, n − 1), the graph of (n − 1)-overlapping n-permutations.”

> Conjecture 6.3 (Conjecture 3.1.3 in [15], [8] of [KSS]). “Given any Euler tour of the clustered graph of overlapping permutations (i.e., an ordering of S_n such that each consecutive pair of permutations overlaps), there is a universal cycle for permutations that covers S_n in the same order.”

An Euler tour here uses each labelled edge once, including each of any parallel edges, and includes the last-to-first adjacency. Every universal cycle gives such a tour. The converse asserts realizability of every prescribed order, rather than just existence of some cycle. Fixing a starting edge causes no loss, since a realization may be rotated.

===PAGE===
## 2. The explicit full-S₄ Euler tour
Theorem. The cyclic order in Table 1 is an Euler tour of O(4), but no cyclic word over any linearly ordered alphabet realizes its window types in that order. Consequently the all-tour ordering assertion in [KSS, Conjecture 6.3] is false.

Positions and windows below are indexed from zero. Rank labels in the displayed permutations are indexed from one. Table 1 supplies the entire finite Euler certificate: the middle and right columns are the reduced prefix and suffix of length three. Read down the first half, then down the second half, then return to the beginning.

[[TOUR_TABLE]]

Table 1. Each permutation of four letters occurs exactly once. Each suffix column equals the next prefix column, including the closing pair. Thus the table verifies completeness, distinctness and cyclic overlap independently of any proposed word realization.

## 3. The comparison criterion
For a cyclic list t = (p_i) of length L, form a directed graph D(t) on the word positions modulo L. For each window i and offsets a,b with p_i(a) < p_i(b), put an edge (i+a) mod L → (i+b) mod L. Include all strict comparisons, not only adjacent ranks. Multiple copies of an edge may be merged. A self-loop is an obstruction.

Lemma (classical comparison criterion). A finite cyclic list of permutation types is realizable over some finite ordered alphabet if and only if D(t) is acyclic. In particular, a directed cycle obstructs realization over every linear order.

Proof. A realization assigns to every edge u → v the strict inequality x_u < x_v. Following a directed cycle and using transitivity gives x_u < x_u, impossible. Conversely, a finite acyclic directed graph has a topological ordering. Assign distinct increasing integers to its vertices in that order. Every required comparison holds. For two distinct offsets in a window, its permutation orders them in exactly one direction; the corresponding edge therefore forces that order and excludes the reverse. Thus all comparisons, including their converses, agree with the required type. The resulting cyclic word realizes the list. This also handles lists with repeated positions in a window: contradictory identifications yield a self-loop. □

This criterion and restricted-class obstructions are explicit in Albert–West [AW]; the acyclic lifted-order method is already present in [CDG, Section 4]. We use their mechanism, not a new realization criterion.

===PAGE===
## 4. A nine-window obstruction
Suppose x_0,…,x_23 were a cyclic word realizing Table 1. Offsets are counted from zero within each window, and subscripts of x are reduced modulo the word length. Table 2 isolates comparisons forced by the indicated ranks. It is a sufficient subcertificate of the full comparison graph; no search result is needed to infer the contradiction.

[[FORCING_TABLE]]

Table 2. In each row the rank at the first offset is strictly smaller than the rank at the second offset. The final row compares positions 23 and (23+3) mod 24 = 2, so cyclic closure is essential.

Chaining the inequalities gives

x₂ < x₅ < x₈ < x₁₀ < x₁₃ < x₁₅ < x₁₈ < x₂₀ < x₂₃ < x₂.

Transitivity and irreflexivity of strict order yield a contradiction. The finite Euler checks in Table 1 and the comparisons in Table 2 prove the theorem. Increasing the alphabet size or allowing repeated symbols outside individual windows does not remove any of these strict inequalities. Any finite word over a linear order can also be relabelled by the ranks of its finite image, so the finite-alphabet and arbitrary-linear-order interpretations agree for existence.

## 5. Words, cycles and history
The source [KSS] attributes the ordering conjecture to Hurlbert's thesis [H, Conjecture 3.1.3] and [CDG]. We have read the restatement, not the thesis body. In Section 4, [CDG] construct universal cycles by choosing Euler circuits and lifting their comparisons to an acyclic order; they express the belief that this acyclicity holds for any Euler circuit. The displayed tour disproves that belief in the stated generality.

Jackson [J] studied universal cycles for k-subsets and k-permutations, using exact-symbol representations as distinguished in Johnson's introduction. Those representations do not identify the arbitrary order-isomorphic lifting question with existence of an Euler circuit. Johnson [Jo] proves existence of a universal cycle using n+1 symbols. His assertion selects a suitable cycle; it does not assert that every Euler ordering can be realized. The shortened-cycle paper of Kirsch, Lidický, Sibley and Sprangel [KLSS] and the graph-cycle paper [KSS], both from 2022, still discuss the arbitrary-tour question as open.

Remark 6.4 of [KSS] states that every Euler tour, or trail, lifts to a universal word with the same permutation order. The difficulty is closing the cycle: its first and last n−1 symbols may be order-isomorphic without being identical. Our contradiction concerns precisely that identification. The correspondence of [KSS, Section 6.2] associates a graph universal cycle to every Euler tour. Applied to Table 1 it therefore gives a graph universal cycle with a permutation order that no ordinary universal cycle can achieve. This is a consequence of their correspondence and the present witness, not a new graph-cycle construction.

===PAGE===
## 6. Albert–West and the full-graph distinction
Albert and West [AW, p. 41] print the following Euler circuit for the restricted class Av₄(132,213):

1234, 2341, 3412, 4231, 3421, 4321, 4312, 4123.

Here Av₄(132,213) means permutations of length four with no subsequence of type 132 or 213. Their second, fifth and seventh windows, in their one-based notation, force c₂ > c₅ > c₈ > c₂. They explicitly state the comparison-DAG criterion and in fact assert that no Euler tour for this class is realizable. This is direct prior art for both the obstruction method and a concrete nonrealizable permutation-class tour, and must not be described as absent.

It does not by itself settle the conjecture for full S_n. Its edge set is restricted, and its contradiction identifies positions modulo eight. If these edges are placed as a contiguous block in a full tour, the closing identifications of that block are lost: its final windows continue into newly inserted edges, not back into its first positions. One cannot retain the contradictory inequalities merely by retaining the eight edge labels.

The frozen review also tested one natural extension: insert a single residual Euler excursion, containing the other sixteen edges, at a vertex of the printed circuit. All 20,000 seeded trials were valid full-S₄ tours and were realizable. Our fresh recomputation reproduces this outcome. It is a negative experiment for one extension scheme, not a proof that every extension is realizable or that no short derivation from other known examples exists. Table 2 is a different chain involving nine windows in a full tour. This is the concrete step beyond the printed restricted-class obstruction, as adjudicated in the supplied root ruling. We make no claim that the general comparison mechanism is new.

## 7. Exact computations and their limits
The dossier's standalone recompute.py uses only the Python standard library. It reconstructs the full forced-comparison digraph, verifies the explicit cycle, and checks the reduced overlap and permutation coverage of Table 1. The witness digraph has 24 vertices and 72 distinct directed edges. Exhaustive depth-first enumeration of S₃ tours, fixing the increasing edge first to remove cyclic rotation, gives eight tours and no failures. The analogous S₂ check gives one tour and no failures. These finite checks are separate from the proof above.

The discovery generator found its first failure on trial 8,465, with seed 356270, giving one failure in that stopped search. The independent review generator found seven failures in 50,000 trials with seed 20261105. Both use shuffled-adjacency Hierholzer tours; neither samples Euler tours uniformly. The counts are reproducible properties of these scripts and seeds, not estimates of the proportion of all tours. We do not claim exhaustive S₄ coverage. The Albert–West extension experiment uses seed 2009 and likewise does not establish an impossibility theorem.

As a positive control, the [CDG, Section 4] word 123412534153214532413254 has length 24, uses five symbols and realizes its own full-S₄ Euler ordering. All its windows and reduced types are recorded in recomputed.json. The supplied Lean control verifies the same assertion, helping distinguish the refuted all-tour assertion from the true existence assertion.

===PAGE===
## 8. Formal statement and certificate correspondence
The source archive proof-source.zip is reused byte-identically. Its namespace is MathDB356266. Permutation m p means injectivity of p : Fin m → Fin m, hence bijectivity on this finite set. Rank labels are shifted down by one from Table 1. Overlaps compares every strict comparison in the suffix with the corresponding comparison in the next prefix. This is exactly equality of reductions, rather than equality of symbols. The operation next includes the last-to-first step by modular addition.

EulerOrdering t has four clauses: every row is a permutation; t is injective; every permutation occurs; and every cyclic neighboring pair overlaps. In particular this is a tour of the full graph. To see why the length is forced, let P be the subtype of all injective self-maps of Fin (n+1). The map i ↦ (t i, proof of its permutation clause) is injective by the distinctness clause and surjective by the coverage clause. It is therefore a bijection from Fin (N+1) to P. Since P is the set of permutations, N+1 = (n+1)!. This cardinality explanation is a prose bridge; the supplied packet does not assert a separate Lean factorial-length theorem.

position i a is addition of the window offset modulo N+1. Realizes t w states that every strict comparison in each permutation is equivalent to its corresponding word comparison. Under a linear order and the permutation clause, this forces distinct symbols within each window. It permits repeated symbols at distant positions.

Conjecture quantifies over all natural n,N and all t : Fin (N+1) → Fin (n+1) → Fin (n+1). Assuming EulerOrdering t, it asks for some K and w : Fin (N+1) → Fin K satisfying Realizes t w. The use of n+1 covers every positive permutation size; the factorial length is forced as above. There is no fixed alphabet bound. The empty alphabet causes no extra realization since the word domain is nonempty. ConjectureLinear instead asks for some linearly ordered type and a word in that type. Every finite image can be ranked, so this also represents the source interpretation.

The supplied exact endpoints are:

MathDB356266.conjecture_false : ¬ MathDB356266.Conjecture

MathDB356266.conjectureLinear_false : ¬ MathDB356266.ConjectureLinear

Both specialize a supposed universal assertion to n = 3, N = 23, and tour, then apply tour_euler and tour_not_realizable. The latter is the transitive chain of Table 2. The finite Euler certificate is kernel-reduced using decide. The CDG theorems cdg_euler and cdg_realizes give the positive control. The packet includes Hurlbert, Endpoints, Control, Inventory and AllAxioms, plus the module order.

The supplied parent replay receipt reports PASS for strict builds and explicit local leanchecker replays of all modules. Its meta-audit reports no flagged local declarations, and the transitive endpoint axiom sets contain only propext, Classical.choice and Quot.sound. This manuscript lane has not run Lean or any solver: it verifies packet identity, safe extraction and independent finite computations. Reproduction details and the original replay logs are preserved in the dossier.

===PAGE===
## 9. Trust, provenance and bounded significance
The formal replay used Lean 4.34.1 and mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612. It trusts supplied prebuilt upstream dependency oleans: no full source-to-cache attestation or upstream rebuild is claimed. Lean's internal checker replay is not a separate proof-assistant implementation. The mathematical comparison-cycle proof is independently readable without the search, Python or Lean. Hash receipts bind the raw MathDB line, literature bodies, review files, root ruling, formal archive and replay reports. Frozen input hashes are checked before and after manuscript preparation. The byte-identical archive can be safely extracted without executing its contents.

The supplied review and parent registry refresh are evidence of a bounded screen, not global novelty clearance. The parent refresh labels its path screens CLEAN; it does not claim every declaration or manuscript body was read. The available source bodies include [CDG], [AW], [Jo], [KLSS], [KSS] and the related shortening and representation papers described in the review. Hurlbert's thesis body and Jackson's full paper remain unread. The CDG citing-work inventory was screened by title only; those titles do not constitute full-text clearance. Folklore and unindexed prior work cannot be excluded. No network refresh was performed by this manuscript lane; its conclusions depend on the dated receipts supplied with the inputs.

The significance is limited and concrete: a hand-checkable full-permutation Euler order refutes the unrestricted lifting assertion in the read source, using a classical obstruction. The draft does not claim priority, acceptance, or additional credit for the linear-order formulation, control or graph-cycle consequence. Root alone decides acceptance. The earlier independent review's missing-endpoint objection is addressed by the supplied later Endpoints module and parent replay; its prior-art caveats remain part of this manuscript.

## References
[AW] Michael Albert and Julian West. Universal cycles for permutation classes. DMTCS Proceedings AK, FPSAC 2009, 39–50. DOI: 10.46298/dmtcs.2727. Primary source for the comparison criterion and restricted-class obstruction.

[CDG] Fan Chung, Persi Diaconis and Ron Graham. Universal cycles for combinatorial structures. Discrete Mathematics 110 (1992), 43–59. DOI: 10.1016/0012-365X(92)90699-G. See Section 4.

[H] Glenn Howland Hurlbert. Universal cycles: On beyond de Bruijn. Ph.D. thesis, Rutgers University, 1990. Conjecture 3.1.3 as cited in [KSS]; thesis body not inspected.

[J] B. W. Jackson. Universal cycles of k-subsets and k-permutations. Discrete Mathematics 117 (1993), 141–150. Bibliographic identification and representation comparison from read secondary sources; body not inspected. No DOI asserted.

[Jo] J. Robert Johnson. Universal cycles for permutations. Discrete Mathematics 309 (2009), 5264–5270. DOI: 10.1016/j.disc.2007.11.004. Author manuscript arXiv:0710.5611.

[KLSS] Rachel Kirsch, Bernard Lidický, Clare Sibley and Elizabeth Sprangel. Shortened Universal Cycles for Permutations. arXiv:2204.02910, 2022; supplied versions inspected in the upstream review.

[KSS] Rachel Kirsch, Clare Sibley and Elizabeth Sprangel. Graph Universal Cycles: Compression and Connections to Universal Cycles. arXiv:2209.14198v1, 2022. Journal publication DOI: 10.1016/j.aam.2023.102522, verified in supplied citation metadata. Definitions 6.1–6.2, Conjecture 6.3 and Remark 6.4 are the target source.
