# A vertex of the asymmetric subtour elimination polytope on eight nodes that is adjacent to no tour

!STATUS DRAFT, not peer reviewed. AI-assisted: the counterexample search, the Lean formalisation, an independent review and this text were produced by instances of the language model Claude Opus 5.5 working in an AI-run research workflow. No human authorship is claimed, and no priority claim is made. MathDB record 368807. Version of 2 November 2026.

## Abstract

Vercesi, Barta, Gambardella, Gualandi and Mastrolilli conjectured, on the basis of computations for n ≤ 6, that every vertex of the asymmetric subtour elimination polytope P<super>n</super><sub>ASEP</sub> has a tour among its neighbours in the vertex–edge graph (arXiv:2506.10671, Conjecture 1). We give an explicit fractional vertex x* = X/4 of P<super>8</super><sub>ASEP</sub>, with 19 support arcs and 8 tight subtour constraints, such that no tour is adjacent to it. For each of the 5040 tours T, an integer direction certificate shows that the segment [x*, T] is not a face. Hence Conjecture 1 is false. The result and all definitions are checked in Lean 4 with mathlib, against a literal statement of the source's polytope on the arc space ℝ<super>A</super>. The proof uses only the axioms propext, Classical.choice and Quot.sound. The case n = 7 remains open.

## 1. Introduction

Let K<sub>n</sub> = (V, A) be the complete digraph on n nodes. The subtour elimination (ASEP) polytope P<super>n</super><sub>ASEP</sub> is the feasible region of the Dantzig–Fulkerson–Johnson relaxation of the asymmetric travelling salesman problem. Its integral vertices are exactly the tours: the incidence vectors of directed Hamiltonian cycles. In [1] the authors study the vertices of P<super>n</super><sub>ASEP</sub> for small n through their orbits under relabelling of the nodes.

They enumerated all vertices for n = 4 and n = 5, and explored neighbourhoods partially for n = 6. From these preliminary tests they state:

!QUOTE Conjecture 1 ([1], p. 14). For each x vertex, N(x) contains at least one tour.

Their motivation is that, if the conjecture were true, "solely pivoting on an integer vertex would lead to the full V-description of the polytope". Lemma 7 of [1] shows that relabelling nodes preserves adjacency, so the neighbourhood of one tour would contain a representative of every orbit.

!THEOREM Theorem 1. The point x* = X/4, with X the integer matrix in (3.1) below, is a fractional vertex of P<super>8</super><sub>ASEP</sub>. For every tour T on the nodes {0, …, 7}, the segment [x*, T] is not a face of P<super>8</super><sub>ASEP</sub>. In particular N(x*) contains no tour, and Conjecture 1 is false.

The proof is elementary but finite. Section 3 verifies that x* is a vertex. Section 4 gives a general perturbation lemma, and then one integer certificate per tour, 5040 in all. Section 5 records the source's n = 4 control, an observation about Table 2 of [1], and the open cases. Section 6 describes the Lean formalisation and its correspondence with the statement. Section 7 discusses related work, notably the metric-polytope precedent of Laurent–Poljak and Deza–Indik [2]. Section 8 states the limits of this draft.

## 2. The source definitions and the reading of adjacency

We follow [1, p. 2]. V = {1, …, n} (the examples of [1] label nodes from 0), A = {(i, j) : i, j ∈ V, i ≠ j}, m = n(n − 1), and for S ⊂ V the cut is δ(S) = {(i, j) : i ∈ S, j ∉ S}. The polytope is

!DISPLAY P<super>n</super><sub>ASEP</sub> = { x ∈ ℝ<super>m</super> : (2), (3), (4), x ≥ 0 }     [1, (6)]

with the in-degree equations (2) Σ<sub>i</sub> x<sub>ij</sub> = 1 for all j ∈ V, the out-degree equations (3) Σ<sub>j</sub> x<sub>ij</sub> = 1 for all i ∈ V, and the subtour elimination constraints (4) Σ<sub>(i,j)∈δ(S)</sub> x<sub>ij</sub> ≥ 1 for all S ⊂ V with 2 ≤ |S| ≤ n − 2. In Section 3 of [1], points are written as n × n matrices with zero diagonal; we do the same.

**Neighbourhoods.** X<super>n</super><sub>ASEP</sub> denotes the vertex set. Definition 3 of [1] reads: "The set of all vertices adjacent to x ∈ X<super>n</super><sub>ASEP</sub> is called the neighborhood of x and is denoted by N(x)". The proof of Lemma 7 spells adjacency out: two adjacent vertices "share exactly r(n) − 1 linearly independent and tight constraints". Section 5.2 of [1] calls the resulting graph the polyhedral graph, the graph "formed from the vertices and edges" of the polyhedron (Definition 8). So N(x) is the neighbourhood in the ordinary vertex–edge graph.

For distinct vertices x, y of a polytope given by linear constraints, three conditions are equivalent:

- (i) the segment [x, y] is a face (an edge);
- (ii) [x, y] is an extreme subset;
- (iii) the constraints tight at both x and y have rank m − 1.

Theorem 1 refutes the weakest of these, (ii). It therefore refutes every one of them, and also the exposed-face reading, since exposed faces are extreme subsets.

**Quantifiers.** Conjecture 1 names no n. The natural reading, and the one formalised, is: for every n ≥ 4, every vertex x of P<super>n</super><sub>ASEP</sub> and some tour T, T ∈ N(x). Every reading whose range of n contains 8 is refuted. (For n ≤ 3 there are no constraints (4); [1] studies n ≥ 4.)

**Other readings do not rescue the conjecture.** Two alternatives can be ruled out.

- *Pivot reading.* The pivoting procedure of [1, Section 4.1] defines N′(x) = Pivoting(x, T), which "returns only a subset of N(x)" [1, (20)]. Each non-degenerate pivot moves along an edge, so a neighbourhood defined by pivots is never larger than N(x).
- *Orbit reading.* Lemma 7 of [1] makes N equivariant under relabelling, and the tours form a single orbit. So "some representative of the tour orbit is adjacent to x" is the same statement as the original.

## 3. The vertex x*

Label the nodes 0, …, 7 and let x* = X/4, where

!MATRIX (3.1)
 0 0 1 2 0 1 0 0
 0 0 1 0 0 0 1 2
 0 2 0 0 0 2 0 0
 2 0 0 0 0 0 0 2
 0 1 0 0 0 0 3 0
 0 1 0 0 3 0 0 0
 0 0 0 2 1 1 0 0
 2 0 2 0 0 0 0 0

The (i, j) entry of X is 4x*<sub>ij</sub>, with rows indexed by tails and columns by heads. For instance x*<sub>02</sub> = 1/4, x*<sub>03</sub> = 1/2 and x*<sub>46</sub> = 3/4. The support has 19 arcs, and 37 arcs carry the value 0.

!THEOREM Lemma 2. (a) x* ∈ P<super>8</super><sub>ASEP</sub>. (b) Every positive entry of x* is at least 1/4. (c) For every S with 2 ≤ |S| ≤ 6, either x*(δ(S)) = 1 or x*(δ(S)) ≥ 5/4. (d) Exactly eight cuts are tight: {0,3}, {4,6}, {0,3,7}, {4,5,6}, {0,1,2,3,7}, {1,2,4,5,6}, {0,1,2,3,5,7} and {1,2,4,5,6,7}. (e) The 16 degree equations, the 37 equations x<sub>a</sub> = 0 on zero arcs and the 8 tight cut equations have rank 56 = m. So x* is a vertex.

*Proof.* Every row and column of X sums to 4, the diagonal is zero, and X ≥ 0. This gives (2), (3) and x ≥ 0. Statement (b) is immediate.

The numbers 4x*(δ(S)) are integers. For all 238 sets S with 2 ≤ |S| ≤ 6, their minimum is 4, attained exactly at the eight listed sets, and every other value is at least 5. This is a finite exact check, and it gives (4), (c) and (d).

The eight tight sets form four complementary pairs. This is forced: the degree equations give x(δ(S)) = x(δ(V∖S)).

Statement (e) is an exact rank computation over ℚ. A feasible point whose tight constraints have rank m is a vertex. ∎

The finite checks in Lemma 2 were performed in three independent ways: by the Lean kernel (Section 6); by two exact programs in the lane that found x* (Python and Node BigInt); and again by the stdlib script tools/check_arith.py in the dossier. The Lean proof of extremality does not use a rank computation. If x* lies in an open segment between y, w ∈ P<super>8</super><sub>ASEP</sub>, then y and w vanish on the zero arcs and are tight on the tight cuts. Linear arithmetic on these equations in the 19 support coordinates then forces y = w = x*.

## 4. No tour is adjacent to x*

!THEOREM Lemma 3 (perturbation). Let x ∈ P<super>8</super><sub>ASEP</sub> satisfy (b) and (c) of Lemma 2, and let T be a tour. Suppose v ∈ ℤ<super>A</super> satisfies:
!ITEM (P1) v<sub>a</sub> ≠ 0 only on arcs a with x<sub>a</sub> > 0 or T<sub>a</sub> = 1;
!ITEM (P2) every row sum and every column sum of v is zero;
!ITEM (P3) v(δ(S)) = 0 for every S that is tight at x and crossed exactly once by T, that is, T(δ(S)) = 1;
!ITEM (P4) Σ<sub>a</sub> |v<sub>a</sub>| ≤ 64;
!ITEM (P5) there are arcs a, b with (x − T)<sub>a</sub> v<sub>b</sub> ≠ (x − T)<sub>b</sub> v<sub>a</sub>, so v is not parallel to x − T.
!ENDITEMS Then [x, T] is not an extreme subset of P<super>8</super><sub>ASEP</sub>. In particular x and T are not adjacent.

*Proof.* Let z = (x + T)/2 and ε = 1/512.

Every constraint that is not tight at z has slack at least 1/8 there.

- *Arcs.* z<sub>a</sub> = 0 only if x<sub>a</sub> = T<sub>a</sub> = 0; otherwise z<sub>a</sub> ≥ 1/8.
- *Cuts.* T(δ(S)) is the number of tour arcs leaving S, an integer that is at least 1. So z(δ(S)) = 1 exactly when x(δ(S)) = T(δ(S)) = 1, and otherwise z(δ(S)) ≥ min{(5/4 + 1)/2, (1 + 2)/2} = 9/8.

By (P4), every partial sum of εv has absolute value at most 64/512 = 1/8. The tight constraints at z are preserved: degree equations by (P2), zero arcs by (P1) and tight cuts by (P3). Hence z − εv and z + εv both lie in P<super>8</super><sub>ASEP</sub>.

If [x, T] were an extreme subset F, then the point z ∈ F, which lies in the open segment between these two points, would force both into F ⊆ x + ℝ(x − T). Then v would be parallel to x − T, contradicting (P5). ∎

*Proof of Theorem 1.* A tour on {0, …, 7} is determined by its cyclic order 0 → p<sub>1</sub> → ⋯ → p<sub>7</sub> → 0, where (p<sub>1</sub>, …, p<sub>7</sub>) runs over the 7! = 5040 permutations of {1, …, 7}. For each such tour the dossier stores an integer vector v satisfying (P1)–(P5) for x = x*, together with the witness arcs a, b of (P5). Lemma 3 applies to each, so no segment [x*, T] is a face. ∎

**Certificate format and checks.** Each certificate is one natural number, read as 90 base-128 digits:

- 7 digits for (p<sub>1</sub>, …, p<sub>7</sub>);
- 8 digits for the successor list of T;
- 4 digits for the witness arcs a and b;
- a count k;
- k triples (i, j, c + 64) describing v = Σ c·e<sub>ij</sub>.

The 5040 certificates are checked by a Boolean function chk. It tests (P1)–(P5) exactly as stated, and checks that the successor list agrees with the cyclic order. For (P3) it uses the list of the eight tight cuts. Completeness of that list (Lemma 2(d)) is itself a kernel-checked fact.

The largest Σ|v| that occurs is 34, and the largest support has 20 arcs. For the tour 0 → 1 → ⋯ → 7 → 0 the certificate is v = e<sub>01</sub> − e<sub>03</sub> − e<sub>21</sub> + e<sub>23</sub>, with witness a = (0,1), b = (0,2):

- (0,1) and (2,3) are tour arcs, and x*<sub>03</sub> = x*<sub>21</sub> = 1/2;
- the row and column sums vanish;
- (x* − T)<sub>a</sub> v<sub>b</sub> − (x* − T)<sub>b</sub> v<sub>a</sub> = (−1)·0 − (1/4)·1 ≠ 0.

The certificates were found from exact nullspaces in the lane that discovered x*. Here they were re-decoded and re-checked by tools/check_arith.py, which recomputes the tight cuts from scratch instead of reading the stored list.

**Rank histogram (diagnostic).** Write J(T) for the set of constraints tight at both x* and T. Adjacency would require J(T) to have rank 55. Over all 5040 tours the exact ranks are distributed as {44: 213, 45: 590, 46: 913, 47: 958, 48: 846, 49: 626, 50: 430, 51: 232, 52: 123, 53: 82, 54: 27}, with maximum 54. So the minimal face containing x* and T has dimension at least 2 in every case.

This histogram was obtained by the discovering lane with two unrelated exact implementations, and identically by the independent reviewer with fraction-free integer elimination. It is a cross-check of Theorem 1, not part of its proof, and it was not recomputed for this draft.

**Consequence for the source's strategy.** By Lemma 7 of [1], every relabelling of x* is also non-adjacent to every tour. So the orbit of x* has no representative in the neighbourhood of any integer vertex, and the route to the V-description of P<super>8</super><sub>ASEP</sub> proposed after Conjecture 1 fails. The vertex graph itself is connected, as every polytope graph is. What fails is only the one-step reach from a tour.

## 5. Small cases, the n = 4 control and Table 2 of the source

**n = 4.** The source's Example 1 is the half-integral vertex x of P<super>4</super><sub>ASEP</sub> with rows (0, ½, 0, ½), (½, 0, ½, 0), (½, 0, 0, ½) and (0, ½, ½, 0). Its tight cuts are {0,1} and {2,3}, and its tight system has rank 12 = m. The same rank test as above shows that x is adjacent to exactly five of the six tours: the common tight rank is 11 for five tours and 7 for the tour 0 → 2 → 1 → 3 → 0.

This agrees with [1, Section 5.2]: each non-integer vertex of P<super>4</super><sub>ASEP</sub> has an integer neighbour, and each tour is adjacent to all vertices but one. We recomputed this control (tools/check_arith.py). It confirms that the rank test of Section 2 reproduces the source's notion of adjacency on its own example.

**n = 5.** The independent reviewer recomputed all 384 vertices of P<super>5</super><sub>ASEP</sub>: 5 orbits of sizes 24, 60, 60, 120 and 120. The values that match the source are:

- the orbit sizes, component types and tight-set counts of Table 2 of [1];
- the neighbourhood sizes |N(x)| = 28 for orbit (a), 23 for (d) and 148 for the tours (e);
- the qualitative statements of Section 5.2 of [1].

Every orbit has adjacent tours, so the conjecture holds for n = 5.

*Observation.* For orbit (b), with entries 1/3 and 2/3, and orbit (c), half-integral with 4 tight sets, Table 2 prints |N(x)| = 20 and 28. The reviewer's exact computation gives 11 and 20, by two methods that agree: the rank test, and a rank-free test of which vertices lie in the minimal face.

The computed values pass a double count of tour–fractional edges. Counting from the fractional orbits gives 60·12 + 60·10 + 120·4 + 120·10 = 3000, where 12, 10, 4 and 10 are the numbers of adjacent tours of orbits (a), (c), (b) and (d). Counting from the tours gives 24·(148 − 23) = 3000.

We report this as an observation only. It may be a transcription slip in the table: the printed values coincide with the computed values of the neighbouring rows. It has no bearing on Theorem 1.

**n = 6 and n = 7.** [1] reports that neighbourhoods for n = 6 cannot be explored exhaustively. In the discovering lane, randomly sampled vertices had at least 3 adjacent tours at n = 6. Eight simulated-annealing walks on the vertex graph at n = 7 reached a vertex with exactly one adjacent tour, but none with zero. The reviewer's small probe at n = 7 found nothing either. None of this is exhaustive. **Whether Conjecture 1 holds for n = 6 or n = 7 is open**, so the least counterexample size is unknown. At n = 8 the walks found many zero-tour vertices (about 100, with denominators 4 to 11 and supports of 19 or 20 arcs). x* has denominator 4 and 19 support arcs, the smallest values seen.

## 6. Formal verification in Lean

The dossier contains 21 Lean modules (and one unused helper). They are byte-identical to the frozen formalisation and build with Lean 4.34.1 (commit 5045d005) against mathlib revision d13f23b7.

!TABLE
Source notion | Lean declaration
P<super>n</super><sub>ASEP</sub> on ℝ<super>A</super>, A = {(i,j) : i ≠ j}: (2), (3), (4) and x ≥ 0 | ASEP.arcPolytope n (ASEPArcs)
the same polytope in the source's zero-diagonal matrix form | ASEP.polytope n, using ASEP.flux x S = Σ<sub>i∈S</sub> Σ<sub>j∉S</sub> x<sub>ij</sub> (ASEPDefs)
vertex | x ∈ Set.extremePoints ℝ (arcPolytope n); ASEP.IsVertex (ASEPDefs)
tour (directed Hamiltonian cycle) | ASEP.IsArcTour n t: t = arcTour σ for some σ with σ.IsCycle and σ.support = univ; ASEP.IsTour (ASEPDefs)
adjacency, Definition 3 | ASEP.ArcAdjacent n x y: both extreme points, x ≠ y, and IsExtreme ℝ (arcPolytope n) (segment ℝ x y); ASEP.Adjacent (ASEPDefs)
Conjecture 1, for all n ≥ 4 | ASEP.ArcNeighborhoodTourConjecture; ASEP.NeighborhoodTourConjecture (ASEPDefs)
Theorem 1 on ℝ<super>A</super> | ASEP.arc_counterexample : xa ∈ extremePoints ℝ (arcPolytope 8) ∧ ∀ t, IsArcTour 8 t → ¬ ArcAdjacent 8 xa t
Conjecture 1 is false | ASEP.arc_neighborhood_tour_conjecture_false : ¬ ArcNeighborhoodTourConjecture
Theorem 1, matrix form; x* fractional | ASEP.counterexample : IsVertex 8 xs ∧ xs 0 2 = 1/4 ∧ ∀ t, IsTour 8 t → ¬ Adjacent 8 xs t
matrix-form refutation | ASEP.neighborhood_tour_conjecture_false
no segment [x*, T] is a face (extreme subset) | ASEP.segment_not_face
nor an exposed face | ASEP.segment_not_exposed
Lemma 2 | ASEP.xs_mem, xs_entry, xs_cut, XN_cut, XN_tight, xs_extreme (ASEPVertex)
Lemma 3 | ASEP.not_extreme_of_dir (ASEPSound); ASEP.not_extreme_of_chk (ASEPBridge)
5040 certificates | ASEP.chunk0_ok … chunk47_ok (ASEPCerts0–11), kernel decide on ASEP.chk
every tour has a certificate | ASEP.certs_cover (ASEPCover) and ASEP.exists_cert (ASEPMain)
!ENDTABLE

**Architecture.** The modules divide the proof as follows.

- ASEPData holds X, the eight tight cuts and the 5040 encoded certificates.
- ASEPCheck defines the decoder and chk.
- ASEPCover proves by kernel decide that the certificates' cyclic orders are exactly List.permutations' [1, …, 7].
- ASEPMain turns the orbit of node 0 under any 8-cycle σ into such an order, using IsCycle.orderOf and IsCycle.pow_eq_one_iff.
- ASEPArcs transfers everything to ℝ<super>A</super> through the zero-diagonal embedding, a bijection onto zero-diagonal matrices that preserves membership, segments and extreme subsets.

The large finite checks are kernel decide proofs of Boolean checkers that are proved sound. Neither native_decide nor compiler evaluation is used.

**Fidelity points.**

- Mathlib's IsExtreme (this revision) asks that the segment lie in the polytope and that whenever a point of it lies in an open segment between two points of the polytope, the first of those points lies in it. By the symmetry of open segments this is the textbook definition of an extreme subset.
- The bound |S| ≤ n − 2 uses natural subtraction, which is exact for n ≥ 4.
- An independent reviewer wrote their own statement of the polytope (summing over all arcs with |S| + 2 ≤ n), of textbook faces and of tours as cyclic listings. They proved it equal to arcPolytope n for every n, and derived their own ¬Conjecture 1. That restatement is part of the review record, not of this dossier.

**Axioms and replay.** All six endpoints depend only on propext, Classical.choice and Quot.sound.

The dossier's replay driver (tools/replay.py) does the following:

- checks the pins (compiler and checker SHA-256, Lean commit, mathlib revision, package manifest);
- refuses existing build artefacts;
- verifies byte identity of the modules;
- scans them for forbidden constructs (sorry, admit, axiom, unsafe, partial, native_decide, ofReduceBool, implemented_by, extern and others);
- builds them one at a time with lean -j1 -DwarningAsError=true;
- runs leanchecker on every module;
- runs a full declaration audit;
- runs one positive and six negative controls.

Every call runs under a watchdog: 2 CPUs, 120 s CPU, 140 s wall, sampled RSS at most 6 GiB, MALLOC_ARENA_MAX = 2, and a systemd MemoryMax = 6G scope.

The audit covers all 300 constants whose home module is one of the 22 frozen modules, including generated ones. For each it records the module, kind, full type, presence of a body (value?), unsafe and partial flags, implemented_by and extern attributes, and collectAxioms. An independent body walk, which does not use the axiom data cached in the oleans, recomputes the closure of every endpoint. It flags two compiler-generated auxiliaries, ASEP.digs._unsafe_rec and ASEP.triples._unsafe_rec, which carry partial safety. The kernel would never let a safe declaration use them, and the walk confirms that no endpoint closure contains them or any other unsafe or partial constant.

The negative controls all fail as required:

- a one-digit mutation of a certificate;
- a certificate paired with another tour;
- the tight-cut list with one cut removed;
- the false claim that x* has no tight cut;
- a sorry;
- a theorem using a new axiom.

**Trust limits.**

- The pinned mathlib and dependency oleans are prebuilt and are trusted, not rebuilt.
- leanchecker runs per module without --fresh and shares the Lean installation with the compiler.
- RSS is sampled every 0.05 s, not continuously enforced, apart from the systemd memory limit.
- The Python and Node computations cited above are cross-checks only.

## 7. Related work

**The source and its follow-ups.** The source is [1]; arXiv lists only v1 (12 June 2025). We found no discussion of Conjecture 1 in later work by the same groups. The following bodies were read in full and do not mention it or tour neighbourhoods:

- [3] on the symmetric subtour relaxation;
- [4] on an asymptotic framework for the integrality gap;
- [5] on cycle covers and small ATSP instances;
- the dissertation [6].

**A precedent in the metric polytope.** Laurent and Poljak conjectured that every fractional vertex of the metric polytope met<sub>n</sub> is adjacent to an integral vertex, i.e. to a cut. Deza and Indik [2] describe the conjecture as dating from 1992, verified for n ≤ 8, and refute it with a vertex of met<sub>9</sub> whose 37 neighbours are all fractional. We have not read the Laurent–Poljak papers themselves and cite the conjecture as stated in [2].

Theorem 1 is the same phenomenon in a different polytope: a fractional vertex of an integrality relaxation with no integral neighbour, appearing just beyond the sizes that were checked exhaustively. We cite [2] as the direct precedent. It does not imply Theorem 1, and Theorem 1 is new as a statement about P<super>n</super><sub>ASEP</sub>, not new in kind.

There are also classical adjacency results for travelling-salesman polytopes, concerning edges between integral vertices (Padberg–Rao and Trubin, cited in the review record). We have not read these and draw no conclusion from them.

## 8. Status and limits

- This is a draft; it has not been peer reviewed. We make no priority claim.
- The literature check is bounded. It covered the bodies listed in Section 7, the arXiv abstract page of [1], and, in the discovering lane, a web search and path and keyword screens of two public proof registries. It is not a clearance of novelty.
- Several sources were not read:
  - the Laurent–Poljak originals and the journal version of [2];
  - Elliott-Magwood's thesis, which [1] cites for earlier enumerations;
  - the 2024 Optimization Online version of [1], which now returns HTTP 404. So we cannot say whether Conjecture 1 already appeared in 2024.
- The conjecture is a remark drawn from preliminary computations, and its refutation is modest in significance. It does defeat the strategy that motivated the conjecture.
- Whether a counterexample exists for n = 6 or n = 7 is open.

## References

!REF [1] E. Vercesi, J. Barta, L. M. Gambardella, S. Gualandi, M. Mastrolilli. On the integrality gap of small asymmetric traveling salesman problems: a polyhedral and computational approach. arXiv:2506.10671v1, 12 June 2025. Formulas (2)–(4) and (6); Definitions 3 and 8; Lemma 7; Example 1; Table 2; Conjecture 1.
!REF [2] A. Deza, G. Indik. A counterexample to a conjecture of Laurent and Poljak. arXiv:math/0512493v1, December 2005; AdvOL-Report 2005/21, McMaster University.
!REF [3] T. Villa, E. Vercesi, J. Barta, M. Mastrolilli. The integrality gap of the traveling salesman problem is 4/3 if the LP solution has at most n + 6 non-zero components. arXiv:2507.07003v3, October 2026.
!REF [4] J. Barta, M. Mastrolilli, E. Vercesi, T. Villa. An asymptotic framework for the integrality gap of the traveling salesman problem. Optimization Online preprint, August 2026.
!REF [5] A. Sosso, A. M. Bernardelli, S. Gualandi. The cloven traveling salesman: cycle covers and the integrality gap of small ATSP instances. arXiv:2511.05045.
!REF [6] E. Vercesi. Relation between computational complexity and integrality gap in branch-and-bound-based methods: the case of the travelling salesman problem. Doctoral dissertation, University of Pavia and Università della Svizzera italiana, October 2023.
!REF [7] MathDB record 368807, "The neighborhood-tour conjecture for ASEP vertices", https://mathdb.com/p/368807/the-neighborhood-tour-conjecture-for-asep-vertices (raw record SHA-256 c215c90f1c340a3c289ccffc287ce0af7f9eb7bca8273ba6e1a9140a682f1067).
!REF [8] The Lean 4 theorem prover, version 4.34.1 (commit 5045d0056413266e57c625dcd7c365b10e377c52), and the mathlib library, revision d13f23b723b8a846827a245b89c10fc7d3f11612.
