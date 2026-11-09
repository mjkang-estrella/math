# Review of the MathDB 343536 candidate proof: grid-review-r1

Reviewer: Claude Opus 5.5, independent adversarial review lane `grid-review-r1`, 2026-11-03.
Target: `expanded-corpus-r131/PROOF-343536.md`, which claims a proof of Neuberger–Sieben–Swift
Conjecture 5.6 (equitable partitions of P_m □ P_n) for all m, n ≥ 1.

This is a review, not an acceptance. Nothing here is self-accepted, and root decides.

## Bottom line

| Gate | Verdict |
| --- | --- |
| A. Statement fidelity | PASS |
| B. Independent mathematics | PASS (minor presentational gaps only) |
| C. Prior art | QUALIFIED_PASS |
| D. Significance | QUALIFIED_PASS |
| E. Lean feasibility | QUALIFIED_PASS |

**Overall recommendation: PROCEED_TO_LEAN.**

I read the proof line by line and found no mathematical gap. My own exhaustive enumeration
covers 173 grids, including every square up to 20×20. It finds no non-orbit equitable partition,
and every prediction of the conjecture holds, including the failures at 2×2 and 3×3.

The bounded prior-art search found no earlier proof for grids with m, n ≥ 2. There are three
caveats on credit:

1. **Paths are already known.** The path case 1×n follows from a 2026 published theorem on trees
   (Brito–Manoel, J. Nonlinear Sci.), which r131 did not find.
2. **The lattice sentence is formal.** It follows from sentence 1 and a stabilizer count, and the
   source itself states the key implication (v2 lines 282–286).
3. **The automorphism group is classical.**

So the substantive new content is sentence 1 for m, n ≥ 2. It is short and elementary. Whether
that clears the substantive-credit bar is root's call; I judge it a genuine, if modest,
resolution of a published conjecture.

## Input binding

All 223 files under `expanded-corpus-r131/` were hashed before any reading and again at the end:

* `hashes/r131-before.sha256` and `hashes/r131-after.sha256` are identical.
* The sha256 of each manifest file is fab7baf47d2bf218e9f80276a89a462df7078ad904186ea31f1e3a9a0c020fd7.

Key files:

| File | sha256 |
| --- | --- |
| `PROOF-343536.md` | 96e653e818e88b30a4d931fdad35a21aef4e9e191ec778735fb528e92decb2b7 |
| `SUMMARY.md` | 97bd3832426432e456d3b3baa67177271c1784cd49d3699141e56bc308bbf580 |
| `results.json` | e96c80a1b86d81ba3433f077efc4198d8cc53e8cb0e259374a8dd849d5b887f0 |
| `lean-draft-UNCOMPILED/Grid343536.lean` | 67d8de6afd98f92956c1de17596b0332c75bd85cc84760f7806a38ba08c20a88 |
| `lean-draft-UNCOMPILED/PLAN-343536.md` | a95642a9a2bcc53d86283dbf6e19699fdc2c2ea3f1936780974778d80c8f8b86 |
| `raw/343536.jsonl` | e2ad69cb53f7ca7e2ee18826e38c587b98ea54e58d87928d18b861ec62949407 |

The MathDB raw line is `mathdb-normalized-chunk-0006.jsonl`, one-based line 2921. Its sha256
(line including the trailing newline) is e2ad69cb…949407. That matches the brief and
`raw/343536.jsonl`. It is identical in all three frozen copies of the chunk (chunk sha256
1dd3c173…ab88), under lanes r301, r307 and r320.

r131's scripts were not run, imported or copied. All code in this lane is new.

## A. Statement fidelity: PASS

### Source text

The source is arXiv:1908.05797:

* v1, lines 299–305;
* v2, lines 293–294 and 308–313 (the conjecture is split by Figure 5.2).

The published version is SIAM J. Appl. Dyn. Syst. 19(2) (2020) 964–993, DOI 10.1137/19m1283495,
confirmed through OpenAlex W2967946008. The conjecture sentence is word-for-word identical in v1
and v2. The following remark differs only in its last sentence: v1 says "A direct approach might
also work."; v2 says "the techniques of [?] might also provide a proof". I did not read the
paywalled SIADS body; v2 (February 2020) is the latest version I read.

### Fixed meanings

* **Orbit partitions of natural actions of the subgroups of the automorphism group.** For each
  subgroup H ≤ Aut(G), let H act on V(G) by h·v = h(v). The orbit partition is {Hv : v ∈ V}. The
  claimed set equality is

  EqPart(G) = {orbit partition of H : H ≤ Aut(G)}.

  The source uses "natural action of Aut(G)" in exactly this sense (v2 lines 282–283).
* **Order direction.** The source's order on partitions (v2 lines 111–116) is A ≤ B iff A is finer
  than B. The discrete partition is the bottom and the one-class partition is the top.
  EqPart = Π_A(n) is ordered as a subposet and is a lattice by Proposition 4.5 (v2 line 196),
  with the join as in Π and a different meet. Sub(Aut G) is ordered by inclusion. So
  Φ : H ↦ orbit partition is order-preserving: the trivial group maps to the discrete partition,
  and larger groups give coarser partitions.

  This matters. For m = n ≥ 4, Sub(D4) has 5 atoms and 3 coatoms, so it is not self-dual. Under
  the reverse order (inclusion of synchrony subspaces) the natural map would be an
  anti-isomorphism, and abstract isomorphism would fail. The source's convention makes the
  conjecture consistent, and the proof uses that convention (PROOF lines 186–190).
* **"Isomorphic."** Two readings are possible:
  * (i) Φ is a lattice isomorphism;
  * (ii) EqPart(G) and Sub(Aut G) are abstractly isomorphic lattices.

  The proof covers both. In the positive cases Φ itself is an order isomorphism, hence a lattice
  isomorphism (PROOF lines 190–194). In the negative cases the two sets have different
  cardinalities, so no isomorphism of any kind exists (lines 195–198).
* **Distinct subgroups may share an orbit partition.** The source's remark after the conjecture
  (v2 line 310) says Z4 and D4 have the same orbit partition on 2×2 and 3×3. That confirms Φ is
  not assumed injective. My enumeration gives the fibres exactly:
  * 2×2: 10 subgroups map onto 7 partitions. The one-class partition is the image of Z4, of the
    Klein group {id, ρ_r, ρ_c, ρ_rρ_c} and of D4. The partition {(1,1),(2,2)} | {(1,2),(2,1)} is
    the image of both the half-turn group and the Klein group of the two diagonal reflections.
  * 3×3: 10 subgroups map onto 9 partitions; only Z4 and D4 coincide.
* **A vertex with trivial stabilizer subgroup.** This means some v ∈ V has Stab_{Aut G}(v) = 1.
  The stabilizer is taken in the full Aut G, not in A0. The proof correctly passes from A0 to
  Aut G through Corollary B (lines 179–184).
* **"This happens unless 2 ≤ m = n ≤ 3."** "This" is the existence of a free vertex, equivalently
  (by sentence 2) the isomorphism. Read literally, "unless" claims only one direction (outside
  the exceptions it happens). The proof gives both directions (lines 173–177 and 190–198), so
  either reading is covered.

### Number of claims

The conjecture is three claims:

* (S1) EqPart = orbit partitions of subgroups of Aut G;
* (S2) for each grid, EqPart ≅ Sub(Aut G) ⟺ a free vertex exists;
* (S3) a free vertex exists ⟺ not 2 ≤ m = n ≤ 3.

S2 is an equivalence, for each (m, n), between two properties. Over the grid family it holds
because both sides are true outside {2×2, 3×3} and both are false on them. The proof establishes
S1 through its Main Theorem plus the general easy direction (lines 46–51), S3 in Section 7
(lines 171–184), and S2 in Corollary C (lines 186–198). All three are established in their
strongest reading, including the "exactly when".

### Degenerate cases

* 1×1: Aut = 1, Sub = {1} and EqPart has one element. The vertex is free, and 1×1 is not
  exceptional. Consistent, and handled by the proof (lines 163 and 176).
* Paths 1×n with n ≥ 2: Aut = Z2, Sub has 2 elements and EqPart has 2 elements (discrete and
  reversal-orbit). The endpoint is free. Handled (lines 161–167). I confirmed this exhaustively
  for n ≤ 40 and n = 80, with brute force over all set partitions for n ≤ 12.
* **m = 0 or n = 0** (empty graph) is the one place the literal statement would fail. Both
  lattices have one element, but no vertex exists, so S2 and S3 would be false. The source's
  "m × n square grid graphs" and P_m imply m, n ≥ 1. The proof states m, n ≥ 1 (lines 29 and 46),
  and the Lean skeleton carries the hypotheses `1 ≤ m`, `1 ≤ n` on S2 and S3. This must be kept
  in any final Lean endpoint.

### MathDB match

The MathDB statement, from the raw line, reproduces the conjecture word for word, with
`\oblong` for □. Its gloss of "equitable" matches Definition 5.1 (v2 lines 266–267). Its status
is open and its solutions array is empty.

One defect is in MathDB metadata, not in the statement. The `references` field and
`first_stated_year: 2018` cite arXiv:1807.10954 as an earlier statement. I fetched that abstract
page (`net/f1/abs1807.html`, receipt included). It is an unrelated coding-theory paper,
"Domination Mappings into the Hamming Ball". So the 2018 provenance is a MathDB error. The
conjecture first appears in arXiv:1908.05797 v1 (2019). r131 did not address this.

Verdict A: **PASS.**

## B. Independent mathematics: PASS

### My computation

The scripts, all new, are:

* `scripts/eqgrid.py`;
* `scripts/run.sh` (the capped runner);
* `scripts/aggregate.py`.

**Equitable partitions** come from an exact split-and-cir enumeration. cir(A) is the coarsest
equitable refinement of A, computed by iterated neighbour-count refinement. The search starts at
T = cir(one class) and runs a depth-first search over every 2-split of every class.

* Completeness: if B is equitable and B < A, with A equitable, then B splits some class of A.
  Group the B-classes inside it into two nonempty parts to get a split A'. Then B ≤ A', so
  B ≤ cir(A') < A.
* Soundness: every output is re-checked literally against Definition 5.1.

The method does not use row determinism, layers, the group A0, or anything else from the r131
proof.

**Brute-force cross-check.** For every grid with at most 12 vertices, all set partitions are
enumerated as restricted-growth strings, up to Bell(12) = 4,213,597, and each is tested against
Definition 5.1. That covers 26 grids:

* 1×n for n ≤ 12;
* 2×n for n ≤ 6;
* 3×1, 3×2, 3×3 and 3×4;
* 4×2, 4×3, 5×2 and 6×2.

Brute force and split-and-cir agree on every one.

**The automorphism group** is computed by complete backtracking over adjacency-preserving vertex
permutations; A0 is not assumed. All subgroups are found as the closed subsets that contain the
identity. For each grid the script then checks:

* the orbit partitions;
* injectivity of Φ;
* the order-embedding property, testing H ⊆ K against Φ(H) ≤ Φ(K) for all pairs;
* the existence of a free vertex in the full Aut G.

**Control.** On the McKay graph of the source's Figure 5.1, the enumerator finds exactly the 8
equitable partitions the source reports (v2 line 276). That includes the non-orbit partition
124578|36. So the code does detect non-orbit equitable partitions.

**Coverage.** 173 grids in all:

* 1×n for n ≤ 40, and 1×80;
* 2×n for n ≤ 30, and 2×60;
* 3×n for n ≤ 20, and 3×40;
* 4×n for n ≤ 16, and 4×30;
* every m×n with 3 ≤ m ≤ n ≤ 14;
* the squares 15×15 through 20×20.

The brief's minimum (1×n to 12, 2×n to 10, 3×3, 3×4, 4×4) is exceeded. Square sizes match the
source's own 20×20 limit.

**Results** (from `summary/enumeration-summary.json`):

* No non-orbit equitable partition anywhere. EqPart equals the set of orbit partitions on every
  grid.
* Aut G = A0 on every grid.
* Counts:
  * 1 (1×1);
  * 2 (paths);
  * 5 (m ≠ n, both ≥ 2);
  * 10 (m = n ≥ 4);
  * 7 against 10 subgroups at 2×2;
  * 9 against 10 subgroups at 3×3.
* A free vertex is absent exactly at 2×2 and 3×3.
* Φ is an order isomorphism onto EqPart exactly when a free vertex exists.

These counts agree with r131's (PROOF lines 210–212), over a larger range. The peak RSS was
14 MB for every enumeration run. The longest single grid (20×20) took 25 s of CPU time.

### Line-by-line reading of PROOF-343536.md

**Lines 38–44 (neighbour rule).** Correct. The neighbour-colour multiset M(c) is well defined
exactly when π is equitable, and χ∘g has the same rule for any automorphism g.

**Lines 50–51 (easy direction).** Correct.

**Lines 55–56, L1 (cell invariants).** Correct: |N(v) ∩ S| = Σ_{B ⊆ S} d_B(v).

**Lines 58–65, L2 (row determinism).** Correct. With rows 1..i fixed, χ(i+1, j) is the unique
element left after removing the colours of the known neighbours of (i, j) from M(χ(i, j)). The
statement is for two colourings with the same rule, which is exactly what the later use needs
(χ and χ∘g).

**Lines 67–76, L3 (propagation).** Correct. For the step w ≡ w' at level k+1:

* d_{χ(a)}(w') = d_{χ(a)}(w) ≥ 1 gives a' ≡ a;
* λ(a') = k by (i);
* induction gives g ∈ H(π) with ga = a';
* uniqueness, transported by g, which preserves λ, forces w' = gw.

Each cell is then contained in one H-orbit, and H-orbits lie inside cells.

**Lines 90–93 (ℓ constant on cells).** Correct. In effect ℓ = 1 + dist(·, border): it is
1-Lipschitz, and the point (i−1, j) witnesses the step down. Base case: {ℓ = 1} = {deg ≤ 3} for
m, n ≥ 3.

**Lines 95–96, property (ii).** Correct. The other neighbours of a = (i−1, j) have ℓ ≤ k.

**Lines 98–101 (border rule).** Correct for m, n ≥ 3. The border is an induced cycle of length
2(m+n)−4, and each non-corner has exactly one interior neighbour (ℓ = 2 needs m ≥ 3).

**Lines 103–106, L4 (side walks).** Correct, with one presentational gap: the walks must be
non-backtracking (x_{t+1} ≠ x_{t−1}). Otherwise M_B(χ(x_t)) = {χ(x_{t−1}), χ(x_{t+1})} is false.
Every walk the proof uses is a monotone walk along one side, so nothing breaks, but a Lean
version must state it.

**Lines 108–111 (corner timing).** Correct. Corners have degree 2 and other border vertices
degree 3, so no cell holds both. At the first step where exactly one walk sits at a corner, L4
up to that step forces equal colours, which is a contradiction. The case where the corner comes
at step 1 is covered by the hypothesis χ(x_1) = χ(y_1).

**Lines 113–124 (corner case).**

* The labelling χ(p') = χ(p) exists by equality of the neighbour-colour multisets.
* If m ≠ n and χ(p) = χ(q), corner timing still forces the chosen p' onto a side with n
  vertices. So the argument is valid for either labelling; in fact χ(p) = χ(q) is then
  impossible.
* g ∈ A0 with g(1,1) = u' and g(1,2) = p' exists:
  * when m ≠ n, because A0 = Z2×Z2 acts regularly on the corners and keeps rows as rows;
  * when m = n, because D4 acts regularly on the 8 corner-side flags.
* With χ∘g = χ on row 1, L2 gives χ∘g = χ everywhere.

**Lines 126–133 (non-corner case).** Correct. The two corner distances n − j and j − 1 put u' on
a side with n vertices at the right position, and L4 in both directions plus L2 finish it.

The reductions "transposing if necessary" and "by ρ_r take row 1" (lines 113–115) need the
standard conjugation argument:

* apply the result to χ∘ρ_r (or to the transported partition on P_n □ P_m);
* conjugate the resulting g back.

This is implicit but routine.

**Line 135.** L3 applies. Cells meeting B lie inside B, because ℓ is cell-constant.

**Lines 139–144 (2×2).** Correct. D4 = Aut(C4) acts regularly on the 8 flags (vertex, neighbour),
and walking around the 4-cycle determines everything.

**Lines 146–159 (2×n, n ≥ 3).**

* λ = 1 + horizontal distance to the corner set, which consists of the degree-2 vertices. It is
  cell-constant, and (ii) holds as stated.
* Column determinism: χ(i, j+1) = M(χ(i, j)) − {χ(i, j−1), χ(3−i, j)}. Correct.
* Corner transitivity is correct. Corner and non-corner colours are disjoint, which forces
  χ(u'*) = χ(u*). Z2×Z2 acts regularly on the corners and maps columns to columns.

**Lines 161–169 (paths and transposition).** Correct. Determinism from vertex 1 and the
reversal give the endpoint cells. For n = 2 both vertices are endpoints, and λ ≡ 1. The
transposition covers n ≤ 2 < m.

**Lines 173–177 (stabilizers in A0).** Correct:

* m ≠ n: the corner (1,1) is free.
* m = n ≥ 4: the eight images of (1, 2) are distinct, since 2 ≠ n − 1.
* 2×2: the diagonal vertices are fixed by τ, the off-diagonal ones by the anti-diagonal
  reflection.
* 3×3: corners are fixed by a diagonal reflection, edge midpoints by ρ_r or ρ_c, and the centre
  by everything. (The proof writes "diagonal vertices by τ", which also covers the centre and
  two corners. The other two corners are fixed by the anti-diagonal reflection, which the proof
  names only for 2×2. A one-word omission.)

**Lines 179–184, Corollary B (Aut G = A0 when an A0-free vertex exists).** Correct, and a neat
use of the Main Theorem. It is also classical by the Sabidussi–Vizing / Imrich unique prime
factorisation of connected Cartesian products, and I confirmed it computationally on all 173
grids.

**Lines 186–198, Corollary C.** Correct. Φ is monotone and surjective, and it is order-reflecting
when a free vertex x exists: H x ⊆ K x and Stab(x) = 1 give H ⊆ K. In the exceptional cases
|EqPart| < |Sub|, through ⟨ρ⟩ ≠ A0 with the same orbits.

**Lines 210–212 (r131's computation).** These are consistent with my independent computation.

**Adversarial attempts.**

* I looked for a cell mixing degree classes, a border cell not closed under the corner-distance
  pair, and a 2×n colouring breaking column determinism.
* I checked whether the argument silently needs m ≠ 3 or n ≠ 3, the shortest sides, where a
  non-corner's two border neighbours are both corners. It does not: corner timing at step 1 is
  handled.
* I checked whether the "exactly when" could fail through an abstract, non-natural isomorphism.
  It cannot, because of the cardinalities.

None of these produced a gap, and the enumeration produced no counterexample.

Verdict B: **PASS.** The only gaps are presentational:

* the non-backtracking walks in L4;
* the implicit conjugation for the WLOG reductions;
* a slightly incomplete witness list for the 3×3 corners.

None is mathematical.

## C. Prior art: QUALIFIED_PASS

All searches ran on 2026-11-03 over public HTTP. There were no 403, 429 or challenge responses,
and no denied route was used: no Crossref, Semantic Scholar or arXiv search API. Every response
has a receipt under `net/f*/`. OpenAlex returned a shared free-budget notice, so queries were
kept few.

### OpenAlex

* The source work is W2967946008. All 15 citing works (`net/f2/cites.json`) were screened by
  title and abstract (`net/f3/citing-detail.json`).
* The NSS-family follow-ups were read in body through my own text extraction
  (`scripts/pdftext.py`, pure Python), in `net/txt/`:
  * Nijholt–Sieben–Swift, arXiv:2206.00094 (J. Nonlinear Sci. 2023);
  * Neuberger–Sieben–Swift, arXiv:2308.10448 (SIADS 2024);
  * Kamei–Ruan, arXiv:2007.07414 (SIADS 2021).

  None mentions grids, apart from a citation title, and none mentions Conjecture 5.6.
* For Neuberger–Sieben–Swift, arXiv:2411.10904 (Constraints 2024), I grepped r131's cached v1 and
  v2 text, read-only. There are 0 hits for "grid", "Conjecture 5.6" and "1908.05797". This
  confirms r131's claim.
* The companion site (r131 cache, read-only) lists computed balanced partitions of the 3×3, 4×4
  and 16×16 grids. It has no proof.

### Keyword searches

* "equitable partitions grid graph";
* "equitable partition orbit partition automorphism grid";
* "balanced colorings finite rectangular lattice network";
* "perfect colorings finite grid graph";
* "equitable partitions Cartesian product of paths";
* "exotic synchrony grid network symmetry";
* "graphs whose equitable partitions are all orbit partitions";
* "compact graphs doubly stochastic …";
* an author search for Neuberger–Sieben–Swift.

### Findings

1. **Brito and Manoel**, "A Symmetry-Based Classification of Synchrony in Tree Networks",
   J. Nonlinear Sci. (2026), DOI 10.1007/s00332-026-10297-1. The abstract states: "We prove that
   exotic synchronizations do not arise in tree-type networks, showing that every balanced
   coloring is a fixed-point coloration determined by graph automorphisms." For undirected
   identical-cell networks, balanced colourings are exactly equitable partitions. Paths are
   trees, so **the 1×n case of S1 is published prior art.** It is also classical folklore.
   r131 missed this; it calls paths only "classical in flavour". I read the abstract only; I
   found no arXiv version, and the body is paywalled. It is published before the present work,
   but whether it states the result exactly in the orbit-partition form should be confirmed if
   it matters.
2. **Godsil**, "Compact graphs and equitable partitions", Linear Algebra Appl. 255 (1997)
   259–266, with Tinhofer 1991 and Wang–Li 2005. If π is equitable with characteristic matrix P,
   then P(PᵀP)⁻¹Pᵀ is a doubly stochastic matrix commuting with A. So in a compact graph every
   equitable partition is an orbit partition of a subgroup, and **compactness of P_m □ P_n would
   imply S1.** I found no result proving that grids, or Cartesian products of paths, are
   compact. Trees and cycles are compact (Tinhofer), and the recent compact-graph papers
   (Cançado–Coutinho, arXiv:2411.09157; Baptista–Coutinho–Godsil–Schmidt, arXiv:2606.13928,
   bodies grepped) do not treat grids. This route is a potential prior-art channel that root
   may wish to probe further, but nothing found closes S1.
3. **Krotov**, "Perfect colorings of the infinite square grid: coverings and twin colors",
   EJC (2023), arXiv:2010.15839 (abstract read). On the infinite grid every covering is either
   orbit or has twin colours, and there are non-orbit perfect colourings. This concerns the
   infinite regular grid, not the finite grid with free boundary, and gives no transfer.
   Švígler–Volek, arXiv:2412.21168 (body grepped), treats infinite lattices and regular graphs,
   with the same conclusion. The coupled-cell lattice papers (Wang–Golubitsky; Antoneli, Dias,
   Golubitsky and Wang) also concern infinite or periodic lattices, consistent with r131's note.
4. **Notarstefano–Parlangeli**, IEEE TAC 2013, arXiv:1203.0129 (body grepped). It treats
   Laplacian eigenvectors of grids through "brick" partitions, not equitable partitions or
   automorphism orbits.
5. **The automorphism group** of P_m □ P_n (Z2×Z2, or D4 when m = n) is classical through unique
   prime factorisation of Cartesian products. So Corollary B is not new, even though r131's
   derivation is self-contained.
6. **The lattice sentence S2.** The source itself proves the forward implication in general
   (v2 lines 283–285: a free vertex makes every subgroup's orbit partition distinct). So S2 adds
   no independent content beyond S1, S3 and the 2×2/3×3 coincidence the source already notes.

No prior proof of S1 for m, n ≥ 2 was found. The search was bounded: no full-text search of the
synchrony literature, no SIADS body, no Brito–Manoel body. Hence QUALIFIED_PASS.

## D. Significance: QUALIFIED_PASS

**For credit:**

* This is a named conjecture in a refereed journal paper (SIADS 2020), not a wording artefact.
* It was open on MathDB, with no resolution in 15 citing works or in the authors' four
  follow-ups to 2024.
* The authors had computational evidence to 20×20 but no proof, and suggested eigenvector or
  other methods.
* The proof resolves S1 in full generality, which is the conjecture's real content, and S2–S3
  exactly.
* It is not a parameter instance, not an endpoint correction, and not a corollary of the
  source's propositions; the source has no grid lemmas.
* A short elementary proof is not by itself evidence of routineness. The key idea is to make
  colours deterministic from a single side and to pin each border vertex's position through
  corner timing, so that cell-transitivity on the border reduces to A0.

**Against, or limiting, credit:**

* The path case is known (Brito–Manoel 2026, and folklore).
* The automorphism group is classical.
* The lattice sentence is formal.
* The remaining argument is about two pages of elementary combinatorics. A specialist in
  equitable partitions might regard it as a pleasant exercise rather than a significant
  theorem.
* The importance class is "corpus".
* The Godsil compactness route stays open as a possible older path to S1 (finding 2 above); no
  instance was found.

**Recommendation for D.** I judge this a genuine resolution of a published conjecture with
modest significance. Credit, if root grants it, should be framed as "S1 for m, n ≥ 2, with S2
and S3 as consequences". It should not be credited for paths or as a lattice-theoretic advance.
I do not find it zero-credit as known, routine or a wording artefact. Root decides the
threshold.

## E. Lean feasibility: QUALIFIED_PASS

Lean, lake and leanchecker were not run in this lane, as instructed. The assessment is based on
reading `Grid343536.lean` and `PLAN-343536.md`.

### The literal statement in the skeleton

**Faithful parts:**

* `Grid m n := pathGraph m □ pathGraph n` on `Fin m × Fin n` is Mathlib's box product of path
  graphs, with adjacency through `boxProd_adj` and `pathGraph_adj`.
* `IsEquitable` (Setoid form, counting `N(u) ∩ [w]` over all w) is Definition 5.1 literally.
* `orbitSetoid G H` with `u ~ v ↔ ∃ g ∈ H, g u = v`, for `H : Subgroup (G ≃g G)`, is the natural
  action of subgroups of the full automorphism group.
* `HasFreeVertex` uses the full Aut G.
* S3 is stated as `¬ (2 ≤ m ∧ m = n ∧ n ≤ 3)` with `1 ≤ m` and `1 ≤ n`; this is needed, see A.
* The Mathlib `Setoid` order is "r ≤ s iff r refines s", which matches the source's
  finer-is-smaller convention. The subgroup order is inclusion.
* `Nonempty (EqPart ≃o Subgroup …)` is abstract order isomorphism, which is equivalent to
  lattice isomorphism between lattices. This is the stronger reading for the negative cases and
  the weaker one for the positive cases.

**Recommended changes:**

1. Add the natural form for the positive cases. When a free vertex exists, `H ↦ orbitSetoid H`
   should be an order isomorphism onto `EqPart`, so that both readings of "isomorphic" are
   certified.
2. Make `EqPart` an `abbrev`, or give the instance through `inferInstanceAs`. As written,
   `Subtype.partialOrder _` on a plain `def` may fail instance resolution.
3. The `A0` definition casts the transpose with `h ▸`, which is fragile. It is cleaner to define
   the generating set by cases with `Equiv.prodComm` only when `m = n`, through `subst`, or to
   avoid `A0` as a subgroup and work with explicit elements.
4. Replace the `sorry` placeholders in `rowFlip`, `colFlip` and `transpose` (`map_rel_iff'`).
   These are easy, through `Fin.revPerm` and `Fin.val_rev` arithmetic.
5. Keep sentence 1 without size hypotheses (it is true for m = 0 or n = 0), but keep `1 ≤ m` and
   `1 ≤ n` on S2 and S3.
6. Optionally prove EqPart is a lattice, as the source's Prop. 4.5. It is not part of the
   conjecture's claim, since an order isomorphism between posets is enough.

### Size and risks

I estimate about 2000–4000 lines, a little above the plan's 1500–3000.

**Easy:**

* the explicit automorphisms;
* orbit partitions being equitable, through `Finset.card_bij`;
* L3 propagation;
* Corollaries B and C;
* the stabilizer computations;
* 2×2 and 3×3 through `decide` on explicit automorphism lists (allowed, not `native_decide`).

**Medium:**

* L2 row and column determinism. Equitability must be reformulated as an equality of
  neighbour-class multisets, followed by a "multiset minus known neighbours" step; Mathlib's
  `Multiset.map` and `Multiset.sub` arithmetic is fiddly.
* Transport of equitable and orbit partitions along the transposition isomorphism
  Grid m n ≃g Grid n m, and the conjugation argument for the WLOG reductions.
* Cell-invariance of ℓ, by induction on k.

**Hard (the bulk):**

* Border transitivity for m, n ≥ 3: side walks, corner timing, and the explicit choice of g ∈ A0
  by cases on the target side and corner. Following the plan's alternative, a uniform
  parametrisation of the border cycle by `ZMod (2(m+n)−4)`, with the corners at four known
  indices, should reduce this to one cyclic-determinism lemma and a short arithmetic case split.
* Since Aut G = A0 must hold literally for the full Subgroup type, Corollary B is needed in Lean;
  it is cheap given the Main Theorem.

**Risky lemmas:**

* L4 needs explicit non-backtracking hypotheses.
* Corner timing needs a degree-separation lemma: no cell contains both a degree-2 and a
  degree-3 vertex.
* The m = 3 and n = 3 edge cases have sides of length 3.

There is no obstacle in principle: no analysis, no large computation, and no dependence beyond
core Mathlib combinatorics.

Verdict E: **QUALIFIED_PASS.** It is feasible and well decomposed, the statement is faithful
with the noted fixes, and the work is substantial but routine. The skeleton has never been
compiled, so every Mathlib API name must be checked against the pinned Mathlib.

## Objections for root

1. (C) **Path-case prior art** from Brito–Manoel (2026, trees) was not found by r131. Credit
   should exclude 1×n.
2. (C) **Godsil compactness channel**: a proof that grids are compact would imply S1. None was
   found, but it was not exhaustively excluded.
3. (A) **MathDB metadata error**: arXiv:1807.10954 is unrelated, so the true first statement is
   arXiv:1908.05797 v1 (2019).
4. (B) **Presentational gaps** that a Lean version must make explicit: the non-backtracking walks
   in L4 (PROOF lines 103–106); the WLOG conjugation (lines 113–115); the 3×3 corner witnesses
   (line 177).
5. (D) **Significance is modest.** It is a short elementary proof of a "corpus"-importance
   conjecture, and root must weigh it against the substantive-credit standard.

## Access, resources and receipts

**Processes.** Every process ran through `scripts/run.sh`, strictly one at a time, with:

* `taskset 0,1` (2 CPUs);
* an RLIMIT_CPU of 120 s;
* a `timeout 140` s wall limit;
* an RLIMIT_AS of 2 GiB;
* MALLOC_ARENA_MAX=2;
* `python3 -I`, with TMPDIR and HOME inside the lane.

There are 25 receipts (including the final validator, `scripts/validate.py`) in `receipts/`, with full logs, `/usr/bin/time -v` output and log hashes
in `logs/`. The maximum peak RSS of any run was 26,252 KiB (a fetch run); enumeration runs stayed under 14 MB. No background job of this lane remains. Two
processes visible at handback belong to another lane (`schrijver-formal-r5`) and were not
touched.

**No Lean, lake, leanchecker, SAT solver or pdftotext was run.** PDFs were parsed by the
pure-Python `scripts/pdftext.py`.

**Network.** `scripts/fetch.py` wrote receipts with URL, status, bytes, sha256 and UTC time. It
was set to stop a host on 403 or 429 without retrying; neither occurred.

* Hosts: arxiv.org (abstract and PDF pages only) and api.openalex.org.
* There were no git operations, ledger edits, uploads, messages or browser tabs.

Downloaded data sits in fresh directories under `net/` and was parsed only by `python3 -I`
scripts kept in `scripts/`.

**Files.** The whole lane is under
`/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/grid-review-r1`:

| Path | Contents |
| --- | --- |
| `REVIEW.md` | this review |
| `review.json` | machine-readable verdicts |
| `scripts/` | eqgrid.py, run.sh, fetch.py, pdftext.py, aggregate.py |
| `outputs/` | per-run JSON |
| `summary/enumeration-summary.json` | aggregated enumeration results |
| `logs/` | run logs |
| `receipts/` | run receipts |
| `net/` | fetched data and receipts |
| `hashes/` | before/after input hashes |
