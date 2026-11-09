# CANDIDATE 351888: the three-colour conjecture for S-edge-colourings is false (Shannon triangles of type (2,1,1))

Status: ordinary proof of the decisive instance complete (half a page); exhaustive data on Shannon triangles; Lean draft plan UNCOMPILED. No credit claimed. Ranked third of the three candidates in this lane, because of family proximity (see §5).

## 1. Source and statement

* Petruševski–Škrekovski, *Odd edge-colorings of subdivisions of odd graphs*, arXiv:2109.04099. The TeX of v1 (Sep 2021), v2 (Dec 2022) and v3 (Mar 2023) was read. The conjecture `conj:3` is present in all three:
  * v1 line 785 ff.;
  * v3 line 854 ff.: "If G is a connected loopless graph that is not a Shannon triangle of type (2,2,1) and multiplicity μ(G) ≥ 3, then χ'_S(G) ≤ 3."
* Version of record: J. Graph Theory 104(3) (2023), DOI 10.1002/jgt.22991. **Its body is unread** (a repository URL served a different paper).
* Definitions:
  * χ'_S(G) is the least number of colours in an edge-colouring whose colour classes all lie in S (v3 line 840).
  * S is defined twice in v3. Line 817, directly before the conjecture: "S = {G : G is a loopless graph with Δ_even(G) ≤ 2}" (every vertex has degree 0, 2 or odd). Line 199: "loopless subdivisions of odd graphs".
  * Bouquet: all edges joining two given vertices. μ(G) is the maximum bouquet size. A Shannon triangle of type (p,q,r) has bouquet-size parities p ≥ q ≥ r, with 2 = even and 1 = odd (line 135).
* Three readings of "colour class ∈ S" were tested (`scripts/sedge3.py`, `scripts/sedge_tri.py`):
  * (deg) Δ_even ≤ 2;
  * (sub) additionally, every component has an odd vertex (a subdivision of an odd graph, where loops are allowed in the odd graph);
  * (subnl) a subdivision of a *loopless* odd graph.

  Each is strictly stronger than the previous one, so deg is the loosest. Only subnl reproduces the source's claim that the (4,4,3) triangle (Fig. "shanno") needs four colours. Under deg, (4,4,3) is 2-colourable: one class takes bouquet counts (0,3,2) and the other (4,1,1).

## 2. Result

**Proposition.** The Shannon triangle T(7,7,8) has bouquets of sizes 7 (xy), 7 (xz) and 8 (yz), so its type is (2,1,1). It is connected, loopless, and not of type (2,2,1). Yet it has **no** S-edge-colouring with 3 colours under the loosest reading (deg), and therefore none under any of the readings. Hence χ'_S(T) ≥ 4, and Conjecture conj:3 fails under every reading of S.

Under the intended reading subnl, the smallest counterexamples are (4,5,5), (4,5,7) and so on. Exhaustively for all Shannon triangles with bouquets ≤ 22 (`outputs/sedge-tri-char-subnl-M22.txt`):
* χ'_S ≥ 4 iff the type is (2,2,1) with every bouquet ≥ 3, or the type is (2,1,1) with every bouquet ≥ 4;
* types (1,1,1) and (2,2,2) are always ≤ 3.

Under deg the corresponding threshold is minimum bouquet ≥ 7 (`scripts/sedge_tri.py deg 20`).

So the correct exception list is not the source's. Moreover the source's own claim "every (2,2,1) triangle with μ ≥ 3 needs 4" is false as written. For example (1,2,4) has μ = 4 and is 2-colourable under subnl (`scripts/sedge3.py subnl 3 3 1 2 4`). The claim is true only when "multiplicity" is read as the minimum bouquet size.

## 3. Proof of the Proposition (reading deg)

1. **Setup.** Let a_j, b_j, c_j be the numbers of xy-, xz- and yz-edges of colour j (j = 1, 2, 3). The colour-j degrees are x_j = a_j + b_j, y_j = a_j + c_j and z_j = b_j + c_j. Each lies in {0, 2} ∪ odd. The totals are Σx_j = 14, Σy_j = 15, Σz_j = 15, Σa_j = 7, Σb_j = 7, Σc_j = 8.
2. **Parity types.** x_j + y_j + z_j is even, so in each colour exactly 0 or 2 of the three degrees are odd. Call colour j of type E (no odd degree), X̄ (odd at y and z), Ȳ (odd at x and z) or Z̄ (odd at x and y). Since Σx_j is even and Σy_j, Σz_j are odd:
   * n_Ȳ + n_Z̄ is even;
   * n_X̄ + n_Z̄ is odd;
   * n_X̄ + n_Ȳ is odd.

   With n_E + n_X̄ + n_Ȳ + n_Z̄ = 3, the possibilities are (n_X̄, n_Ȳ, n_Z̄) ∈ {(1,0,0), (3,0,0), (0,1,1), (1,2,0), (1,0,2)}.
3. **Size bounds.** An even colour degree is at most 2.
   * (1,0,0) with two E colours, or (3,0,0): x is even in every colour, so 14 = Σx_j ≤ 6. Contradiction.
   * (0,1,1) with one E colour: y is even in the Ȳ and E colours, so y_{Z̄} ≥ 15 − 4 = 11. But z_{Z̄} = b_{Z̄} + c_{Z̄} ≤ 2, so a_{Z̄} ≥ 9 > 7. Contradiction.
   * (1,2,0): y is even in both Ȳ colours, so y_{X̄} ≥ 11. But x_{X̄} ≤ 2, so c_{X̄} ≥ 9 > 8. Contradiction.
   * (1,0,2): symmetric to (1,2,0) with z in place of y, so c_{X̄} ≥ 9 > 8. Contradiction. ∎

Independent checks: brute-force enumeration of all 3-colour count vectors (`scripts/sedge_show.py 7 7 8`: 0 colourings) and a backtracking search (`scripts/sedge2.py`) agree. The intended-reading instance (4,5,5) has 0 colourings with 3 colours and 240 with 4 (`scripts/sedge3.py`).

## 4. Prior art screen (bounded)

* Every arXiv version was read. The conjecture persists in v3, and the S^{(2k)} reformulation dates from v2.
* Web searches for S-edge-colourings and Shannon triangles found only the odd-edge-colouring literature (Liu–Petruševski and others), none treating S-colourings.
* Registries: no hits (Lean Pool, Omega, OpenAI/math; GitHub "odd edge coloring" 0 results, "Shannon triangle" 2 unrelated results). The Omega file caro-petrusevski-skrekovski-tuza-grid-three-eighths concerns a different paper.

## 5. Honest credit risks (high)

* The obstruction is again a Shannon triangle, the same object family as the source's printed four-colour example (4,4,3), with the other parity type. Root may judge it a small modification of a printed example or a parameter variant. The characterisation of all Shannon triangles is the more substantive content, but it is computational only (bouquets ≤ 22), with no proof yet.
* The source's two definitions of S disagree. The refutation is robust because it uses the loosest reading, but a reviewer may see part of the picture as a formulation correction.
* The JGT VoR is unread.

## 6. Lean plan (UNCOMPILED)

* **Statement.** A loopless multigraph on Fin 3 with bouquet multiplicities (7,7,8). A k-colouring is a family of k sub-multiplicity vectors summing to (7,7,8). A colour class is in S_deg iff every vertex degree is 0, 2 or odd. The endpoint is ¬ ∃ 3-colouring, which implies ¬ ∃ for S_sub and S_subnl via monotonicity lemmas.
* **Proof.** Either use kernel `decide` over the 36 · 36 · 45 = 58,320 count triples (measure the cost first; no native_decide), or formalise the parity argument of §3 (≈ 60 lines with `omega`).
* **Modelling bridge.** Colouring individual edges is equivalent to colouring count vectors, because parallel edges are interchangeable. The lemma is easy: map an edge colouring to its counts, and conversely assign colours to bouquet edges in blocks.
* The conjecture's hypothesis "not a Shannon triangle of type (2,2,1) with μ ≥ 3" holds by `decide` (parities: 8 even; 7, 7 odd).
