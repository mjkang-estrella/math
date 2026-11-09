# Independent adversarial review of the MathDB 329080 candidate (chord-review-r1)

Reviewer: Claude Opus 5.5 (review lane, no child agents), 2026-11-03.
Object: lane `expanded-corpus-r137`, candidate proof of the intended form of Conjecture 3.4 of Burns, Jonoska and Saito, "Genus Ranges of Chord Diagrams", arXiv:1410.6148v1. The paper has three authors, not "et al.". It was published in J. Knot Theory Ramifications 24(4) (2015) 1550022, doi 10.1142/S0218216515500224, with an open copy at PMC4607078.

This is a review, not an acceptance. Root decides.

**Overall recommendation: PROCEED to Lean formalisation, under the conditions in gates A and C.** The credit question in gate E is left to root.

| Gate | Verdict |
|---|---|
| A. Statement fidelity | QUALIFIED_PASS |
| B. Independent mathematics | PASS |
| C. Lean route design | QUALIFIED_PASS (the drafts are skeletons; a route exists) |
| D. Prior art (bounded) | PASS (no prior proof found) |
| E. Significance and exclusion screen | QUALIFIED_PASS (genuine, modest; not excluded) |

## 0. Discipline and receipts

- Read-only inputs were hash-bound before and after the review: 39 files (`hashes/before.sha256` and `hashes/after.sha256`). They are **identical**.
- The discovery lane's scripts were read but never imported or run. All code is mine: `scripts/chordrev.py`, written from the source definitions. It runs under `scripts/run.sh`, which sets:
  - `python3 -I`;
  - CPU limit 120 s (`ulimit -t 120`), wall limit 140 s (`timeout 140`), virtual memory about 1.9 GiB;
  - `MALLOC_ARENA_MAX=2`, two CPUs (`taskset -c 0,1`);
  - one process at a time.
- Full logs are in `logs/`, with peak RSS reported by `/usr/bin/time -v`. The largest run (hereditary search to n = 11) used 103 s CPU and 0.99 GB peak RSS. Every other run stayed under 260 MB.
- No Lean, lake, leanchecker or SAT/ILP binary was used. No background job remains.
- Downloads went into fresh directories `downloads/openalex-1/` and `downloads/arxiv-1/`. Receipts are in `downloads/receipts.json`, and hashes of the review artifacts are in `hashes/review-artifacts.sha256`.
- Two arXiv author-listing URLs returned 404 and were not retried. Crossref, Semantic Scholar, the arXiv search API and ScienceDirect were not touched.

Line references below are to `expanded-corpus-r137/sources/329080.txt` (the arXiv v1 text, "src") and to `expanded-corpus-r137/outputs/329080-proof.md` ("proof").

## Gate A: statement fidelity (QUALIFIED_PASS)

### A.1 Source definitions

- **Double-occurrence words and equivalence** (src 86–105): two words are equivalent when related by "cyclic permutations, reversal, and/or symbol renaming".
- **Thickened diagram** (src 106–121): the backbone is thickened to an annulus. Each band end is attached to the inner or the outer boundary circle, giving 4^n surfaces. All surfaces are orientable (Convention, src 121).
- **Genus range** (Definition 2.1, src 123–126): gr(D) = { g(F) }.
- **Lemma 3.1** (src 165–171): g(F) = (n − b(F) + 2)/2, derived from χ(F) = χ(D) = −n.
- The proof file states all of these correctly (proof 11–16).

### A.2 Literal statement

- MathDB 329080 (`raw/329080.jsonl`) reproduces the conjecture verbatim and fixes "Let n be a positive integer". The source wording is src 201–202, and the PMC text is identical (checked in `sources/329080-pmc.html`).
- The source's own table (src 182–186) gives GR₁ = GR₂ = {{0, 1}}. So no diagram with 1 or 2 chords has genus range {1, 2}, and the literal "for any n ≠ 4, there is a unique …" is **false at n = 1, 2**. My computation confirms this independently (`logs/gr_ribbon_n1-5.log`).
- The intended scope n ≥ 3, n ≠ 4 is clearly what the authors meant:
  - Lemma 5.2(2) (src 402–403) says "For any n > 2, there exists a chord diagram of n chords with genus range [1, 2]";
  - the remark after the conjecture (src 204) refers only to n = 4.
- At n = 3 the factor (44⋯nn) is empty and the diagram is 123123. This is consistent: R3 = 123123 is the unique {1, 2} diagram for n = 3.
- This matches the precedent pattern of 372205: a degenerate printed scope that contradicts the source's own data, with the substantive content at n ≥ 3. The n = 1, 2 refutation is itself zero credit and should be recorded only as a fidelity note.

### A.3 Key Lean-fidelity ruling: the combinatorial boundary count

**How the source counts boundary components.**
- Lemma 3.1 is stated topologically (src 154–171).
- The computations use "a modified version of [Anderson–Penner–Reidys–Waterman's] algorithm … by means of cycle decompositions of permutations" (src 174–178).
- Every proof that counts boundary components does so by tracing boundary curves along backbone arcs and band sides: Lemma 4.2 (src 218–241), Lemma 4.3 (src 279–314), Lemma 4.4 (src 340–351), Lemma 5.1 (src 375–389).
- So the source's working notion of b(F) is exactly face tracing. It also states that a thickened diagram is a compact surface with the graph D as a deformation retract (src 159–160).

**My independent derivation of the dart model.**
- ∂F is the union of two kinds of piece:
  - the annulus boundary minus the attaching intervals, which is 2n circle segments when both circles carry attachments, each starting at an endpoint i and running in the circle's induced orientation;
  - the 2n long sides of the bands.
- The two annulus boundary circles carry opposite induced orientations. Orientability means every band preserves the orientation, so a boundary curve leaving segment(i) at σ(i) crosses the band and continues on segment(τσ(i)).
- So the components that meet a band are exactly the cycles of τσ, which has the same cycle count as στ. An unattached circle adds one component.
- This is the lane's formula (proof 31–35), with the direction rule "inner increasing, outer decreasing". The rule is correct up to a global mirror, which does not change any count.

**Ribbon-graph view.**
- Equivalently, F is the ribbon graph of the cubic graph (2n vertices, 2n arcs, n chords). Inner and outer attachments are the two cyclic rotations at each trivalent vertex, so the 4^n thickened diagrams are exactly the 2^{2n} pure rotation systems.
- b(F) is the number of faces given by the classical Heffter–Edmonds face-tracing permutation (Mohar–Thomassen, the source's reference [6]).
- So gr(D) is the orientable genus range of that cubic multigraph. The source alludes to this at src 51–55 and 387–388.

**Ruling.**
- No surface topology of the needed kind (classification of compact surfaces with boundary, genus of a band surface) is available in mathlib. A literal topological formalisation is not feasible.
- The combinatorial face count is the standard combinatorial definition of a ribbon graph's boundary components. It is also how the source computes, and how its reference [1] defines genus.
- I rule that **a Lean endpoint may take a combinatorial boundary count as the definition**, under these conditions:
  1. **Preferred definition.** Take the textbook 6n half-edge rotation-system face count as the defining notion. At vertex i, an inner end gives rotation N→C→P and an outer end gives N→P→C; b is the number of orbits of ρ∘θ. Then prove in Lean that it equals the 2n-dart count used in the proofs. A first-return-map lemma gives this bridge (about 200–400 lines). If root accepts the 2n-dart model directly as the definition, the paper must contain the informal topological bridge above. The model then needs no unproved Lean bridge, but the definitional choice must be disclosed in the statement-fidelity review.
  2. **Empty circles.** The two empty-circle terms must be part of the definition. At n = 0 this gives b = 2, the annulus.
  3. **Genus without silent rounding.** Either define genus by 2g = n + 2 − b, or prove the parity lemma b ≡ n (mod 2). Do not rely silently on ℤ floor division.
  4. **Kernel sanity checks.** Include `decide` lemmas that reproduce source data: gr(1212) = gr(1122) = {0, 1}, gr(123123) = {1, 2}, GR₃ and GR₄ as in the source table, and gr(R4) = {1, 2}.
- Under these conditions the formal statement is a faithful formalisation of the source's notion. The verdict is QUALIFIED because the final call on "combinatorial definition = literal" belongs to root.

### A.4 Remaining fidelity notes

- Equivalence must include rotation, reversal and renaming. The lane's `Equivalent` does (Defs.lean 59–64).
- The n = 4 exception is not part of the conjecture's claim. The lane's "exactly four" (proof 124) is extra information. I confirm it: 11234234, 12134234, 12314234, 12341234 (`logs/gr_ribbon_n1-5.log`).

## Gate B: independent mathematics (PASS)

### B.1 Independent computations (`logs/`)

| Check | Result |
|---|---|
| Dart model vs my 6n ribbon model, every labelled matching and every mask, n ≤ 5 | 995,572 pairs, 0 mismatches (`xval_n1-5.log`) |
| The same on all 554 classes, n = 6, all 4,096 masks | 2,269,184 pairs, 0 mismatches (`xval_classes_n6.log`) |
| Class counts n = 1…7 | 1, 2, 5, 17, 79, 554, 5,283 (OEIS A007769), confirming the dihedral canonicalisation |
| GR_n for n = 1…6 (ribbon model) | equals the source table exactly (src 182–185) (`gr_ribbon_n*.log`) |
| GR_7 (dart model, all 5,283 classes, mirror-halved masks) | exactly the eight source sets {0,1}, {0,1,2}, {1,2}, {0,1,2,3}, {1,2,3}, {0,1,2,3,4}, {1,2,3,4}, {2,3,4} (src 186); the lane only checked n ≤ 6 (`gr7_dart_all.log`) |
| {1, 2} diagrams | n = 3: 123123; n = 4: four; n = 5, 6, 7: only R3·U_{n−3} |
| Genus ranges are intervals; bipartite iff min genus 0 | 0 failures, n ≤ 7 and n ≤ 6 |
| Deletion: removing any chord changes b by exactly ±1 (ribbon model, n ≤ 5, all classes, chords and masks) | 422,916 cases, 0 failures (`local_n1-5.log`) |
| Flipping one side changes b by 0 or ±2; global mirror preserves b; b ≡ n (mod 2) | 0 failures |
| Five-chord lemma, all 945 matchings, full maximum genus in the ribbon model | 492 satisfy P, 453 do not; no word with max genus ≤ 2 fails P; every max-genus-≤-2 word containing a triangle is ≅ 1231234455; 12 of 79 classes have max genus ≤ 2 (`base5.log`) |
| Lane certificate `Base5Data.lean` (parsed as text) | all 453 entries are genuine (1 face in my ribbon model, word fails my P), and they cover exactly the not-P set |
| R3 masks with 5 faces | 0 |
| Transfer rules for D_m = 123123 a₁a₁⋯a_ma_m, with s defined independently as "the two sides of the end edge lie on one face" | 21,760 rule checks for m ≤ 3, 0 violations; base states {(1,T), (3,F), (3,T)} confirmed; gr(D_m) = {1, 2} for m ≤ 5 (`transfer_m0-5.log`) |
| Hereditary classification of max genus ≤ 2 (complete by Corollary 2) | \|C_n\| = 5, 17, 12, 15, 17, 20, 22, 25, 27 for n = 3…11; the only {1, 2} diagram is R3·U_{n−3} for every 5 ≤ n ≤ 11; this goes two levels past the lane's n = 9 (`hered_n2-11.log`) |

### B.2 Step-by-step re-derivation

**Dart model.** Correct; derived above in A.3. The proof's justification (proof 35) is terse but correct.

**Lemma 1 (deletion; proof 45–57).** Correct.
- The band-side reconnection argument gives |Δb| ≤ 1.
- χ changes by +1, so parity forces Δb = ±1. Equivalently, an orientable ribbon edge deletion merges two faces or splits one.
- The source uses the same fact (src 222–226).
- Small presentational gap: step 3 uses the integrality of the genus, i.e. Lemma 3.1 applied to both surfaces. That is fine.

**Corollary 2 (heredity; proof 59–62).** Correct in both directions. Only the max-genus direction is used for sub-diagrams.

**Lemma 3 (bipartite gives genus 0; proof 64–68).** Correct. The A-chords are drawn inside the backbone circle and the B-chords outside, giving a plane embedding of the cubic graph, so b = n + 2. Only this direction is used.

**Lemma 4 (five-chord lemma; proof 70–78).** Independently re-verified by full maximum-genus computation, not only via witnesses. The statement "(b) for every triangle" is what the main proof needs.

**Main argument (proof 131–143).** Correct; I re-derived each step.
- Step 1 uses Lemma 3.
- Step 2: a shortest odd cycle is induced.
- Step 3: interlacement of a sub-diagram is the induced subgraph. Five consecutive vertices of an induced odd cycle of length 5 or more induce C₅ or P₅, which has no isolated vertex. That contradicts Lemma 4(a) through max-genus heredity.
- Step 4 needs n − 3 ≥ 2. This is exactly why n = 4 is exceptional.
- Steps 5 and 6: all extra chords lie in one arc I and are adjacent pairs, because a nested or crossing pair would violate adjacency in the five-chord sub-diagram.
- Step 7: reading from the triangle endpoint that follows I gives the word xyzxyz followed by pairs, which renames to (123123)(44⋯nn). The appeal to the 6-fold rotational symmetry is correct but unnecessary.
- n = 3 also follows directly: a non-bipartite 3-vertex graph is a triangle, so D = 123123. No finite check is needed.

**Existence (Lemma 6; proof 82–116).** Correct.
- I re-derived the dart algebra:
  - in-in: q becomes a fixed point and p is inserted into the cycle through τℓ, so b increases by 1;
  - in-out: τℓ → p → u and τv → q → a, a successor transposition, so b changes by +1 when s holds and by −1 otherwise;
  - in both in-out cases, q → a, so s becomes true;
  - the empty-circle cases agree.
- Existence is also already in the source, Lemma 5.2(2) (src 402–412).

**Verdict.** No gap found. The proof is complete given the finite Lemma 4, and I re-verified Lemma 4 independently.

## Gate C: Lean route design (QUALIFIED_PASS; nothing was compiled here)

### C.1 Cheapest literal endpoint

```
theorem conjecture_3_4 (n : ℕ) (hn : 3 ≤ n) (h4 : n ≠ 4) :
  genusRange (r3Block n hn) = {1, 2} ∧
  ∀ D : Diagram n, genusRange D = {1, 2} → Equivalent D (r3Block n hn)
theorem literal_false : ∀ D : Diagram 1, genusRange D ≠ {1,2}   -- and the same for Diagram 2
```

This is the lane's endpoint (Statement.lean 15–24), and it is the right shape. Optionally add a packaged `¬ (∀ n ≥ 1, n ≠ 4 → …)` so the literal falsity is explicit.

### C.2 Recommended design

**Data.** Keep `Diagram n` as a double-occurrence word, since that is the literal MathDB object. Prove the lemmas on a position-set representation: a `Finset ℕ` of positions with a partner involution and a side map. Sub-diagrams are then restrictions, and no `Fin` reindexing is needed. In the lane's design, deletion with reindexing from `Fin (n+1)` to `Fin n` (Proof.lean 16–20) will dominate the cost.

**Computable core.**
- σ is "next element of the same side in the filtered set": the minimum above, or the minimum overall for inner; mirrored for outer.
- Cycle count is the number of orbit minima. Bridge it once to `Fintype.card (Quotient (SameCycle.setoid π))`.

### C.3 Lemmas needed, in order

1. Basic algebra: σ_S is a permutation; boundary invariance under order-isomorphism of position sets (renaming and compression).
2. Lemma 1 (±1 deletion, with the refined criterion "+1 iff the inserted transition splits a cycle") via a local `card_cycles (π * swap a b) = card_cycles π ± 1` lemma. Parity b ≡ n then follows by induction from b(empty) = 2, so no separate sign argument is needed.
3. Corollary 2 (max-genus monotone under restriction), and the min-genus direction for existence.
4. Lemma 3 (bipartite gives genus 0) by induction, removing an innermost same-side chord (the fixed-point +1 case).
5. Finite lemmas by `decide` (C.4).
6. The transfer lemma by induction on m, or equivalent end-edge bookkeeping, giving gr(r3Block) = {1, 2}.
7. Graph part: non-2-colourable implies an induced odd cycle, so a triangle or a five-vertex window with no isolated vertex. Use `SimpleGraph` walks, or a self-contained shortest-odd-closed-walk lemma.
8. Arc argument and the final rotation and renaming to `r3Block`, using `finRotate` and `Fin.rev` instead of hand-written modular bounds.

### C.4 What the kernel can decide

- n = 1 and n = 2 literal falsity: 4 masks; 3 matchings × 16 masks.
- R3 has no 5-face mask: 64 masks.
- gr(123123) = {1, 2}, and the base states of the transfer lemma: 64 masks.
- The 945-word lemma:
  - write it as a nested ∀ over the partner-choice indices (9 · 7 · 5 · 3 = 945 leaves);
  - at each leaf, check either P or one face of a mask from a certificate table aligned with the enumeration order;
  - prove separately (about 100–200 lines) that every fixed-point-free involution on 10 points is one of the 945.
  - The lane's `base5_check` (Proof.lean 54–57) instead searches the 453-entry list for every word, about 430,000 list comparisons. It also lacks the completeness lemma for `standardWords5`. Both should be changed.
- n = 3 and n = 4 need no `decide`, because n = 3 follows from the triangle argument and n = 4 is excluded. The four n = 4 diagrams (105 × 256 masks) are optional.
- Kernel cost: all finite checks together should take seconds to a few minutes with structural `List` and `Nat` code and no `native_decide`.

### C.5 Size estimate

About 2,000–4,000 lines. The lane's 1,500–3,000 lines (PLAN.md 31) is optimistic once reindexing and the graph part are counted.

### C.6 What is right and wrong in the lane's UNCOMPILED drafts

**Right:**
- the statement shape (Statement.lean 22–24);
- `boundary` = cycles of σ∘τ (`(tau D).trans (sigma c)` is σ∘τ) plus the two empty-circle terms, which correctly gives b = 2 at n = 0 (Defs.lean 46–48);
- the side convention, true = outer;
- `Equivalent` includes rotation, reversal and renaming;
- the witness data is valid (verified above).

**Wrong or incomplete:**
- `partner` uses `Classical.choose` with `sorry` (Defs.lean 22–25). It is noncomputable and blocks `decide`.
- `nextSame`, `sigma`, `tau` and `r3Block` are `sorry` (Defs.lean 33, 36, 38, 68). Sorried definitions make the statement itself meaningless until filled.
- `genus` uses ℤ division with no parity lemma (Defs.lean 51–52).
- `Equivalent` has `sorry` bounds (Defs.lean 63–64).
- `maxGenus_mono_sub`, `dartFaces_eq_boundary` and `transfer_step` are vacuous `True := trivial` placeholders (Proof.lean 30–31, 60, 65).
- `base5_check` has the inefficiency and missing completeness lemma noted in C.4.
- `numCycles` via a Quotient cardinality is fine as a specification, but it needs a computable twin.

None of this is a mathematical error: the drafts are honest skeletons, and PLAN.md says so. They are a starting point, not partial certificates.

## Gate D: prior art, bounded (PASS)

Searches made on 2026-11-03; receipts are in `downloads/receipts.json`.

- **OpenAlex record** for the source: W2161507091, cited-by count 3. The three citing works are:
  - Zając et al. 2018, Sci. Rep. (genus trace of biomolecules);
  - Jaramillo Rodriguez 2023 (barcode analysis);
  - Cangiotti and Grasso 2025 (RNA genus comparison).
  - None concerns Conjecture 3.4 or uniqueness of genus ranges.
- **OpenAlex searches** for "genus range(s)" with chord diagrams, and for chord-diagram genus range uniqueness, found:
  - the source and its CiteSeerX copy;
  - Buck, Dolzhenko, Jonoska, Saito and Valencia, *Genus ranges of 4-regular rigid vertex graphs* (EJC 2015), whose citing works (5) are not about chord-diagram genus ranges;
  - Arredondo's 2014 USF thesis (genus ranges of assembly graphs);
  - Braun's 2020 USF thesis;
  - a 2026 Zenodo preprint by Qihang Wang on singleton genus ranges of rigid 4-regular graphs (Conjecture 33 of Buck et al.). That is a different object and a different conjecture.
- **Jonoska** (A5083450874, A5110555428) and **Saito** (A5017175550): 2015–2026 OpenAlex work lists, filtered by title for genus, chord, embedding, surface and double-occurrence words. No follow-up on chord-diagram genus ranges and no proof of Conjecture 3.4.
- **Maximum-genus literature**: OpenAlex searches for Kuratowski-type maximum-genus theorems (Nordhaus, Ringeisen, Stewart and White 1972 characterise maximum genus 0) and "graphs with maximum genus two" found no classification of cubic Hamiltonian graphs with maximum genus 2. Even such a classification would not settle uniqueness up to chord-diagram equivalence, because one graph can carry several Hamiltonian cycles.
- **Web search** (standard and extended): only the source, PubMed and PMC copies, and unrelated chord-diagram genus papers. No resolution reported.
- arXiv author-listing pages `/a/jonoska_n_1` and `/a/saito_m_1` returned 404 (no such author ids) and were not retried. The arXiv search API was not used, by rule.
- **The n = 4 exception**: the source's only statement is "several more chord diagrams for n = 4" (src 204). No later source lists the four. The lane's list of four is new information, but it is not credit-bearing.

**Limits.** OpenAlex citation coverage is incomplete. MathSciNet and zbMATH were not checked, and Google Scholar's "cited by" is not reachable. The lane's own registry screen (Omega and OpenAI/math path screens) was not re-done here.

## Gate E: significance and exclusion screen (QUALIFIED_PASS)

- **Known result?** None found (gate D).
- **Routine consequence of the source's lemmas?** No.
  - The source's tools are the concatenation Lemma 4.3 (src 261–314), the 123321 lemma (Lemma 4.4), the R_n and G_m computations, and the realisation results (Section 5). They all construct diagrams or bound one range. None classifies diagrams or proves uniqueness.
  - Concatenation gives existence only (Lemma 5.2(2)), and existence carries no credit.
  - The uniqueness argument needs three things absent from the source:
    - the bipartite planarity criterion;
    - the shortest-odd-cycle reduction;
    - the new finite five-chord lemma, an obstruction-type classification: 12 of 79 classes, 453 genus-3 witnesses.
- **Wording or endpoint artefact?** The n = 1, 2 falsity is a degenerate wording defect and is zero credit by itself. The substantive content, uniqueness for every n ≥ 5, is genuinely the conjecture's content and is fully proved. This is the 372205 pattern, so it is not an endpoint-correction exclusion. Root must not count the n = 1, 2 refutation.
- **Source-internal conflict?** Only the n = 1, 2 table versus wording issue. No conflict in the intended scope.
- **Degenerate case?** No. The theorem covers infinitely many n, with a uniform argument.
- **Significance.** Modest. This is a 2014 JKTR conjecture backed by computations, and the proof is short once Lemma 4 is known. The heredity-plus-finite-base technique is standard in spirit (Kuratowski-type obstruction arguments). The finite base and the odd-cycle reduction are new, and the conjecture was explicitly open. It meets the "genuine full proof of a published conjecture" bar, but not with a wide margin. Root should weigh the "short computer-assisted base" concern explicitly.

**Recommendation:** do not exclude. PROCEED to Lean, with the A.3 definition conditions and the C.2–C.4 design. Credit, if any, is for the intended statement for n ≥ 3, n ≠ 4.

## Files

- `REVIEW.md`, `review.json`
- `scripts/chordrev.py`, `scripts/run.sh`
- `logs/*.log`
- `hashes/before.sha256`, `hashes/after.sha256`, `hashes/review-artifacts.sha256`
- `downloads/openalex-1/`, `downloads/arxiv-1/`, `downloads/receipts.json`
