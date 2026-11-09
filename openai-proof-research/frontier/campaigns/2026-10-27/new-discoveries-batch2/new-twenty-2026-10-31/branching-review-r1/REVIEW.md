# Independent adversarial review: MathDB 347138 (branching-review-r1)

Reviewer: Claude Opus 5.5 review lane, 2026-11-03. This is a review, not an acceptance. Root decides.

Candidate: lane expanded-corpus-r135 claims that the family D_m (m ≥ 3) refutes Bang-Jensen–Bessy–Yeo Conjecture 35 ("rooted non-separating out-branching conjecture").

## Verdicts

| Gate | Verdict | One line |
|---|---|---|
| A. Statement fidelity | PASS | The conjecture, the definitions and W1 match both arXiv v1 and the published version. D_m contradicts no proved result of the source or of its companion paper. |
| B. Independent mathematics | PASS | I re-derived the proof for all m ≥ 3 and found no gap. My own brute force confirms m = 3 to 8. |
| C. Lean route | QUALIFIED_PASS | A cheap literal endpoint exists. The draft's mathematics is right, but it has 3 `sorry`s, one reversed fidelity remark and several fragile tactics. |
| D. Prior art | QUALIFIED_PASS | Bounded search: no resolution, refutation or restatement found. No stated example in the source or its companion has α = 2 and refutes Conjecture 35. |
| E. Significance and exclusion | FAIL | A genuine, literal refutation, but a routine adaptation: the source's own W1 obstruction (Theorem 19(b)) padded by the same authors' gadget-padding technique, plus about 4 new lines (case e = p3). |
| **Overall** | **EXCLUDE** (recommended) | A to D are clean. E fails under the campaign's credit standard (precedents 364079, 369221, 371637 and 374241), although this is a closer call than those (see E.4). |

If root weighs E.4 differently, the candidate is otherwise ready for Lean: PROCEED, at low cost (section C).

## Inputs and hashes

- I hashed every file of `../expanded-corpus-r135/` (163 files) before and after the review:
  - before: `hashes/inputs-before.sha256`
  - after: `hashes/inputs-after.sha256`
  - The two listings are byte-identical (the hash of each listing is `79983457e167ebea754c1b060976297be21b0e5f91d9ef91db3cff7d915c339a`).
- Key input hashes:
  - `candidates/347138/PROOF.md`: f3761298…71c2ae
  - `statement-correspondence.md`: 4966d025…6fd
  - `lean/NonSepBranching.lean`: 70e27030…86fd
  - `sources/347138.txt` (arXiv v1 text): 8b1b3fdc…601c
  - `sources/gc2022-springer.html`: 2cef35e3…b8964
  - `sources/bbhy-2003.02107.txt`: 7bea975f…fae6
  - `raw/347138.jsonl`: f8ee1691…235bf
  - `results.json`: 659bc5a0…334d
- I did not import or execute any discovery-lane script; I only read them.

## A. Statement fidelity: PASS

Line numbers below refer to `../expanded-corpus-r135/sources/347138.txt` (arXiv v1), unless they are marked "published" (that is `gc2022-springer.html`, Graphs Combin. 38 (2022) 187, DOI 10.1007/s00373-022-02589-6).

1. **Definitions.**
   - Non-separating: "D \ A′ is strongly connected" (abstract, lines 14–15).
   - Out-tree and out-branching: a connected subdigraph in which every vertex except the root s has exactly one entering arc, equivalently s reaches every vertex; an out-branching is a spanning out-tree (lines 30–34; identical in the published version).
   - λ(D): "the minimum out-degree of a proper subset of V" (line 153).
   - α(D): the largest X with D[X] arcless (line 160).
   - Digraphs follow Bang-Jensen–Gutin: no loops and no parallel arcs. Directed multigraphs are named separately (Theorem 16, Corollary 20). 2-cycles are allowed: W1 has p2↔p4, and Theorem 8(ii) singles out oriented graphs.
   - D_m is a simple loopless digraph with 2-cycles, so it is inside every reading.
2. **Conjecture 35** (line 1393; verbatim in the published version; verbatim in MathDB `raw/347138.jsonl`): ∃ L ∀ D (|V| ≥ L ∧ λ ≥ 2 ∧ α = 2 → ∀ s ∃ non-separating B_s^+).
   - The Prop to prove is the negation: ∀ L ∃ D, s with |V| ≥ L, λ(D) ≥ 2, α(D) = 2 and no non-separating B_s^+.
   - An integer L ≤ 0 behaves like L = 0, so a natural-number L in Lean is faithful.
   - D_{max(3, L)} with s = a_1 witnesses the negation.
3. **W1.**
   - The figure does not survive text extraction. The arcs come from the proof of Theorem 19(c): H = p1p2p3p4p1 and A(D′) = {p2p4, p4p2, p1p3} (arXiv line 426).
   - The published proof was revised. It lists exactly these seven arcs, adds "no other arc is incident to p1" and "p3p2 is not an arc", and says that a D which is not W1 must contain p4p3. So W1 is exactly the seven arcs used by the candidate.
   - My check (`logs/w1-finite.log`): W1 is semicomplete; in-degrees are (1, 2, 2, 2); λ(W1) = 1; no root has a non-separating out-branching, in agreement with Theorem 19(b) (line 374).
4. **No source-internal conflict.** D_m has δ⁻ = 2, λ = 2, α = 2, and it has non-separating out-branchings rooted in B. Against each result:
   - Theorem 8 (line 107): needs δ⁻ ≥ 5, or an oriented graph with δ⁻ ≥ 3, and asserts only some root. No conflict.
   - Theorem 19 and Corollary 20 (lines 365, 506): semicomplete digraphs only. D_m is not semicomplete.
   - Lemma 21 (line 513): needs δ⁻ ≥ 3. D_m (m ≥ 4) satisfies Corollary 18(A) with V1 = A, V2 = B, u1 = a_3 and u2 = p2, and its V2 block is exactly the W1 that the proof of Lemma 21 excludes via δ⁻ ≥ 3 (lines 518 and 533).
   - Theorem 23 (line 862): spanning trees, which are weaker. D_m has non-separating out-branchings from B anyway.
   - Theorem 5 (line 91, from [2]): some s, t. No conflict.
   - Conjecture 6 / companion Conjecture 29 (good pairs B_s^+, B_s^- for every s): D_m is not a counterexample. My search finds arc-disjoint B_s^+, B_s^- for every s ∈ A and m = 3 to 8 (`goodpair_same_root_found: true`).
   - Conjecture 34 (line 1389, some root) is not refuted, for all m. An explicit witness for root p3 is F = p3a_m, a_m a_{m-1}, …, a_2 a_1, a_1p1, p1p2, p2p4. D \ A(F) is strong:
     - A minus a Hamiltonian path is strong for m ≥ 3;
     - a_2p3 enters B;
     - p3p4, p4p1, p4p2, p1p3, p2p3 keep B strong;
     - p3a_1 returns to A.
   - The source's remark that the Proposition 12 class has a non-separating branching from every vertex (line 1391) concerns a different family.
5. **Fidelity remark on the lane's correspondence table.** Row "out-branching" of `statement-correspondence.md` (line 13) says the explicit `root` field "only makes the conjecture easier to satisfy". That is backwards. An extra conjunct in `OutBranching` shrinks the set of witnesses F, so the conjecture becomes harder to satisfy and its negation easier to prove. The definition is still faithful: an out-tree root has in-degree 0. The concern also disappears if the formal proof uses only `sub` and `spans`, which the draft's `not_nonsep` already does (see C.3).

## B. Independent mathematics: PASS

### B.1 Re-derivation for all m ≥ 3

Notation: A = {a_1, …, a_m}; B = {p1, p2, p3, p4}; entries a_1p1, a_2p3; exits p3a_1, p3a_m.

- **α = 2.**
  - D[A] is complete and D[B] = W1 is semicomplete, so any three vertices include two on one side, and those two are adjacent.
  - p2 has no arc to or from A, so {a_1, p2} is independent.
- **λ = 2.** Let X be a nonempty proper subset of V.
  - If ∅ ≠ X ∩ A ≠ A: the complete digraph alone gives |X ∩ A| · |A \ X| ≥ m − 1 ≥ 2 leaving arcs.
  - If A ⊆ X: put Y = B \ X ≠ ∅. The leaving arcs are the W1 arcs entering Y plus the entries with head in Y.
  - If X ⊆ B: the leaving arcs are the W1 arcs leaving X, plus 2 if p3 ∈ X (both exits).
  - These two finite tables (15 + 15 sets) do not depend on m. My table has minimum 2 in both (`logs/w1-finite.log`, `cut_table`).
  - X = B has exactly the two exits, so λ = 2 exactly. (This uses m ≥ 3 only in the first case, and so that a_1, a_2, a_m are three distinct vertices.)
- **No non-separating B_s^+ for s ∈ A.** Suppose F is an out-branching rooted at s and R = D \ A(F) is strong.
  - F and R each need an A→B arc. There are only two such arcs, so each contains exactly one entry. Write e for the head of F's entry and e′ for the head of R's.
  - A last-crossing argument gives:
    - (i) e reaches all of B in T := F ∩ A(W1);
    - (ii) e′ reaches all of B in W1 − T.
  - A first-crossing argument gives (iii): every vertex of B reaches p3 in W1 − T, because both exits have tail p3.
  - **Case e = p1, e′ = p3.** By (ii) and (iii), W1 − T is strong. T contains an out-branching T0 of W1 rooted at p1, and W1 − T0 ⊇ W1 − T is strong. This contradicts Theorem 19(b). I also checked the lane's direct argument (PROOF.md lines 71–73) step by step, and it is correct.
  - **Case e = p3, e′ = p1.** T contains an out-branching T0 rooted at p3.
    - p3p4 ∈ T0 (it is p3's only W1 out-arc), and p4p1 ∈ T0 (it is p1's only W1 in-arc).
    - If p2's parent is p1: W1 − T0 = {p1p3, p2p3, p2p4, p4p2}, so p1 reaches only p3, contradicting (ii).
    - If p2's parent is p4: p4 has no out-arc left, contradicting (iii).
    - This case is NOT covered by Theorem 19(b). In D_m, p1 has a second in-arc from A, so a W1 branching rooted at p3 is no longer trivially separating.
  - The argument uses only F ⊆ A(D) and "s reaches every vertex in F". It never uses the unique-parent or root-in-degree conditions. So it proves the stronger statement that no spanning subdigraph in which s reaches everything leaves a strong complement.

I found no gap. PROOF.md §5 (lines 56–83) is correct as written.

### B.2 Own brute force (written from the definitions; `scripts/`, `logs/`)

- **`dm_check.py 3 8 --goodpair`** (`logs/dm-check-m3-8.log`; wall 110 s, CPU 95 s, peak RSS 11.4 MB).
  - Method: for every root it searches ALL out-branchings, choosing a parent for each vertex and excluding cycles. The only pruning is a sound necessary condition: every vertex keeps an out-arc outside F.
  - It also checks λ by the source's cut definition and by the Lean-style "strong after deleting any one arc" definition, α by all vertex subsets, and same-root good pairs.
  - Result for every m = 3 to 8: λ = 2 (both definitions), α = 2, δ⁻ = 2. The failing roots are exactly a_1, …, a_m.
  - Out-branchings examined at m = 8: about 1.7 to 2.2 million per root.
  - Every root in B has a witness, and every root in A has a same-root good pair.
- **`verify_witnesses.py`**: separate set-based code re-validates all 24 witnesses for roots in B (`logs/verify-witnesses.log`: all valid).
- **`w1_finite.py`** (`logs/w1-finite.log`):
  - W1 basics as in A.3.
  - Controls: S4 and the complete digraph on 4 vertices have a non-separating branching from every root, as the source says (Figure 4, Corollary 20).
  - The finite lemma over all 128 subsets T ⊆ A(W1) has zero violations in both cases. The hypothesis holds for 44 subsets in case p1 and for 24 in case p3.
  - Neither conjunct alone suffices: 3 and 4 subsets survive in case p1, 3 and 2 in case p3. Both conditions (ii) and (iii) are therefore needed.

### B.3 Robustness (`robust.py`, `robust2.py`)

- **Other attachments of W1** (`logs/robust-w1.log`): all 16 × 16 patterns of entry heads and exit tails, at m = 3 and m = 4. 49 patterns have λ ≥ 2 and α = 2. Only one pattern makes any root in A fail: entry heads {p1, p3} and both exit tails at p3. That is exactly D_m (and its entry-swapped twin).
- **Does the failure need W1?** (`logs/robust-semi.log`): all 729 labelled semicomplete digraphs on 4 vertices × 256 patterns, at m = 3. Of these, 47,604 configurations have λ ≥ 2 and α = 2.
  - The only isomorphism class with a failing root in A is W1: 48 labelled hits, every one with all of A failing.
  - W2, the other Theorem 19 obstruction, never works.
  - This agrees with the lane's 24 unordered hits.
- **Fragility** (`logs/robust-extra.log`, m = 3 and 4): adding any single extra entry, or any exit whose tail is not p3, destroys the failure. Extra exits from p3 keep it, as the proof predicts.
- **Companion-style dense padding** (`logs/robust2-dense.log`, m = 3 to 5), as in arXiv:2003.02107 Proposition 23:
  - all A → p1 and all p3 → A: λ ≥ 2 and α = 2, but no root fails;
  - all A → {p1, p3} and all p3 → A: λ ≥ 2 and α = 2, but no root fails;
  - all A → p3 and all p3 → A: λ = 1.
  - So the failure needs the sparse 2 + 2 attachment. It is not the companion paper's padding verbatim.

All runs were single sequential `python3 -I` processes through `scripts/run_capped.sh`: taskset to 2 CPUs, prlimit CPU 120 s, address space 1.5 GiB, timeout 140 s, MALLOC_ARENA_MAX = 2. Peak RSS was at most 12.3 MB. Resource receipts are in `logs/*.resources.txt`. No background job is left.

## C. Lean route: QUALIFIED_PASS (no Lean run here)

### C.1 Recommended literal endpoint

`theorem not_conjecture35 : ¬ Conjecture35`, with:

- **Digraph:** `V : Type`, `[Fintype V]`, `E : V → V → Prop`, plus a looplessness hypothesis.
- **λ(D) ≥ 2, stated literally as the source's cut definition:** `∀ X : V → Prop, (∃ x, X x) → (∃ y, ¬ X y) → ∃ u₁ v₁ u₂ v₂, (u₁, v₁) ≠ (u₂, v₂) ∧ E u₁ v₁ ∧ X u₁ ∧ ¬ X v₁ ∧ E u₂ v₂ ∧ X u₂ ∧ ¬ X v₂`.
  - Optionally, also prove the draft's `TwoArcStrong` from it with a generic 10-line lemma: if u cannot reach v in E − e, the reachable set has e as its only leaving arc. Then both readings are covered.
- **α = 2:** as in the draft's `IndepTwo` (an independent pair exists, and no independent triple).
- **OutBranching:** as in the draft (literal). Prove the core lemma for the weaker hypothesis `F ⊆ E ∧ ∀ v, ReflTransGen F s v`. The endpoint then holds for every reading of "out-branching" (B.1, last bullet).
- **Vertex type:** `Fin (k+3) ⊕ Fin 4`, with k := L. `Fintype.card` is k + 7.
- **Axioms:** only propext, Classical.choice and Quot.sound (classical choice of the 7 arc bits). No `native_decide`.

### C.2 Cheapest proof plan

1. **α.** Case-split on the sides (`Sum`) of three vertices; two lie on one side. Side A: `i ≠ j` gives an arc. Side B: `w1_semicomplete` by `decide`. The independent pair is (inl 0, inr 1).
2. **λ for general m** (the only general-m finite-combinatorics part). Given X with a member and a non-member:
   - (a) If some A-vertex is in X and some is not, say i ∈ X and j ∉ X: pick a third index l ∉ {i, j}, which exists since k + 3 ≥ 3 (choose among 0, 1, 2). The two arcs are i→j together with l→j if X l, or i→l if not.
   - (b) Otherwise A ⊆ X or A ∩ X = ∅. Case-split classically on the four Booleans X(inr q) and exhibit the two arcs from the 15 + 15 table (`logs/w1-finite.log`).
   - This avoids the lane's contracted-quotient bridge entirely.
3. **Crossing lemmas.** `last_cross` and `first_cross` (draft lines 62–84) are correct in content. In `first_cross`, replace the fragile `simpa [flip, and_comm, …]` with an explicit `ReflTransGen.mono`.
4. **Gluing.** Draft lines 206–286 (`entryF`, `entryR`, `Treach`, `Rreach`, `Rback`, `toB`) follow PROOF.md Steps 1 to 3 and use only `hF.sub` and `hF.spans`.
5. **Finite W1 step: closed-set certificates, which are easier than the draft's Bool reachability.**
   - Let `b i := decide (T arcᵢ)` (classical) for the 7 W1 arcs, and prove `T p q ↔ W1 p q ∧ bit(p, q)` by `fin_cases`.
   - Kernel-decide, over the 7 Booleans quantified separately as `∀ b₀ … b₆ : Bool` (not `Fin 7 → Bool`, whose Pi-type `Fintype` reduction is very slow in the kernel), the disjunction: there is a set S : Fin 4 → Bool closed under the T-relation that contains e but misses some q, OR one closed under W1 − T that contains e′ but misses some q, OR one closed under the reversed W1 − T that contains p3 but misses some q. Encode the existential over S as 4 Booleans or as `Fin 16`.
   - The bridge is the one-line generic lemma `ReflTransGen R a b → S a → (∀ x y, S x → R x y → S y) → S b`.
   - This removes `reachB`, `reachB_closed` and the missing reversed-relation closure lemma (draft lines 116–143).
   - Size: 2 cases × 128 bit patterns × at most 3 × 16 sets.

### C.3 What is right or wrong in the uncompiled draft (`lean/NonSepBranching.lean`)

**Right:**
- The definitions are faithful (lines 25–57).
- `Em` encodes D_m exactly with m = k + 3 (lines 151–155).
- The crossing structure and Steps 1 to 3 (lines 206–286) are mathematically correct.
- The endpoint wiring (lines 306–311) is right.

**Wrong or incomplete:**
1. Three `sorry`s: `indepTwo_Em` (line 179), `twoArcStrong_Em` (line 186) and both finite cases (lines 287 and 302).
2. `w1_finite` (lines 123–131) depends on a closure lemma for the reversed relation that is not stated. Its own comment admits this.
3. `decide` over `Fin 7 → Bool` (lines 116–129) is likely to be very slow or time out in the kernel.
4. `card_Vm` (line 158): `simp [Vm]; omega` may fail with "no goals" if `simp` closes the goal.
5. `irrefl_Em` (line 163): `decide` may not find a `Decidable` instance through the `Em` match without `show ¬ W1 p p` or `simp only [Em]`.
6. The `rcases … with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩` calls on `Em k (inl i) (inr q)` (lines 218, 228, 279 and 284) may need `simp only [Em] at h` first.
7. The fidelity rationale in `statement-correspondence.md` line 13 is reversed (A.5).

**Estimated cost:** small. λ is about 100 to 200 lines of case analysis; the finite step is one `decide` plus a bridge lemma.

## D. Prior art: QUALIFIED_PASS (bounded)

All downloads are in `downloads-r1/`, hashed in `hashes/downloads.sha256`, and were fetched on 2026-11-03.

- **OpenAlex.**
  - Records: W3039611750 (arXiv) and W4308784876 (GC 2022). Both show cited_by_count 0, and `cites:` filters on both return 0 works.
  - The Springer page shows "1 Citation", which I could not identify: Crossref is denied, and I did not try it.
  - Keyword searches ("non-separating out-branching", "non-separating branching", out-branching with "independence number 2", arc-disjoint branchings with independence number, 2020 onwards) found the source, the companion JGT paper (W4200448177), Gu–Gutin–Li–Shi (smallest digraphs without good pairs), Bang-Jensen–Wang 2024 (good pairs in compositions and semicomplete digraphs), Ai–Hao–Li–Shao 2025 (semicomplete split digraphs), and Bang-Jensen–Yeo 2026, "Acyclic orientations of mixed graphs" (arXiv:2609.32403).
  - I read the full text of arXiv:2609.32403. Its Section 5 is about non-separating out-branchings in acyclic digraphs in the underlying-connected sense. It neither mentions nor cites Conjectures 34 or 35, nor arXiv:2007.02834.
  - None of these works resolves, refutes or restates Conjecture 34 or 35.
- **Companion paper arXiv:2003.02107** (`sources/bbhy-2003.02107.txt`). Checking the stated properties of its examples:
  - Proposition 9 (line 148): co-bipartite, but only strong (λ = 1).
  - W (Proposition 22, line 681): a single 8-vertex digraph with α = 2 and λ = 2.
  - W′_n (Proposition 23, line 692): α = 3.
  - W_S (Theorem 24, line 703): α ≤ 7.
  - H4: α = 4.
  - Figure 12: a multigraph, and a single example.
  - None is an α = 2 infinite family. By Theorem 5, no λ ≥ 2, α = 2 digraph lacks good pairs entirely. A non-separating B_s^+ needs a same-root good pair, and the companion paper conjectures (Conjecture 29) that these always exist. So no stated example in the companion refutes Conjecture 35.
  - The source's own D̃ (6 vertices, Proposition 24) and D̂ (8 vertices) are single small digraphs.
- **Registries.**
  - OpenAI/math HEAD is still 4eaee87548250b2682affda7d05d947c05554bae (2026-10-30). A path screen of its recursive tree (truncated by GitHub) and of `sources/preprints-tree.json` (13,223 paths) found no digraph, branching or independence-number item.
  - Omega HEAD is now ab0073eb… (2026-11-03 18:10Z). The lane saw a41b3dc7, so the head has moved. I did not re-screen the newest delta. This is the main residual gap in D.
- **Limits.** These are bounded keyword and citation screens. They are not an exhaustive literature review.

## E. Significance and exclusion screen: FAIL (EXCLUDE recommended)

E.1 **Genuine?** Yes, in the narrow sense:
- the statement is correct and literal;
- the family is arbitrarily large, made of simple digraphs, and meets the exact hypotheses (λ = 2, α = 2);
- it is not a wording, domain or endpoint artefact;
- it is not degenerate;
- it does not conflict with any source theorem.

E.2 **What is new beyond the sources.** Every structural ingredient is the authors' own:
- The obstruction W1 and its proof: Theorem 19(b). Case e = p1 IS Theorem 19(b).
- The "exactly two arcs in both directions, so each partition class takes exactly one" counting: the source's Proposition 12 proof (line 224).
- Padding a small obstruction with a large semicomplete digraph and restricting the branchings to the gadget, so that roots far from the gadget fail: the same authors' companion paper, Proposition 23 (lines 692–700) and Theorem 24 (line 710), and Proposition 9. Proposition 23 is the rooted good-pair analogue of exactly this argument.
- The co-bipartite structure with a W1 block: the source's Corollary 18(A), with W1 explicitly flagged as the exceptional block in the proof of Lemma 21 (lines 518 and 533).

The genuinely new mathematics amounts to:
- (i) noticing that a semicomplete gadget keeps α = 2 under co-bipartite padding;
- (ii) choosing the attachment, which is a 16-option search once λ forces an entry at p1 and an exit at p3;
- (iii) the case e = p3, about 4 lines.

E.3 **Precedent.** Root excluded:
- 364079: a counterexample verified by the source's own Theorem 3.4;
- 369221 and 371637: short bridges from the source's own lemmas;
- 374241: a one-paragraph bridge, even though a later paper still listed the statement as a conjecture.

The D_m refutation has the same shape: a short bridge from source ingredients to a conjecture the authors left open. Two further points weigh against significance:
- Only the rooted strengthening (Conjecture 35) falls. The main Conjecture 34 is untouched, and so are the substantive related conjectures: same-root good pairs (Conjecture 6/29) hold in D_m.
- The family sits at δ⁻ = 2 and λ = 2, exactly the boundary that the source's own D̃ already shows to be delicate.

E.4 **Why this is closer than the precedents (for root's judgment).**
- The bridge is not black-box. Case e = p3 is outside Theorem 19(b).
- The companion paper's dense padding of W1 does not work (B.3).
- The attachment is unique: one isomorphism class among 47,604 eligible configurations, with W2 never working.
- Three experts stated Conjecture 35 after proving Theorem 19, while knowing the padding technique, and they checked their own infinite class.

If root regards these as sufficient, A to D impose no further obstacle and the Lean cost is small. My recommendation stays EXCLUDE: the new argument beyond Theorem 19(b) and the companion's padding technique is a few lines plus a tiny search, which is what the campaign standard calls a routine adaptation.

## Files

- `TASK.txt`, `launch.json`: the task (given).
- `REVIEW.md`, `review.json`: this review.
- `scripts/`: `run_capped.sh`, `dm_check.py`, `verify_witnesses.py`, `w1_finite.py`, `robust.py`, `robust2.py` (all written in this lane).
- `logs/`: full stdout logs and `*.resources.txt` receipts (peak RSS, CPU, wall time, exit status, script and log hashes).
- `hashes/`: `inputs-before.sha256`, `inputs-after.sha256`, `downloads.sha256`, `scripts-logs.sha256`.
- `downloads-r1/`: OpenAlex JSON, the GitHub HEAD and tree JSON, and the arXiv:2609.32403 abstract page and PDF and text.
- `tmp/`: the lane-local TMPDIR (empty).
