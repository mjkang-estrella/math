# Independent adversarial review of MathDB 374241 (r3)

Reviewer: Claude Opus 5.5, a separate instance from the candidate's lane. No child agents were used. Date: 2026-11-02.
Target: arXiv:2604.16188v1, Conjecture 4.16: R_cyc(S_a, P_b^mon) = 1 + (a−1)(b−2) for all a ≥ 3 and b ≥ 4.

**Recommendation: REJECT for credit.** The theorem is true, the candidate proof is correct and the Lean endpoint is faithful. But the upper bound is a one-paragraph bridge from the source's own Corollary 4.19 (Theorem 4.18), so the full conjecture falls under the excluded "one-paragraph bridge from source lemmas" pattern, like the sibling 374246.

| Gate | Verdict |
|---|---|
| A. Source and MathDB fidelity | PASS |
| B. Ordinary mathematics | PASS |
| C. Lean audit (source plus root replay; no recompilation) | PASS |
| D. Prior art (publication) | PASS: no published resolution found |
| E. Significance | **FAIL**: one-paragraph bridge from source Corollary 4.19 |

## Input binding

I hash-bound 335 input files (the root check JSON, `expanded-corpus-r112/` and `cycramsey-parent-check-r1/`) before and after the review. The two lists are identical (`receipts/input-hashes-{before,after}.txt`). All eight hashes in `cycramsey-root-check-r1.json` match. The parent-check `src/Cyc*.lean` files are byte-identical to `formal/Cyc*.lean`.

## A. Fidelity

* **R_cyc.** Source line 331: R_cyc is the least n such that every k-colouring of K_n contains H_j in colour j. The embedding φ must have some t with (φ(t), …, φ(|H_j|−1), φ(0), …, φ(t−1)) increasing.
* **Stars.** S_n^sc is the star of order n with centre 0. Before Proposition 2.2 the source says stars of the same order are equivalent cyclically.
* **Paths.** P_n^mon has edges {i, i+1}.
* **MathDB text.** It has the same quantifiers and formula. Its phrase "star with parameter a" means order a; Table 11 and my searches confirm this.
* **Lean definitions.**
  * `Colouring n := Sym2 (Fin n) → Fin 2`. Diagonal entries are never queried, because H is irreflexive and φ is injective.
  * `IsCyclicEmbedding φ := Injective φ ∧ ∃ t, StrictMono (j ↦ φ (t + j))`. Fin addition is mod k, so this is exactly the rotated sequence.
  * `ContainsCyc` uses `c s(φ u, φ v) = i`, which is unordered, so orientation is irrelevant.
  * `CycRamseyProp` checks H₁ = star in code 0 (colour 1) and H₂ = path in code 1 (colour 2), in the correct argument order.
  * `cycRamsey := sInf …`. The endpoint proves `IsLeast` and then uses `csInf_eq`, so the empty-set degeneracy is excluded. The lower-bound half also shows that `ContainsCyc` is not trivially true.
  * `startStar` and `monPath` (via `fromRel`) are as in the source.
* **Shortcut check.** `scripts/defcheck.py` compares the literal definition, for every star-centre position, with the degree and clockwise-path shortcuts on 4350 random instances with n ≤ 7. There were 0 mismatches.

## B. Mathematics

**Theorem A.** I re-proved it independently and every step holds:

1. J, K ≤ t+1.
2. The runs at offsets 1..J−1 and N−K+1..N−1 are disjoint iff J+K ≤ N+1, which holds because 2t+2 ≤ (t+1)(b−2)+2 for b ≥ 4. So J+K ≤ t+2.
3. The span is at least N when there is no path, and at most (t+2)+(b−3)(t+1) = N. Equality is forced, and J(g(s)) = t+1 because b ≥ 4.
4. The orbit from u = g(0) wraps to u−1 at k = b−2. There J(u−1) ≥ 2, which contradicts K(u) = 1.

The edge cases t ≥ 1 and b ≥ 4 are used exactly where claimed. The lower bound (source Theorem 4.5 block colouring) and the star application are also correct.

**Own computation.** `scripts/rcyc_search.py` is a pure-Python exhaustive backtracking search with rotation symmetry breaking (`logs/rcyc-grid.log`). It finds SAT at N−1 and UNSAT at N for these cases:

* (a, b) = (3, 3..9)
* (4, 3..6)
* (5, 3..5)
* (6, 3..4)
* (7, 4), SAT at n = 12 only

That is 16 UNSAT and 17 SAT verdicts, all equal to Table 11, including the b = 3 column that the conjecture excludes. Three runs hit the 140 s wall limit and give no verdict: (7, 4) at n = 13 and (8, 4) at n = 14 and 15.

## C. Lean (source review plus root evidence; nothing was compiled here, by instruction)

* **Sources.** None of the five modules contains sorry, admit, axiom, unsafe, partial, native_decide, implemented_by, extern, opaque, set_option, notation, macro, instance or attribute. The endpoint is
  `cycRamsey_startStar_monPath (a b) (3 ≤ a) (4 ≤ b) : cycRamsey (startStar a) (monPath b) = 1 + (a−1)*(b−2)`.
  Lean's `theoremA` is the colouring form of Theorem A. It bridges to the endpoint through `nonBlue_mod`.
* **Root run.** Root's `run.py` asserts there are no prebuilt .olean files, then runs strict `-DwarningAsError=true` builds (rc 0, empty logs) and `leanchecker` per module (rc 0). Lean is 4.34.1 at commit 5045d005.
* **Audit log.** I parsed `build-AuditFull.log` after joining wrapped lines:
  * There are 148 DECL records: CycDefs 10, CycRot 18, CycLower 38, CycUpper 56, CycMain 26.
  * None is unsafe or partial, and every one has a body.
  * Axioms are always within {propext, Classical.choice, Quot.sound}. The endpoint uses exactly these three.
* **Trust limits.** The Mathlib cache was not rebuilt, and `leanchecker` was not run with `--fresh`.
* **Negative controls.** Both are only syntactic: an arithmetic mismatch (7 ≠ 5) and a hypothesis mismatch (4 ≤ 3). I propose four semantic controls:
  1. Prove cycRamsey(startStar 4, monPath 3) = 5.
  2. Refute an ordered-only mutation for (3, 4) at n = 5.
  3. Give an example of `ContainsCyc` that needs t ≠ 0.
  4. Refute a same-colour mutation.

  Swapping both colours is not a useful control, because R(H₁, H₂) = R(H₂, H₁).

## D. Prior art

* **Source versions.** arXiv 2604.16188 has only v1 (17 Apr 2026).
* **Follow-up paper.** I read the body of arXiv 2607.06817v2 by Damnjanović and Đorđević (12 Jul 2026), who share an author with the source. Its Table 2 still marks the cyclic star versus monotone path case "conjectured [4, Conjecture 4.16]". It marks star versus monotone cycle "solved [4, Corollary 4.19]".
* **Registries, checked via /commits/HEAD only.**
  * openai/math is at 4eaee875, unchanged.
  * Omega has moved to **2c68091d** (2026-11-02T21:39Z). Its HEAD commit's 300 files contain no relevant paths. Commits between e51c7d81 and 2c68091d were not screened.
* **Web searches.** I ran three searches (two standard, one extended). None found a Dirac-type theorem for clockwise paths in cyclically ordered or convex geometric graphs.
* **Unread bodies.** These are listed in `receipts/web-and-registry-receipts.json`.

## E. Significance: FAIL

**The bridge (objection O1).** Let N = 1 + (a−1)(b−2), and take a colouring of K_N with no colour-1 cyclic S_a. Then every vertex has colour-1 degree at most a−2.

1. Apply source Corollary 4.19 with b′ = b−1 ≥ 3. Its upper half is Theorem 4.18 plus Proposition 1.5, and it gives R_cyc(S_a, C_{b−1}^mon) = N. So there is a colour-2 cycle x₁ < … < x_{b−1} whose cyclically consecutive pairs are all colour 2.
2. Each of the N − (b−1) = (a−2)(b−2) other vertices y lies in exactly one gap (x_i, x_{i+1}).
3. If {y, x_i} has colour 2, then x_{i+1}, …, x_{b−1}, x₁, …, x_i, y is a colour-2 cyclic P_b. If {y, x_{i+1}} has colour 2, then y, x_{i+1}, …, x_i is one.
4. Otherwise x_i is colour-1 adjacent to both neighbouring gaps, so g_{i−1} + g_i ≤ a−2.
5. Summing over i gives 2(a−2)(b−2) ≤ (b−1)(a−2), i.e. b ≤ 3. This contradicts b ≥ 4.

**Computational check.** `scripts/bridge_check.py` enumerates every P_b-free colouring with colour-1 degree at most a−2, in 12 configurations, and finds 0 violations of the bridge inequality (`logs/bridge-check.log`).

**Assessment.** Together with source Theorem 4.5 for the lower bound, this proves Conjecture 4.16 with one paragraph on top of source results. That is the excluded pattern, matching precedents 369221, 374488 and 371637 and the same-paper sibling 374246, which was excluded as a bridge from source Theorems 1.3 and 4.1. Theorem A is equivalent to the Ramsey statement via t = a−2 and follows from the same bridge.

The candidate's statement that the upper-bound argument is "not in the source" and that the source "has only the ordered upper bound" overlooks Corollary 4.19 and Theorem 4.18.

**Counter-consideration for root.** A source author still listed 4.16 as open in July 2026. The standard, however, judges whether the result is derivable from the source, not whether anyone noticed.

## Next actions

* Root: verify O1 independently and record 374241 as EXCLUDED: one-paragraph bridge from source Corollary 4.19 / Theorem 4.18.
* Optionally keep the Lean development as a verified formalization with no credit.
* Screen the other conjectures of 2604.16188 for the same kind of bridge before investing in them.

## Files

* `review.json` (keyed "374241")
* `scripts/`: `hash_inputs.py`, `wrap.sh`, `defcheck.py`, `rcyc_search.py`, `bridge_check.py`
* `logs/`: `defcheck.log`, `rcyc-grid.log`, `bridge-check.log`
* `receipts/`: `start-utc.txt`, `input-hashes-before.txt` and `-after.txt`, `http-2026-11-02/` (registry HEAD JSON and arXiv abs page, with sha256), `dl-2607.06817/` (follow-up abs, HTML and text), `web-and-registry-receipts.json`

**Resources.** No Lean, SAT binaries or Java were run. All computation was pure Python under `wrap.sh`, one process at a time. There was no git and no ledger edit, and no background jobs remain.
