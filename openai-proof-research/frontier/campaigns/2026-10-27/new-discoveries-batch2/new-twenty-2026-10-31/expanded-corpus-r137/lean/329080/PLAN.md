# 329080 Lean plan (UNCOMPILED; nothing in this directory has been compiled)

All files here are UNCOMPILED drafts. Claude lane restriction: no Lean, lake or leanchecker was run. The drafts contain `sorry` placeholders that mark proof obligations. They are skeletons for the root or a Sol worker, not certificates.

## Statement correspondence

| Source / MathDB notion | Lean object | Bridge needed |
|---|---|---|
| Chord diagram = double-occurrence word with a base point | `Diagram n` (word `Fin (2n) → Fin n`, each letter exactly twice) | None; this is the source's own encoding (Section 2). |
| Equivalence "cyclic permutations, reversal, symbol renaming" | `Equivalent` | Literal transcription of Section 2. |
| Thickened diagram: each band end attached to the inner or outer boundary circle (4^n surfaces) | `Sides n := Fin (2n) → Bool` | Bijection between attachment choices and Boolean side vectors (literal). |
| b(F) = number of boundary components | `boundary` (dart model: cycles of σ_c ∘ τ plus empty circles) | **Semantic bridge.** The topological count is replaced by the standard ribbon-graph face count. The source itself computes genus ranges by permutation cycle counts (Section 3.2, "algorithm … by means of cycle decompositions of permutations"). The model reproduces the source's GR₁…GR₆ table and the 6n half-edge ribbon model on all 995,572 cases with n ≤ 5. Root must decide whether this combinatorial definition counts as literal (no surface theory is available in mathlib). |
| g(F) = (n − b + 2)/2 | `genus` | Source Lemma 3.1, used as the definition. |
| gr(D) | `genusRange D : Set ℤ` | Literal. |
| (123123)(44 ⋯ nn) | `r3Block n` | Literal. |
| "for any n ≠ 4 there is a unique …" | `conjecture_3_4` for n ≥ 3, n ≠ 4; `literal_false_n1` and `literal_false_n2` for n = 1, 2 | The literal n = 1, 2 cases are false (source table). The endpoint proves the intended range and states the defect explicitly. |

## Proof obligations, in suggested order

1. **Computable core.** Implement `partner`, `nextSame`, `sigma` and `tau` computably. Prove `sigma` and `tau` are permutations. Prove `numCycles` (SameCycle quotient) equals the "orbit-minimum" count used by `dartFaces`, so `decide` can run on concrete words.
2. **Lemma 1 (`boundary_delete`).** The general cycle-count ± 1 under successor transposition. Mathlib has `Equiv.Perm.SameCycle` and `swap`. A lemma of the form `card_cycles (σ * swap a b) = card_cycles σ ± 1` according to `SameCycle σ a b` probably needs to be proved locally. This is the largest piece; estimate 400–800 lines.
3. **Corollary 2 (heredity).** Iterate Lemma 1 over a chord subset; use min/max over `Sides`.
4. **Lemma 3 (bipartite ⇒ genus 0).** Induction on n: remove an innermost chord of the inner side (or outer side), using Lemma 1's +1 case, which is a fixed-point face as in the transfer computation.
5. **Lemma 4 (`base5_check`).** Transcribe `P` and `dart_faces` from `scripts/chord_cert.py` and `scripts/chord_dart.py`. Enumerate the 945 standard words and check by `decide` / `rfl`. The witness table `Base5Data.witnesses` has 453 entries. Then bridge from standard words to arbitrary 5-chord sub-diagrams via renaming invariance (renaming preserves `boundary` trivially; the standard form only fixes the letter names).
6. **Lemma 5 (R3 not planar)** and the base states of Lemma 6: finite `decide` over 2⁶ masks.
7. **Lemma 6 (transfer).** The dart-algebra computation in `outputs/329080-proof.md`, as an induction on m.
8. **Main argument.** Shortest odd cycle in the interlacement graph (`SimpleGraph`; a shortest odd closed walk gives an induced odd cycle), five-vertex windows, the pair argument, the single-arc argument, and the rotation/renaming to `r3Block`.

## Cost estimate and risk

- Moderate to heavy: roughly 1500–3000 lines. The finite part is cheap.
- The general permutation surgery (Lemma 1 and Lemma 6) and the final word-rotation bookkeeping dominate.
- Acceptance risk: the topological-to-combinatorial bridge for b(F), and a possible "routine heredity" judgement.
