/-
UNCOMPILED DRAFT — lane expanded-corpus-r137 (Claude), 2026-11-03. Not compiled; see PLAN.md.

Endpoints for MathDB 329080 (Conjecture 3.4 of arXiv:1410.6148).
  * `literal_false_n1`, `literal_false_n2`: the printed "for any n ≠ 4" fails at n = 1, 2 (no diagram has
    genus range {1,2}); this matches the source's own table GR₁ = GR₂ = {{0,1}} and is a zero-credit
    wording defect, recorded only for fidelity.
  * `conjecture_3_4`: the intended statement for every n ≥ 3, n ≠ 4 (existence and uniqueness up to
    equivalence of the genus-range-{1,2} diagram, and it is (123123)(44⋯nn)).
-/
import «Defs»

namespace ChordGenus

theorem literal_false_n1 : ∀ D : Diagram 1, genusRange D ≠ {1, 2} := by
  sorry -- DRAFT: finite (2 standard words? only "00"), decide over 4 side assignments

theorem literal_false_n2 : ∀ D : Diagram 2, genusRange D ≠ {1, 2} := by
  sorry -- DRAFT: finite (3 standard words "0011","0101","0110"), decide over 16 assignments each

/-- Main endpoint: Conjecture 3.4 for all n ≥ 3, n ≠ 4. -/
theorem conjecture_3_4 (n : ℕ) (hn : 3 ≤ n) (h4 : n ≠ 4) :
    genusRange (r3Block n hn) = {1, 2} ∧
    ∀ D : Diagram n, genusRange D = {1, 2} → Equivalent D (r3Block n hn) := by
  sorry -- DRAFT: Proof.lean assembles Lemmas 1–6 of outputs/329080-proof.md

end ChordGenus
