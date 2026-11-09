import Antimagic4ALeafBlocks
namespace Antimagic.Round4A

/-- The elementary parity shell, before assigning shell intervals to rows. -/
def shellEntry (Z r : ℕ) : ℕ := if r % 2 = 0 then Z - (1 + r / 2) else Z + (1 + r / 2)

theorem shellEntry_range (Z R r : ℕ) (hR : R < Z) (hr : r < 2 * R) :
    Z - R ≤ shellEntry Z r ∧ shellEntry Z r ≤ Z + R ∧ shellEntry Z r ≠ Z := by
  unfold shellEntry
  split_ifs <;> omega

theorem shellEntry_injective (Z R : ℕ) (hR : R < Z) :
    Function.Injective (fun r : Fin (2 * R) => shellEntry Z r.val) := by
  intro r u he
  have hr := r.isLt
  have hu := u.isLt
  change shellEntry Z r.val = shellEntry Z u.val at he
  unfold shellEntry at he
  apply Fin.ext
  split_ifs at he <;> omega

/-- Explicit inverse: the centered interval with its center deleted is
covered without any finite enumeration. -/
theorem shellEntry_unique (Z R x : ℕ) (hR : R < Z)
    (hx : Z - R ≤ x ∧ x ≤ Z + R ∧ x ≠ Z) :
    ∃! r : Fin (2 * R), shellEntry Z r.val = x := by
  have hex : ∃ r : Fin (2 * R), shellEntry Z r.val = x := by
    by_cases h : x < Z
    · refine ⟨⟨2 * (Z - x - 1), by omega⟩, ?_⟩
      simp only [shellEntry, show 2 * (Z - x - 1) % 2 = 0 by omega, ite_true,
        show 2 * (Z - x - 1) / 2 = Z - x - 1 by omega]
      omega
    · refine ⟨⟨2 * (x - Z - 1) + 1, by omega⟩, ?_⟩
      simp only [shellEntry, show (2 * (x - Z - 1) + 1) % 2 ≠ 0 by omega, ite_false,
        show (2 * (x - Z - 1) + 1) / 2 = x - Z - 1 by omega]
      omega
  obtain ⟨r, hr⟩ := hex
  refine ⟨r, hr, ?_⟩
  intro u hu
  exact shellEntry_injective Z R hR (hu.trans hr.symm)

theorem shellEntry_pair (Z b : ℕ) (hb : b + 1 ≤ Z) :
    shellEntry Z (2 * b) + shellEntry Z (2 * b + 1) = 2 * Z := by
  simp only [shellEntry, show 2 * b % 2 = 0 by omega,
    show (2 * b + 1) % 2 ≠ 0 by omega, ite_true, ite_false,
    show 2 * b / 2 = b by omega, show (2 * b + 1) / 2 = b by omega]
  omega

/-- Exact agreement with the inherited internal formula, including its patch. -/
theorem internalLabel_shell (t n h i : ℕ) (hh : h ≠ 1) :
    internalLabel t n h i = shellEntry (center t n) (offset t n h + patchedIndex t h i) := by
  simp only [internalLabel, hh, ite_false, shellEntry]

open Finset in
/-- Any even consecutive shell segment has constant total weight. -/
theorem shellEntry_sum (Z B s : ℕ) (hB : B + s ≤ Z) :
    (∑ j ∈ range (2 * s), shellEntry Z (2 * B + j)) = (2 * s) * Z := by
  rw [Round3.sum_range_pairs]
  calc
    _ = ∑ _b ∈ range s, 2 * Z := by
      apply sum_congr rfl
      intro b hb
      rw [show 2 * B + 2 * b = 2 * (B + b) by omega,
        show 2 * B + (2 * b + 1) = 2 * (B + b) + 1 by omega]
      exact shellEntry_pair Z (B + b) (by have := mem_range.mp hb; omega)
    _ = _ := by simp only [sum_const, card_range, smul_eq_mul]; nlinarith

#print axioms shellEntry_unique
#print axioms internalLabel_shell
#print axioms shellEntry_sum
end Antimagic.Round4A
