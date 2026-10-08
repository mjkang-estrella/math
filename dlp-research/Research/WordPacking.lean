import Research.WordQueryData

/-! Arithmetic and representation lemmas for the descending Horner decoder.
These are not an executed decoder, trace count, or query-program refinement. -/
namespace Research.WordPacking

/-- Numeric value of the encoded bit at a little-endian position. -/
def bitValue (value position : Nat) : Nat := value / 2 ^ position % 2

theorem bitValue_bound (value position : Nat) : bitValue value position < 2 :=
  Nat.mod_lt _ (by decide)

theorem horner_step (value remaining : Nat) :
    2 * (value / 2 ^ (remaining + 1)) + bitValue value remaining =
      value / 2 ^ remaining := by
  unfold bitValue
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  exact Nat.div_add_mod _ _

theorem horner_initial (width value : Nat) (hv : value < 2 ^ width) :
    value / 2 ^ width = 0 := Nat.div_eq_of_lt hv

theorem horner_final (value : Nat) : value / 2 ^ 0 = value := by simp

/-- Each separate checked multiply and add fits, including full word width.
There is no final stored weight 2^W. -/
theorem horner_intermediates (W value remaining : Nat) (hv : value < 2 ^ W) :
    2 * (value / 2 ^ (remaining + 1)) < 2 ^ W ∧
    2 * (value / 2 ^ (remaining + 1)) + bitValue value remaining < 2 ^ W := by
  have hs := horner_step value remaining
  have hd := Nat.div_le_self value (2 ^ remaining)
  omega

theorem bitValue_bool (value position : Nat) :
    (if bitValue value position == 1 then 1 else 0) = bitValue value position := by
  have h := bitValue_bound value position
  split <;> simp_all <;> omega

/-- Index semantics of the actual public encoding, not a substitute encoding. -/
theorem bits_getElem (width value i : Nat) (hi : i < width) :
    (Research.bits width value)[i]'(by rw [WordQueryData.bits_length]; exact hi) =
      (bitValue value i == 1) := by
  induction width generalizing value i with
  | zero => omega
  | succ width ih =>
    cases i with
    | zero => simp [Research.bits, bitValue]
    | succ i =>
      have hii : i < width := by omega
      simpa [Research.bits, bitValue, Nat.pow_succ', Nat.div_div_eq_div_mul] using
        ih (value / 2) i hii

end Research.WordPacking
