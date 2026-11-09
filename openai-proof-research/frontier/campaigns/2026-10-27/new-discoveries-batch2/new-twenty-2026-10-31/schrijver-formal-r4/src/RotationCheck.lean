import BridgeTransport
namespace Schrijver
set_option autoImplicit false

def rotationBitsCheck (n t a b : ℕ) : Bool :=
  (List.range n).all fun i => a.testBit i == b.testBit ((i+t)%n)

theorem rotationBitsCheck_sound {n : ℕ} [NeZero n] {t : Fin n} {a b : ℕ}
    (hb : b < 2^n) (h : rotationBitsCheck n t.val a b = true) :
    rotateMask n t a = b := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < n
  · let i : Fin n := ⟨j, hj⟩ - t
    have hij : i + t = ⟨j, hj⟩ := sub_add_cancel _ _
    have hc := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
    have he : a.testBit i.val = b.testBit (i+t).val := by
      simpa only [beq_iff_eq, Fin.val_add] using hc
    have hr := rotateMask_bit t i a
    rw [hij] at hr he
    exact hr.trans he
  · have hn : n ≤ j := by omega
    have hpow : 2^n ≤ 2^j := Nat.pow_le_pow_right (by decide) hn
    change (encode (rotateSet t (decode n a))).testBit j = b.testBit j
    rw [Nat.testBit_lt_two_pow ((encode_lt _).trans_le hpow),
      Nat.testBit_lt_two_pow (hb.trans_le hpow)]

theorem rotationBitsCheck_vertex {i r : Fin 3185} {t : Fin 28}
    (h : rotationBitsCheck 28 t.val (maskAt28 i.val) (maskAt28 r.val) = true) :
    rotateVertex t (indexedVertex maskAt28 masks28_valid_at i) =
      indexedVertex maskAt28 masks28_valid_at r := by
  apply Subtype.ext
  exact (decode_rotateMask t (maskAt28 i.val)).symm.trans
    (congrArg (decode 28) (rotationBitsCheck_sound
      (validMask_sound (masks28_valid_at r)).1 h))

def rotationChunkCheck (start count : ℕ) (ts rs : Array ℕ) : Bool :=
  (List.range count).all fun j =>
    decide (ts[j]! < 28) && decide (rs[j]! < 3185) &&
    (upperRoots28.any fun r => r.val == rs[j]!) &&
    rotationBitsCheck 28 ts[j]! (maskAt28 (start+j)) (maskAt28 rs[j]!)

theorem rotationChunk_sound {start count : ℕ} {ts rs : Array ℕ}
    (h : rotationChunkCheck start count ts rs = true) (i : Fin 3185)
    (hi : start ≤ i.val ∧ i.val < start+count) :
    ∃ t : Fin 28, ∃ r : Fin 3185, r ∈ upperRoots28 ∧
      rotateVertex t (indexedVertex maskAt28 masks28_valid_at i) =
        indexedVertex maskAt28 masks28_valid_at r := by
  have hj : i.val-start ∈ List.range count := List.mem_range.mpr (by omega)
  have hc := List.all_eq_true.mp h (i.val-start) hj
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨ht, _hr⟩, hroot⟩, hbits⟩ := hc
  obtain ⟨r, hroot, he⟩ := List.any_eq_true.mp hroot
  have he : r.val = rs[i.val-start]! := by simpa only [beq_iff_eq] using he
  refine ⟨⟨ts[i.val-start]!, ht⟩, r, hroot, ?_⟩
  apply rotationBitsCheck_vertex
  have heq : start + (i.val-start) = i.val := by omega
  simpa only [heq, he] using hbits
end Schrijver
