import Checkers
import Mathlib.Data.Nat.Bitwise
namespace Schrijver

def encodeList : List ℕ → ℕ
  | [] => 0
  | a :: l => 2^a ||| encodeList l

noncomputable def encode {n : ℕ} (s : Finset (Fin n)) : ℕ :=
  encodeList (s.toList.map Fin.val)

theorem encodeList_bit (l : List ℕ) (i : ℕ) :
    (encodeList l).testBit i = decide (i ∈ l) := by
  induction l with
  | nil => simp [encodeList]
  | cons a l ih => simp [encodeList, Nat.testBit_or, Nat.testBit_two_pow, ih, eq_comm]

theorem encodeList_lt {n : ℕ} (l : List ℕ) (h : ∀ a ∈ l, a < n) :
    encodeList l < 2^n := by
  induction l with
  | nil => simp [encodeList]
  | cons a l ih =>
    apply Nat.or_lt_two_pow
    · exact Nat.pow_lt_pow_right (by decide) (h a (by simp))
    · exact ih (fun a ha => h a (by simp [ha]))

theorem encode_lt {n : ℕ} (s : Finset (Fin n)) : encode s < 2^n := by
  apply encodeList_lt
  intro a ha
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
  exact i.isLt

theorem encode_bit {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    (encode s).testBit i.val = decide (i ∈ s) := by
  rw [encode, encodeList_bit]
  congr 1
  apply propext
  simp only [List.mem_map, Finset.mem_toList]
  constructor
  · rintro ⟨j, hj, he⟩
    have : j = i := Fin.ext he
    simpa [this] using hj
  · intro hi; exact ⟨i, hi, rfl⟩

theorem decode_encode {n : ℕ} (s : Finset (Fin n)) : decode n (encode s) = s := by
  ext i
  simp [decode, encode_bit]

theorem decode_injective {n a b : ℕ} (ha : a < 2^n) (hb : b < 2^n)
    (h : decode n a = decode n b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · have hh := congrArg (fun s => (⟨i, hi⟩ : Fin n) ∈ s) h
    simpa [decode] using hh
  · have hn : n ≤ i := by omega
    have hp : 2^n ≤ 2^i := Nat.pow_le_pow_right (by decide) hn
    rw [Nat.testBit_lt_two_pow (ha.trans_le hp), Nat.testBit_lt_two_pow (hb.trans_le hp)]

theorem encode_decode {n m : ℕ} (hm : m < 2^n) : encode (decode n m) = m :=
  decode_injective (encode_lt _) hm (decode_encode _)

theorem validMask_complete {n k m : ℕ} (hm : m < 2^n)
    (hc : (decode n m).card = k) (hs : Stable n (decode n m)) :
    validMask n k m = true := by
  simp only [validMask, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨hm, hc⟩, ?_⟩
  intro i _
  by_cases hi : m.testBit i.val = true
  · have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
    have hj : ¬ m.testBit ((i.val+1)%n) = true := by
      intro hj
      exact hs i (by simp [decode, hi]) ⟨(i.val+1)%n, Nat.mod_lt _ hn⟩
        (by simp [decode, hj]) rfl
    simp [hi, hj]
  · simp [hi]

theorem encode_vertex_valid {n k : ℕ} (v : Vertex n k) :
    validMask n k (encode v.val) = true := by
  apply validMask_complete (encode_lt _)
  · simpa [decode_encode] using v.property.1
  · simpa [decode_encode] using v.property.2

-- A genuine bijection, without relying on a cardinality comparison.
noncomputable def maskVertexEquiv (n k : ℕ) :
    {m : ℕ // validMask n k m = true} ≃ Vertex n k where
  toFun m := ⟨decode n m.val, (validMask_sound m.property).2⟩
  invFun v := ⟨encode v.val, encode_vertex_valid v⟩
  left_inv m := Subtype.ext (encode_decode (validMask_sound m.property).1)
  right_inv v := Subtype.ext (decode_encode v.val)

end Schrijver
