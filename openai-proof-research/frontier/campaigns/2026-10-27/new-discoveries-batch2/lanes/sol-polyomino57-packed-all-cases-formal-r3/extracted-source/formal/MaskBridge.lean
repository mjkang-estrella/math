import PackedBits
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Polyomino57.Diagonal.FiniteProof.Packed
 def encode (k : ℕ) (A : Finset ℕ) : ℕ :=
  Nat.rec 0 (fun j r => r ||| (if j ∈ A then 2^j else 0)) k
 theorem encode_bit (k : ℕ) (A : Finset ℕ) (i : ℕ) :
    (encode k A).testBit i = decide (i < k ∧ i ∈ A) := by
  induction k with
  | zero => simp [encode]
  | succ k ih =>
    change (encode k A ||| (if k ∈ A then 2^k else 0)).testBit i = _
    rw [Nat.testBit_or, ih]
    by_cases ha : k ∈ A <;> by_cases hi : k = i <;>
      simp_all [Nat.testBit_two_pow]
    all_goals
      have hii : (i < k) ↔ (i < k+1) := by omega
      simp only [hii]
 theorem encode_lt (k : ℕ) (A : Finset ℕ) : encode k A < 2^k := by
  induction k with
  | zero => simp [encode]
  | succ k ih =>
    change encode k A ||| (if k ∈ A then 2^k else 0) < 2^(k+1)
    apply Nat.or_lt_two_pow
    · have : 2^k < 2^(k+1) := by omega
      omega
    · split <;> simp_all [pow_succ] <;> omega
 def decode (k m : ℕ) : Finset ℕ := (Finset.range k).filter (fun i => m.testBit i)
 theorem decode_encode (k : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.range k) :
    decode k (encode k A) = A := by
  ext i
  simp only [decode, Finset.mem_filter, Finset.mem_range, encode_bit, decide_eq_true_eq]
  constructor
  · tauto
  · intro h; exact ⟨Finset.mem_range.mp (hA h), Finset.mem_range.mp (hA h), h⟩
 theorem encode_decode (k m : ℕ) (hm : m < 2^k) : encode k (decode k m) = m := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [encode_bit]
  by_cases hi : i < k
  · simp [decode, hi]
  · have hp : 2^k ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    have hb : m.testBit i = false := Nat.testBit_lt_two_pow (by omega)
    simp [hi, hb]
 theorem encode_union (k : ℕ) (A B : Finset ℕ) :
    encode k (A ∪ B) = encode k A ||| encode k B := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [encode_bit, Nat.testBit_or, Finset.mem_union]
  by_cases h : i < k <;> by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;> simp [h,ha,hb]
 theorem encode_and (k : ℕ) (A B : Finset ℕ) :
    encode k (A ∩ B) = encode k A &&& encode k B := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [encode_bit, Nat.testBit_and, Finset.mem_inter]
  by_cases h : i < k <;> by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;> simp [h,ha,hb]
 theorem encode_empty (k : ℕ) : encode k ∅ = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i; simp [encode_bit]
 theorem encode_nonzero {k : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.range k)
    (hne : A.Nonempty) : encode k A ≠ 0 := by
  intro h
  obtain ⟨i,hi⟩ := hne
  have := encode_bit k A i
  rw [h] at this
  have hit := Finset.mem_range.mp (hA hi)
  simp [hit,hi] at this
 theorem encode_disjoint {k : ℕ} {A B : Finset ℕ} (hd : Disjoint A B) :
    encode k A &&& encode k B = 0 := by
  rw [← encode_and, Finset.disjoint_iff_inter_eq_empty.mp hd, encode_empty]
 theorem encode_complement {k : ℕ} {A B : Finset ℕ} (hd : Disjoint A B) :
    encode k (A ∪ B) ^^^ encode k A = encode k B := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [encode_bit, Nat.testBit_xor, Finset.mem_union]
  have h := Finset.disjoint_left.mp hd
  by_cases ht : i < k <;> by_cases ha : i ∈ A <;> by_cases hb : i ∈ B <;> simp_all
 def rowOf (k : ℕ) (table : ℕ → ℕ) (A : Finset ℕ) : ℕ := table (encode k A)
 theorem rowOf_decode (k m : ℕ) (table : ℕ → ℕ) (hm : m < 2^k) :
    rowOf k table (decode k m) = table m := by rw [rowOf, encode_decode k m hm]
 def submasks (k u : ℕ) : List ℕ :=
  Nat.rec [0] (fun j r => if u.testBit j then r ++ r.map (fun a => a ||| 2^j) else r) k
 theorem encode_mem_submasks (k u : ℕ) (A : Finset ℕ)
    (h : ∀ i < k, i ∈ A → u.testBit i = true) : encode k A ∈ submasks k u := by
  induction k with
  | zero => simp [encode, submasks]
  | succ k ih =>
    have hi := ih (fun i hi ha => h i (by omega) ha)
    change encode k A ||| (if k ∈ A then 2^k else 0) ∈
      (if u.testBit k then submasks k u ++ (submasks k u).map (fun a => a ||| 2^k)
       else submasks k u)
    by_cases ha : k ∈ A
    · rw [ite_eq_left ha, h k (by omega) ha]
      exact List.mem_append_right _ (List.mem_map.mpr ⟨encode k A, hi, rfl⟩)
    · simp only [ite_eq_right ha, Nat.or_zero]
      split
      · exact List.mem_append_left _ hi
      · exact hi
 def unionCheck (k n : ℕ) (table : ℕ → ℕ) (u : ℕ) : Bool :=
  (submasks k u).all (fun a => if a = 0 ∨ a = u then true
    else bitCheck n (table a) (table (u ^^^ a)) (table u))
 theorem unionCheck_sound {k n : ℕ} {table : ℕ → ℕ}
    (checked : ∀ u < 2^k, unionCheck k n table u = true)
    (A B : Finset ℕ) (hA : A ⊆ Finset.range k) (hB : B ⊆ Finset.range k)
    (hneA : A.Nonempty) (hneB : B.Nonempty) (hd : Disjoint A B) :
    bitCheck n (rowOf k table A) (rowOf k table B) (rowOf k table (A ∪ B)) = true := by
  have hu := checked (encode k (A ∪ B)) (encode_lt _ _)
  have ham : encode k A ∈ submasks k (encode k (A ∪ B)) := by
    apply encode_mem_submasks
    intro i hi ha
    simp [encode_bit, hi, ha]
  have hx := encode_complement (k := k) hd
  have han := encode_nonzero hA hneA
  have hab : encode k A ≠ encode k (A ∪ B) := by
    intro he
    rw [← he, Nat.xor_self] at hx
    exact encode_nonzero hB hneB hx.symm
  simp only [unionCheck, List.all_eq_true] at hu
  have hp := hu _ ham
  simp only [han, hab, or_self, ite_false] at hp
  rw [hx] at hp
  exact hp
 theorem row_bounds {k n : ℕ} {table : ℕ → ℕ}
    (h : ∀ m < 2^k, boundCheck n (table m) = true) (A : Finset ℕ) :
    bounded n (rowOf k table A) := boundCheck_sound (h _ (encode_lt _ _))
theorem all_split {α : Type*} (l : List α) (p : α → Bool) (n : ℕ)
    (ht : (l.take n).all p = true) (hd : (l.drop n).all p = true) : l.all p = true := by
  have he := List.take_append_drop n l
  have h : ((l.take n) ++ l.drop n).all p = true := by
    rw [List.all_append, ht, hd]; rfl
  rw [he] at h
  exact h
end Polyomino57.Diagonal.FiniteProof.Packed
