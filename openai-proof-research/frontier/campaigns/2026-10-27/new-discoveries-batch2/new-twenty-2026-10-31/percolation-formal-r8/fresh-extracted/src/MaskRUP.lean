import Std
namespace Percolation.MaskRUP
set_option autoImplicit false
abbrev Mask := Nat × Nat
def bits (m : Mask) (b : Bool) : Nat := if b then m.2 else m.1
def insert (m : Mask) (n : Nat) (b : Bool) : Mask :=
  if b then (m.1, m.2 ||| (1 <<< n)) else (m.1 ||| (1 <<< n), m.2)
def cover (c f : Mask) : Bool :=
  (c.1 &&& f.1 == c.1) && (c.2 &&& f.2 == c.2)
def Holds (v : Nat → Bool) (c : Mask) : Prop :=
  ∃ n b, (bits c b).testBit n = true ∧ v n ≠ b
def FalseUnder (v : Nat → Bool) (f : Mask) : Prop :=
  ∀ n b, (bits f b).testBit n = true → v n = b
abbrev Hint := Mask × Option (Nat × Bool)
noncomputable def check (f : Mask) (hs : List Hint) : Bool :=
  List.rec (motive := fun _ => Mask → Bool) (fun _ => false)
    (fun h _ prev fs =>
      match h.2 with
      | none => cover h.1 fs
      | some (n,b) => cover h.1 (insert fs n b) && prev (insert fs n (!b))) hs f

theorem bit_insert (f : Mask) (n k : Nat) (b d : Bool) :
    (bits (insert f n b) d).testBit k =
      ((bits f d).testBit k || (decide (n = k) && decide (b = d))) := by
  cases b <;> cases d <;> simp [bits, insert, Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem cover_bit (c f : Mask) (h : cover c f = true) (n : Nat) (b : Bool)
    (hc : (bits c b).testBit n = true) : (bits f b).testBit n = true := by
  have hh : c.1 &&& f.1 = c.1 ∧ c.2 &&& f.2 = c.2 := by simpa [cover] using h
  have he : bits c b &&& bits f b = bits c b := by
    cases b <;> simp_all [bits]
  have ht := congrArg (fun m : Nat => m.testBit n) he
  simpa [hc] using ht

theorem conflict (v : Nat → Bool) (c f : Mask) (hf : FalseUnder v f)
    (hc : Holds v c) (he : cover c f = true) : False := by
  obtain ⟨n,b,h,hv⟩ := hc
  exact hv (hf n b (cover_bit c f he n b h))

theorem force (v : Nat → Bool) (c f : Mask) (n : Nat) (b : Bool)
    (hf : FalseUnder v f) (hc : Holds v c)
    (he : cover c (insert f n b) = true) : v n = !b := by
  obtain ⟨k,d,h,hv⟩ := hc
  have ht := cover_bit c (insert f n b) he k d h
  rw [bit_insert] at ht
  have ht : (bits f d).testBit k = true ∨ (decide (n = k) && decide (b = d)) = true := by simpa using ht
  rcases ht with ht | ht
  · exact False.elim (hv (hf k d ht))
  · have hd : n = k ∧ b = d := by simpa using ht
    obtain ⟨rfl,rfl⟩ := hd
    cases hvn : v n <;> cases b <;> simp_all

theorem insert_false (v : Nat → Bool) (f : Mask) (n : Nat) (b : Bool)
    (hf : FalseUnder v f) (hv : v n = b) : FalseUnder v (insert f n b) := by
  intro k d h
  rw [bit_insert] at h
  have h : (bits f d).testBit k = true ∨ (decide (n = k) && decide (b = d)) = true := by simpa using h
  rcases h with h | h
  · exact hf k d h
  · have hd : n = k ∧ b = d := by simpa using h
    obtain ⟨rfl,rfl⟩ := hd
    exact hv

theorem check_sound_aux (v : Nat → Bool) (hs : List Hint) :
    ∀ f, FalseUnder v f → (∀ h ∈ hs, Holds v h.1) → check f hs = true → False := by
  induction hs with
  | nil => intro f hf hh he; simp [check] at he
  | cons h hs ih =>
    intro f hf hh he
    have hc := hh h (by simp)
    cases hu : h.2 with
    | none => exact conflict v h.1 f hf hc (by simpa [check, hu] using he)
    | some z =>
      have hhcheck : cover h.1 (insert f z.1 z.2) = true ∧
          check (insert f z.1 (!z.2)) hs = true := by simpa [check, hu] using he
      apply ih (insert f z.1 (!z.2))
      · exact insert_false v f z.1 (!z.2) hf (force v h.1 f z.1 z.2 hf hc hhcheck.1)
      · intro d hd; exact hh d (by simp [hd])
      · exact hhcheck.2

theorem check_sound (c : Mask) (hs : List Hint) (he : check c hs = true)
    (v : Nat → Bool) (hh : ∀ h ∈ hs, Holds v h.1) : Holds v c := by
  apply Classical.byContradiction
  intro hn
  apply check_sound_aux v hs c ?_ hh he
  intro n b hb
  apply Classical.byContradiction
  intro hv
  exact hn ⟨n,b,hb,hv⟩

noncomputable def encode (c : List (Nat × Bool)) : Mask :=
  List.foldr (fun z m => insert m z.1 z.2) (0,0) c

theorem encode_bit (c : List (Nat × Bool)) (n : Nat) (b : Bool) :
    (bits (encode c) b).testBit n = true ↔ (n,b) ∈ c := by
  induction c with
  | nil => simp [encode, bits]
  | cons z zs ih =>
    change (bits (insert (encode zs) z.1 z.2) b).testBit n = true ↔ (n,b) ∈ z :: zs
    rw [bit_insert]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨h1,h2⟩)
      · exact Or.inr h
      · exact Or.inl (Prod.ext h1.symm h2.symm)
    · rintro (h | h)
      · cases h; exact Or.inr ⟨rfl,rfl⟩
      · exact Or.inl h

theorem encode_holds (v : Nat → Bool) (c : List (Nat × Bool)) :
    Holds v (encode c) ↔ ∃ z ∈ c, v z.1 ≠ z.2 := by
  constructor
  · rintro ⟨n,b,h,hv⟩; exact ⟨(n,b),(encode_bit c n b).mp h,hv⟩
  · rintro ⟨⟨n,b⟩,h,hv⟩; exact ⟨n,b,(encode_bit c n b).mpr h,hv⟩
#print axioms check_sound
end Percolation.MaskRUP
