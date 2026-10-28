import Mathlib
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CA115
abbrev RawColumn := Fin 9 → Bool
def next (t : Fin 9) : Fin 9 := ⟨(t.val + 1) % 9, Nat.mod_lt _ (by decide)⟩
def prev (t : Fin 9) : Fin 9 := ⟨(t.val + 8) % 9, Nat.mod_lt _ (by decide)⟩
def rule (l m r : Bool) : Bool := !m || (l && !r)
def RawLegal (l m r : RawColumn) : Prop :=
  ∀ t, m (next t) = xor (m (prev t)) (rule (l t) (m t) (r t))
def Valid (m : RawColumn) : Prop :=
  ∀ t, m t = false → m (prev t) ≠ m (next t)
instance (l m r : RawColumn) : Decidable (RawLegal l m r) := inferInstanceAs (Decidable (∀ _t, _))
instance (m : RawColumn) : Decidable (Valid m) := inferInstanceAs (Decidable (∀ _t, _))
def codes : List ℕ := [73, 79, 103, 115, 121, 127, 146, 158, 206, 230, 242, 254, 292, 295, 307, 313, 316, 319, 403, 409, 412, 415, 457, 460, 463, 484, 487, 499, 505, 508, 511]
def bits (i : Fin 31) : RawColumn := fun t => (codes[i.val]!).testBit t.val
def bg : RawColumn := fun t => decide (t.val % 3 = 1)
def allOne : RawColumn := fun _ => true

theorem legal_valid (l m r : RawColumn) (h : RawLegal l m r) : Valid m := by
  intro t ht
  have he := h t
  simp [rule, ht] at he
  cases hp : m (prev t) <;> cases hn : m (next t) <;> simp_all


theorem valid_enumeration : ∀ m : RawColumn, Valid m → ∃ i : Fin 31, bits i = m := by
  decide +kernel

def forward : List (ℕ × ℕ) := [(79, 230),
  (121, 307),
  (146, 146),
  (146, 158),
  (146, 242),
  (146, 254),
  (146, 403),
  (146, 415),
  (146, 499),
  (146, 511),
  (158, 457),
  (158, 460),
  (158, 484),
  (242, 79),
  (242, 103),
  (242, 295),
  (254, 121),
  (254, 313),
  (254, 316),
  (295, 115),
  (316, 409),
  (403, 121),
  (403, 313),
  (403, 316),
  (415, 79),
  (415, 103),
  (415, 295),
  (457, 412),
  (484, 206),
  (499, 457),
  (499, 460),
  (499, 484),
  (511, 146),
  (511, 158),
  (511, 242),
  (511, 254),
  (511, 403),
  (511, 415),
  (511, 499),
  (511, 511)]
def backward : List (ℕ × ℕ) := [(73, 146),
  (73, 292),
  (79, 146),
  (103, 103),
  (103, 146),
  (103, 316),
  (103, 457),
  (103, 511),
  (115, 146),
  (115, 457),
  (121, 146),
  (127, 103),
  (127, 146),
  (146, 73),
  (146, 146),
  (146, 292),
  (146, 511),
  (158, 146),
  (206, 121),
  (206, 146),
  (230, 146),
  (230, 316),
  (242, 146),
  (254, 146),
  (292, 73),
  (292, 146),
  (295, 146),
  (307, 146),
  (307, 484),
  (313, 79),
  (313, 146),
  (313, 313),
  (313, 484),
  (313, 511),
  (316, 146),
  (319, 146),
  (319, 313),
  (403, 146),
  (409, 79),
  (409, 146),
  (412, 146),
  (412, 295),
  (415, 146),
  (457, 146),
  (460, 121),
  (460, 146),
  (460, 295),
  (460, 460),
  (460, 511),
  (463, 146),
  (463, 460),
  (484, 146),
  (487, 103),
  (487, 146),
  (499, 146),
  (505, 146),
  (505, 313),
  (508, 146),
  (508, 460),
  (511, 103),
  (511, 146),
  (511, 313),
  (511, 460)]
def code (i : Fin 31) : ℕ := codes[i.val]!
def FW (l m : Fin 31) : Prop := (code l, code m) ∈ forward
def BW (l m : Fin 31) : Prop := (code l, code m) ∈ backward
instance (l m : Fin 31) : Decidable (FW l m) := inferInstanceAs (Decidable (_ ∈ _))
instance (l m : Fin 31) : Decidable (BW l m) := inferInstanceAs (Decidable (_ ∈ _))

theorem forward_closed : ∀ l m r : Fin 31,
    FW l m → RawLegal (bits l) (bits m) (bits r) → FW m r := by
  decide +kernel

theorem backward_closed : ∀ l m r : Fin 31,
    BW m r → RawLegal (bits l) (bits m) (bits r) → BW l m := by
  decide +kernel

theorem background_code : bits ⟨6, by decide⟩ = bg := by decide +kernel

theorem forward_root : FW ⟨6, by decide⟩ ⟨6, by decide⟩ := by decide +kernel

theorem backward_root : BW ⟨6, by decide⟩ ⟨6, by decide⟩ := by decide +kernel

theorem core_columns : ∀ l m : Fin 31, FW l m → BW l m →
    (bits m = bg ∨ bits m = allOne) := by decide +kernel

end CA115
