import IndexedCertificates
set_option autoImplicit false
namespace Schrijver

theorem decode_disjoint {n a b : ℕ} (ha : a < 2^n) (_hb : b < 2^n) :
    Disjoint (decode n a) (decode n b) ↔ a &&& b = 0 := by
  constructor
  · intro hd
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hi : i < n
    · have hh : ¬ ((⟨i, hi⟩ : Fin n) ∈ decode n a ∧ (⟨i, hi⟩ : Fin n) ∈ decode n b) := by
        rintro ⟨h1, h2⟩
        exact Finset.disjoint_left.mp hd h1 h2
      have hn : ¬ (a.testBit i = true ∧ b.testBit i = true) := by
        rintro ⟨h1, h2⟩
        exact hh ⟨by simp [decode, h1], by simp [decode, h2]⟩
      cases h1 : a.testBit i <;> cases h2 : b.testBit i <;> simp_all
    · have hp : 2^n ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow (ha.trans_le hp)]
      rfl
  · intro he
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have h1 : a.testBit i.val = true := by simpa [decode] using hi
    have h2 : b.testBit i.val = true := by simpa [decode] using hj
    have hh := congrArg (fun m => m.testBit i.val) he
    simp [Nat.testBit_and, h1, h2] at hh

noncomputable def indexedVertex {n k N : ℕ} (masks : ℕ → ℕ)
    (hv : ∀ i : Fin N, validMask n k (masks i.val) = true) (i : Fin N) : Vertex n k :=
  ⟨decode n (masks i.val), (validMask_sound (hv i)).2⟩

theorem indexedVertex_injective {n k N : ℕ} (masks : ℕ → ℕ)
    (hv : ∀ i : Fin N, validMask n k (masks i.val) = true)
    (hi : Function.Injective (fun i : Fin N => masks i.val)) :
    Function.Injective (indexedVertex masks hv) := by
  intro a b he
  apply hi
  exact decode_injective (validMask_sound (hv a)).1 (validMask_sound (hv b)).1
    (congrArg Subtype.val he)

theorem indexedVertex_surjective {n k N : ℕ} (masks : ℕ → ℕ)
    (hv : ∀ i : Fin N, validMask n k (masks i.val) = true)
    (hc : ∀ v : Vertex n k, ∃ i : Fin N, masks i.val = encode v.val) :
    Function.Surjective (indexedVertex masks hv) := by
  intro v
  obtain ⟨i, hi⟩ := hc v
  refine ⟨i, Subtype.ext ?_⟩
  change decode n (masks i.val) = v.val
  rw [hi, decode_encode]

noncomputable def indexedLiteralIso {n k N : ℕ} (masks : ℕ → ℕ)
    (hv : ∀ i : Fin N, validMask n k (masks i.val) = true)
    (hi : Function.Injective (fun i : Fin N => masks i.val))
    (hc : ∀ v : Vertex n k, ∃ i : Fin N, masks i.val = encode v.val) :
    indexedGraph N masks ≃g SG n k where
  toEquiv := Equiv.ofBijective (indexedVertex masks hv)
    ⟨indexedVertex_injective masks hv hi, indexedVertex_surjective masks hv hc⟩
  map_rel_iff' := by
    intro a b
    change (indexedVertex masks hv a ≠ indexedVertex masks hv b ∧
      Disjoint (decode n (masks a.val)) (decode n (masks b.val))) ↔
      (a ≠ b ∧ masks a.val &&& masks b.val = 0)
    exact and_congr (indexedVertex_injective masks hv hi).ne_iff
      (decode_disjoint (validMask_sound (hv a)).1 (validMask_sound (hv b)).1)

end Schrijver
