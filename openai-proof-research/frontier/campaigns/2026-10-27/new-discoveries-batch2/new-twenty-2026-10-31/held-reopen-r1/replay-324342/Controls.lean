import ConferenceMDS324342

/-! Non-vacuity control: under the same definitions, the Paley conference matrix of order 4
(p = 3) satisfies every clause of Conjecture 5. -/

namespace ConferenceMDS.Control
open ConferenceMDS Matrix

def P3 : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 1, 1, 1; -1, 0, 1, -1; -1, -1, 0, 1; -1, 1, -1, 0]

theorem P3_conference : IsConferenceMatrix P3 := by
  refine ⟨?_, by decide +kernel, by decide +kernel, ?_⟩
  · have h : ∀ q : Fin 4 × Fin 4, P3 q.1 q.2 = 0 ∨ P3 q.1 q.2 = 1 ∨ P3 q.1 q.2 = -1 := by
      decide +kernel
    exact fun i j => h (i, j)
  · have h : ∀ q : Fin 4 × Fin 4, (P3 * P3ᵀ) q.1 q.2 = if q.1 = q.2 then 3 else 0 := by
      decide +kernel
    ext i j
    have hij := h (i, j)
    simp only at hij
    rw [hij, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> norm_num

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

theorem weight_ge (x : Fin 4 → ZMod 3) (hx : x ∈ rowCode 3 P3) (h0 : x ≠ 0) :
    3 ≤ hammingNorm x := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 3)).1 hx
  have h : ∀ c : Fin 4 → ZMod 3, (∑ i, c i • rowVecs 3 P3 i) ≠ 0 →
      3 ≤ hammingNorm (∑ i, c i • rowVecs 3 P3 i) := by
    decide +kernel
  exact h c h0

theorem row0_mem : rowVecs 3 P3 0 ∈ rowCode 3 P3 := Submodule.subset_span ⟨0, rfl⟩

theorem minDistance_P3 : minDistance (rowCode 3 P3) = 3 := by
  apply le_antisymm
  · apply Nat.sInf_le
    refine ⟨_, row0_mem, 0, Submodule.zero_mem _, ?_, ?_⟩
    · intro h; have := congrFun h 1; revert this; decide +kernel
    · rw [hammingDist_zero_right]; decide +kernel
  · apply le_csInf
    · exact ⟨_, _, row0_mem, 0, Submodule.zero_mem _, by
        intro h; have := congrFun h 1; revert this; decide +kernel, rfl⟩
    · rintro d ⟨x, hx, y, hy, hxy, rfl⟩
      rw [hammingDist_eq_hammingNorm]
      exact weight_ge _ (Submodule.add_mem _ (Submodule.neg_mem _ hx) hy)
        (fun h => hxy (neg_add_eq_zero.1 h))

def bv (t : Fin 2) : Fin 4 → ZMod 3 := rowVecs 3 P3 (Fin.castLE (by norm_num) t)
def A2 : Matrix (Fin 2) (Fin 2) (ZMod 3) := fun t s => bv t (Fin.castLE (by norm_num) s)
def B2 : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![0, 2; 1, 0]

theorem A2_unit : IsUnit A2 := by
  have h1 : ∀ q : Fin 2 × Fin 2, (A2 * B2) q.1 q.2 = if q.1 = q.2 then 1 else 0 := by
    decide +kernel
  have h2 : ∀ q : Fin 2 × Fin 2, (B2 * A2) q.1 q.2 = if q.1 = q.2 then 1 else 0 := by
    decide +kernel
  refine ⟨⟨A2, B2, ?_, ?_⟩, rfl⟩
  · ext i j; rw [h1 (i, j), Matrix.one_apply]
  · ext i j; rw [h2 (i, j), Matrix.one_apply]

theorem bv_li : LinearIndependent (ZMod 3) bv :=
  LinearIndependent.of_comp (LinearMap.funLeft (ZMod 3) (ZMod 3) (Fin.castLE (by norm_num)))
    (Matrix.linearIndependent_rows_of_isUnit A2_unit)

theorem rows_in_span : ∀ r : Fin 4, rowVecs 3 P3 r ∈ Submodule.span (ZMod 3) (Set.range bv) := by
  intro r
  rw [Submodule.mem_span_range_iff_exists_fun]
  have h : ∀ r : Fin 4, ∃ c : Fin 2 → ZMod 3, ∑ t, c t • bv t = rowVecs 3 P3 r := by
    decide +kernel
  exact h r

theorem finrank_P3 : Module.finrank (ZMod 3) (rowCode 3 P3) = 2 := by
  have : rowCode 3 P3 = Submodule.span (ZMod 3) (Set.range bv) := by
    apply le_antisymm
    · rw [rowCode, Submodule.span_le]; rintro _ ⟨r, rfl⟩; exact rows_in_span r
    · rw [Submodule.span_le]; rintro _ ⟨t, rfl⟩
      exact Submodule.subset_span ⟨Fin.castLE (by norm_num) t, rfl⟩
  rw [this, finrank_span_eq_card bv_li]; simp

/-- Every clause of Conjecture 5 holds for the order-4 Paley matrix. -/
theorem paley3_satisfies :
    IsConferenceMatrix P3 ∧ IsMDS (rowCode 3 P3) ∧
      Module.finrank (ZMod 3) (rowCode 3 P3) = (3 + 1) / 2 ∧
      minDistance (rowCode 3 P3) = (3 + 3) / 2 := by
  refine ⟨P3_conference, ?_, finrank_P3, minDistance_P3⟩
  unfold IsMDS; rw [finrank_P3, minDistance_P3]

end ConferenceMDS.Control

#print axioms ConferenceMDS.Control.paley3_satisfies
