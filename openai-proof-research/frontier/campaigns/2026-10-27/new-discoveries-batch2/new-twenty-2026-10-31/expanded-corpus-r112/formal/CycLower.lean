import CycRot

/-!
# Lower bound (arXiv:2604.16188, Theorem 4.5 construction, specialised to `S_a` vs `P_b^{mon}`)

For `m ≤ (a-1)(b-2)` colour the edge `{u,v}` of `K_m` with colour `1` (code `0`) iff
`⌊u/(a-1)⌋ = ⌊v/(a-1)⌋`.  It contains no colour-1 cyclic `S_a` and no colour-2 cyclic `P_b^{mon}`.
-/

namespace CycRamsey

/-- The block colouring with blocks of size `s`. -/
def blockCol (m s : ℕ) : Colouring m :=
  Sym2.lift ⟨fun u v => if u.val / s = v.val / s then 0 else 1, by
    intro u v
    dsimp only
    by_cases h : u.val / s = v.val / s
    · rw [ite_t h, ite_t h.symm]
    · rw [ite_f h, ite_f (Ne.symm h)]⟩

theorem blockCol_apply (m s : ℕ) (u v : Fin m) :
    blockCol m s s(u, v) = if u.val / s = v.val / s then 0 else 1 := by
  simp [blockCol]

theorem startStar_adj_zero {a : ℕ} (ha : 0 < a) (j : Fin a) (hj : j.val ≠ 0) :
    (startStar a).Adj ⟨0, ha⟩ j := by
  rw [startStar, SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl ⟨rfl, hj⟩⟩
  intro h; apply hj; rw [← h]

theorem no_red_star (a m : ℕ) (ha : 3 ≤ a) : ¬ ContainsCyc (startStar a) (blockCol m (a - 1)) 0 := by
  rintro ⟨φ, ⟨hinj, -⟩, hcol⟩
  have ha0 : 0 < a := by omega
  have hs : 0 < a - 1 := by omega
  have hblock : ∀ j : Fin a, (φ j).val / (a - 1) = (φ ⟨0, ha0⟩).val / (a - 1) := by
    intro j
    by_cases hj : j.val = 0
    · have : j = ⟨0, ha0⟩ := Fin.ext hj
      rw [this]
    · have h := hcol _ _ (startStar_adj_zero ha0 j hj)
      rw [blockCol_apply] at h
      by_contra hne
      rw [ite_f (Ne.symm hne)] at h
      exact absurd h (by decide)
  let g : Fin a → Fin (a - 1) := fun j => ⟨(φ j).val % (a - 1), Nat.mod_lt _ hs⟩
  have hg : Function.Injective g := by
    intro j1 j2 h
    have h' : (φ j1).val % (a - 1) = (φ j2).val % (a - 1) := congrArg Fin.val h
    apply hinj
    apply Fin.ext
    rw [← Nat.div_add_mod (φ j1).val (a - 1), ← Nat.div_add_mod (φ j2).val (a - 1), hblock j1,
      hblock j2, h']
  have := Fintype.card_le_of_injective g hg
  simp at this
  omega

theorem monPath_adj_succ {b : ℕ} (u v : Fin b) (h : u.val + 1 = v.val) : (monPath b).Adj u v := by
  rw [monPath, SimpleGraph.fromRel_adj]
  refine ⟨?_, Or.inl h⟩
  intro e; rw [e] at h; omega

theorem no_blue_path (a b m : ℕ) (ha : 3 ≤ a) (hb : 4 ≤ b) (hm : m ≤ (a - 1) * (b - 2)) :
    ¬ ContainsCyc (monPath b) (blockCol m (a - 1)) 1 := by
  classical
  rintro ⟨φ, ⟨-, t, hmono⟩, hcol⟩
  have hs : 0 < a - 1 := by omega
  have hb0 : 0 < b := by omega
  -- block index along the rotated sequence
  let f : ℕ → ℕ := fun j => if h : j < b then (φ (t + ⟨j, h⟩)).val / (a - 1) else 0
  have hf : ∀ (j : ℕ) (h : j < b), f j = (φ (t + ⟨j, h⟩)).val / (a - 1) := by
    intro j h; simp [f, h]
  have hfle : ∀ j, j < b → f j ≤ b - 3 := by
    intro j h
    rw [hf j h]
    have hv := (φ (t + ⟨j, h⟩)).isLt
    have : (φ (t + ⟨j, h⟩)).val / (a - 1) < b - 2 := by
      rw [Nat.div_lt_iff_lt_mul hs]
      calc (φ (t + ⟨j, h⟩)).val < m := hv
        _ ≤ (a - 1) * (b - 2) := hm
        _ = (b - 2) * (a - 1) := Nat.mul_comm _ _
    omega
  have hstep_le : ∀ j, j + 1 < b → f j ≤ f (j + 1) := by
    intro j h
    rw [hf j (by omega), hf (j + 1) h]
    apply Nat.div_le_div_right
    have : (⟨j, by omega⟩ : Fin b) < ⟨j + 1, h⟩ := by
      show j < j + 1; omega
    exact le_of_lt (hmono this)
  let bad : ℕ → Prop := fun j => (t.val + j) % b = b - 1
  have hstep_lt : ∀ j, j + 1 < b → ¬ bad j → f j < f (j + 1) := by
    intro j h hbad
    have hlt : f j ≤ f (j + 1) := hstep_le j h
    have hr : (t.val + j) % b + 1 < b := by
      have := Nat.mod_lt (t.val + j) hb0
      simp only [bad] at hbad
      omega
    have hidx : (t + (⟨j, by omega⟩ : Fin b)).val + 1 = (t + (⟨j + 1, h⟩ : Fin b)).val := by
      rw [Fin.val_add, Fin.val_add]
      simp only
      rw [← Nat.add_assoc, Nat.add_mod (t.val + j) 1 b, Nat.mod_eq_of_lt (a := 1) (by omega)]
      rw [Nat.mod_eq_of_lt hr]
    have hadj := monPath_adj_succ _ _ hidx
    have hc := hcol _ _ hadj
    rw [blockCol_apply] at hc
    have hne : (φ (t + ⟨j, by omega⟩)).val / (a - 1) ≠ (φ (t + ⟨j + 1, h⟩)).val / (a - 1) := by
      intro e; rw [ite_t e] at hc; exact absurd hc (by decide)
    rw [hf j (by omega), hf (j + 1) h] at hlt ⊢
    exact lt_of_le_of_ne hlt hne
  have huniq : ∀ i j, i < j → j < b → bad i → ¬ bad j := by
    intro i j hij hj hi hjb
    simp only [bad] at hi hjb
    have ht := t.isLt
    -- (t + j) = (t + i) + (j - i) with 0 < j - i < b, so the residues differ
    have key : (t.val + j) % b = ((t.val + i) % b + (j - i)) % b := by
      rw [Nat.mod_add_mod]; congr 1; omega
    rw [hi, hjb] at key
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at key
    omega
  have claim : ∀ j, j < b →
      f 0 + j ≤ f j + (if ∃ i, i < j ∧ bad i then 1 else 0) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have ih := ih (by omega)
      by_cases hbj : bad j
      · have hnone : ¬ ∃ i, i < j ∧ bad i := by
          rintro ⟨i, hi, hbi⟩; exact huniq i j hi (by omega) hbi hbj
        have hsome : ∃ i, i < j + 1 ∧ bad i := ⟨j, by omega, hbj⟩
        rw [ite_f hnone] at ih
        rw [ite_t hsome]
        have := hstep_le j hj
        omega
      · have hiff : (∃ i, i < j + 1 ∧ bad i) ↔ (∃ i, i < j ∧ bad i) := by
          constructor
          · rintro ⟨i, hi, hbi⟩
            refine ⟨i, ?_, hbi⟩
            rcases Nat.lt_or_ge i j with h | h
            · exact h
            · exfalso; have : i = j := by omega
              exact hbj (this ▸ hbi)
          · rintro ⟨i, hi, hbi⟩; exact ⟨i, by omega, hbi⟩
        have := hstep_lt j hj hbj
        by_cases hex : ∃ i, i < j ∧ bad i
        · rw [ite_t hex] at ih; rw [ite_t (hiff.mpr hex)]; omega
        · rw [ite_f hex] at ih; rw [ite_f (fun h => hex (hiff.mp h))]; omega
  have hc := claim (b - 1) (by omega)
  have hl := hfle (b - 1) (by omega)
  split_ifs at hc <;> omega

end CycRamsey
