
/-- Edge `i` of the counterexample clutter. -/
def X' (i : Nat) : Finset (Fin 11) := XL.getD i ∅

/-- Blocker member `j` (for `j < 36`). -/
def Y' (j : Nat) : Finset (Fin 11) := YL.getD j ∅

/-- The counterexample clutter on ground set `Fin 11`. -/
def C11 : Finset (Finset (Fin 11)) := (Finset.range 11).image X'

theorem mem_C11 {X : Finset (Fin 11)} : X ∈ C11 ↔ ∃ i < 11, X' i = X := by
  simp [C11]

theorem C11_clutter : IsClutter C11 := by
  have h : ∀ i < 11, ∀ j < 11, X' i ⊆ X' j → X' i = X' j := by decide +kernel
  intro X hX Y hY hXY
  obtain ⟨i, hi, rfl⟩ := mem_C11.1 hX
  obtain ⟨j, hj, rfl⟩ := mem_C11.1 hY
  exact h i hi j hj hXY

theorem transversal_Y : ∀ j < 36, ∀ i < 11, (X' i ∩ Y' j).Nonempty := by decide +kernel

theorem minimal_Y : ∀ j < 36, ∀ v ∈ Y' j, ∃ i < 11, Disjoint (X' i) ((Y' j).erase v) := by
  decide +kernel

theorem Y_mem_blocker {j : Nat} (hj : j < 36) : Y' j ∈ blocker C11 := by
  refine ⟨fun X hX => ?_, fun T hT htr => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := mem_C11.1 hX
    exact transversal_Y j hj i hi
  · obtain ⟨v, hvY, hvT⟩ := Finset.exists_of_ssubset hT
    obtain ⟨i, hi, hdisj⟩ := minimal_Y j hj v hvY
    have hsub : T ⊆ (Y' j).erase v := fun x hx =>
      Finset.mem_erase.2 ⟨fun h => hvT (h ▸ hx), hT.subset hx⟩
    obtain ⟨x, hx⟩ := htr (X' i) (mem_C11.2 ⟨i, hi, rfl⟩)
    rw [Finset.mem_inter] at hx
    exact Finset.disjoint_left.1 hdisj hx.1 (hsub hx.2)

theorem fact_dom : ∀ i < 11, ∀ x ∈ X' i, x.val ∈ DL.getD i [] := by decide +kernel

theorem fact_cover : ∀ j < 36, ∀ y ∈ Y' j, ∃ e ∈ KL.getD j [], e.1 = y.val := by decide +kernel

theorem fact_single :
    ∀ j < 36, ∀ e ∈ KL.getD j [], ∀ i ∈ e.2, i < 11 ∧ (X' i ∩ Y' j).card ≤ 1 := by
  decide +kernel

theorem DL_len : DL.length = 11 := rfl

theorem KL_len : KL.length = 36 := rfl

/-- The kernel evaluates the certificate tree. -/
theorem cert_ok : chk DL KL cert [] = true := by decide +kernel

/-- No Király functions exist for `C11`. -/
theorem not_kiraly : ¬ KiralyProperty C11 := by
  rintro ⟨p, q, hp, hq, hpq⟩
  let Xc : (i : Nat) → i < 11 → C11 := fun i hi => ⟨X' i, mem_C11.2 ⟨i, hi, rfl⟩⟩
  let b : Nat → Nat := fun i => if hi : i < 11 then (p (Xc i hi)).val else 0
  have hdom : ∀ i, DL.getD i [] ≠ [] → b i ∈ DL.getD i [] := by
    intro i hne
    by_cases hi : i < 11
    · simp only [b, hi, dite_true]
      exact fact_dom i hi _ (hp (Xc i hi))
    · exact absurd (List.getD_eq_default _ _ (by rw [DL_len]; omega)) hne
  obtain ⟨j, hj, hdead⟩ := chk_sound DL KL cert [] cert_ok b (by simp) hdom
  rw [KL_len] at hj
  let Yc : blocker C11 := ⟨Y' j, Y_mem_blocker hj⟩
  obtain ⟨e, he, he1⟩ := fact_cover j hj _ (hq Yc)
  obtain ⟨i, hi, hbi⟩ := hdead e he
  obtain ⟨hi11, hcard⟩ := fact_single j hj e he i hi
  have hbval : b i = (p (Xc i hi11)).val := by simp only [b, hi11, dite_true]
  have hpq' : p (Xc i hi11) = q Yc := by
    apply Fin.ext
    rw [← hbval, hbi, he1]
  have h1 := hpq (Xc i hi11) Yc hpq'
  have h2 : (Xc i hi11).1 ∩ Yc.1 = X' i ∩ Y' j := rfl
  rw [h2] at h1
  omega

/-! ## Nonideality: `(1/3, …, 1/3)` is a fractional vertex of `P(C11)` -/

/-- The point `x* = (1/3, …, 1/3)`. -/
noncomputable def xstar : Fin 11 → ℝ := fun _ => 1 / 3

theorem card_X : ∀ i < 11, (X' i).card = 3 := by decide +kernel

theorem tight {a b s t : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hs : 1 ≤ s)
    (ht : 1 ≤ t) (h : a * s + b * t = 1) : s = 1 := by
  nlinarith [mul_le_mul_of_nonneg_left ht hb.le]

theorem xstar_mem : xstar ∈ coveringPolyhedron C11 := by
  refine ⟨fun _ => by norm_num [xstar], fun X hX => ?_⟩
  obtain ⟨i, hi, rfl⟩ := mem_C11.1 hX
  simp only [xstar, Finset.sum_const, card_X i hi, nsmul_eq_mul]
  norm_num

/-- The edge incidence system `x(X) = 1` (all eleven edges) has the unique solution `x*`. -/
theorem eq_xstar {y : Fin 11 → ℝ} (hy : ∀ i < 11, ∑ v ∈ X' i, y v = 1) : y = xstar := by
@@EDGE_EQS@@
  funext v
  fin_cases v <;> simp only [xstar, Fin.reduceFinMk, Fin.isValue] <;> linarith

theorem xstar_extreme : xstar ∈ Set.extremePoints ℝ (coveringPolyhedron C11) := by
  rw [mem_extremePoints]
  refine ⟨xstar_mem, fun y hy z hz hseg => ?_⟩
  obtain ⟨a, b, ha, hb, hab, h⟩ := hseg
  have hpt : ∀ v, a * y v + b * z v = 1 / 3 := fun v => by
    have := congrFun h v
    simpa [xstar] using this
  have hsum : ∀ i < 11, a * (∑ v ∈ X' i, y v) + b * (∑ v ∈ X' i, z v) = 1 := by
    intro i hi
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    simp only [hpt, Finset.sum_const, card_X i hi, nsmul_eq_mul]
    norm_num
  have hy1 : ∀ i < 11, ∑ v ∈ X' i, y v = 1 := fun i hi =>
    tight ha hb hab (hy.2 _ (mem_C11.2 ⟨i, hi, rfl⟩)) (hz.2 _ (mem_C11.2 ⟨i, hi, rfl⟩))
      (hsum i hi)
  have hz1 : ∀ i < 11, ∑ v ∈ X' i, z v = 1 := fun i hi =>
    tight hb ha (by linarith) (hz.2 _ (mem_C11.2 ⟨i, hi, rfl⟩))
      (hy.2 _ (mem_C11.2 ⟨i, hi, rfl⟩)) (by linarith [hsum i hi])
  exact ⟨eq_xstar hy1, eq_xstar hz1⟩

theorem C11_not_ideal : ¬ IsIdeal C11 := by
  intro h
  obtain ⟨z, hz⟩ := h xstar xstar_extreme 0
  have hz' : (z : ℝ) = 1 / 3 := by rw [← hz]; rfl
  have h1 : (0 : ℝ) < z := by rw [hz']; norm_num
  have h2 : (z : ℝ) < 1 := by rw [hz']; norm_num
  have h1' : 0 < z := by exact_mod_cast h1
  have h2' : z < 1 := by exact_mod_cast h2
  omega

/-! ## Main results -/

/-- `C11` is a nonideal clutter without Király functions. -/
theorem counterexample : IsClutter C11 ∧ ¬ IsIdeal C11 ∧ ¬ KiralyProperty C11 :=
  ⟨C11_clutter, C11_not_ideal, not_kiraly⟩

/-- **MathDB 388087 is answered in the negative**: Király's conjecture is false. -/
theorem kiraly_conjecture_false : ¬ KiralyConjecture := by
  intro h
  exact not_kiraly ((h (Fin 11) C11 C11_clutter).1 C11_not_ideal)

end KiralyClutter

#print axioms KiralyClutter.kiraly_conjecture_false
#print axioms KiralyClutter.counterexample
