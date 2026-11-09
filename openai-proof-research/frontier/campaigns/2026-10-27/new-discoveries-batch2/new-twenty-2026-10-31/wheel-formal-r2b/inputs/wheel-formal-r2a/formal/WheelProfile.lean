import DeletionGrid
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
open scoped BigOperators
namespace WheelFormal
abbrev WheelSet (t : ℕ) := Finset (Option (ZMod (2*t+1)) × Option (ZMod (2*t+1)))
noncomputable def mixedA (t : ℕ) (s : WheelSet t) : Finset (ZMod (2*t+1)) :=
  Finset.univ.filter (fun i => (some i,none) ∈ s)
noncomputable def mixedB (t : ℕ) (s : WheelSet t) : Finset (ZMod (2*t+1)) :=
  Finset.univ.filter (fun i => (none,some i) ∈ s)
noncomputable def rimSet (t : ℕ) (s : WheelSet t) : Finset (ZMod (2*t+1) × ZMod (2*t+1)) :=
  Finset.univ.filter (fun z => (some z.1,some z.2) ∈ s)

@[simp] theorem mem_mixedA (t : ℕ) (s : WheelSet t) (i : ZMod (2*t+1)) :
    i ∈ mixedA t s ↔ (some i,none) ∈ s := by
  classical
  simp [mixedA]
@[simp] theorem mem_mixedB (t : ℕ) (s : WheelSet t) (i : ZMod (2*t+1)) :
    i ∈ mixedB t s ↔ (none,some i) ∈ s := by
  classical
  simp [mixedB]
@[simp] theorem mem_rimSet (t : ℕ) (s : WheelSet t) (z : ZMod (2*t+1) × ZMod (2*t+1)) :
    z ∈ rimSet t s ↔ (some z.1,some z.2) ∈ s := by
  classical
  simp [rimSet]

theorem weight_profile (t : ℕ) (s : WheelSet t) :
    (∑ v ∈ s, vertexWeight t v) =
      (if (none,none) ∈ s then 2 else 0) +
      ((t:ℝ)+1)*((mixedA t s).card+(mixedB t s).card)+2*(rimSet t s).card := by
  classical
  have hh : (∑ v ∈ s, vertexWeight t v) = ∑ v, if v ∈ s then vertexWeight t v else 0 := by
    simp [← Finset.sum_filter]
  rw [hh]
  simp only [Fintype.sum_prod_type, Fintype.sum_option, vertexWeight]
  simp only [Finset.sum_add_distrib]
  have ha : (∑ i : ZMod (2*t+1), if (some i,none) ∈ s then ((t:ℝ)+1) else 0) =
      ((t:ℝ)+1)*(mixedA t s).card := by simp [mixedA, Finset.sum_ite, mul_comm]; ring
  have hb : (∑ i : ZMod (2*t+1), if (none,some i) ∈ s then ((t:ℝ)+1) else 0) =
      ((t:ℝ)+1)*(mixedB t s).card := by simp [mixedB, Finset.sum_ite, mul_comm]; ring
  have hr : (∑ i : ZMod (2*t+1), ∑ j : ZMod (2*t+1), if (some i,some j) ∈ s then (2:ℝ) else 0) =
      2*(rimSet t s).card := by
    rw [← Fintype.sum_prod_type (f := fun z : ZMod (2*t+1) × ZMod (2*t+1) => if (some z.1,some z.2) ∈ s then (2:ℝ) else 0)]
    simp [rimSet, Finset.sum_ite, mul_comm]
  rw [ha,hb,hr]
  ring

theorem mixedA_card (t : ℕ) (ht : 1 ≤ t) (s : WheelSet t)
    (hs : Independent (wheelSquare t) s) : (mixedA t s).card ≤ t := by
  apply cycle_independent_card t ht
  intro x hx y hy hn he
  exact hs _ (mem_mixedA t s x |>.mp hx) _ (mem_mixedA t s y |>.mp hy)
    (by simpa using hn) (by simp [wheelSquare, SimpleGraph.boxProd, wheel,he])

theorem mixedB_card (t : ℕ) (ht : 1 ≤ t) (s : WheelSet t)
    (hs : Independent (wheelSquare t) s) : (mixedB t s).card ≤ t := by
  apply cycle_independent_card t ht
  intro x hx y hy hn he
  exact hs _ (mem_mixedB t s x |>.mp hx) _ (mem_mixedB t s y |>.mp hy)
    (by simpa using hn) (by simp [wheelSquare, SimpleGraph.boxProd, wheel,he])

theorem rim_avoids_mixed (t : ℕ) (s : WheelSet t)
    (hs : Independent (wheelSquare t) s) :
    rimSet t s ⊆ (mixedA t s)ᶜ ×ˢ (mixedB t s)ᶜ := by
  classical
  rintro ⟨i,j⟩ hz
  have hz' := (mem_rimSet t s (i,j)).mp hz
  simp only [Finset.mem_product, Finset.mem_compl, mem_mixedA, mem_mixedB]
  constructor
  · intro hi
    exact hs _ hi _ hz' (by simp) (by simp [wheelSquare, SimpleGraph.boxProd,wheel])
  · intro hj
    exact hs _ hj _ hz' (by simp) (by simp [wheelSquare, SimpleGraph.boxProd,wheel])

theorem rim_grid_independent (t : ℕ) (s : WheelSet t)
    (hs : Independent (wheelSquare t) s) :
    ∀ x ∈ rimSet t s, ∀ y ∈ rimSet t s, x ≠ y →
      ¬ ((x.1 = y.1 ∧ rimAdj (2*t+1) x.2 y.2) ∨
         (rimAdj (2*t+1) x.1 y.1 ∧ x.2 = y.2)) := by
  intro x hx y hy hn he
  have hne : (some x.1,some x.2) ≠ (some y.1,some y.2) := by simpa [Prod.ext_iff] using hn
  exact hs _ ((mem_rimSet t s x).mp hx) _ ((mem_rimSet t s y).mp hy) hne
    (by simpa [wheelSquare, SimpleGraph.boxProd, wheel] using (by tauto : (rimAdj (2*t+1) x.1 y.1 ∧ x.2 = y.2) ∨ (rimAdj (2*t+1) x.2 y.2 ∧ x.1 = y.1)))

/-- Bound rim vertices by surviving columns times the cyclic fibre bound. -/
theorem rim_column_bound (t : ℕ) (ht : 1 ≤ t) (s : WheelSet t)
    (hs : Independent (wheelSquare t) s) :
    (rimSet t s).card ≤ (2*t+1-(mixedB t s).card)*t := by
  classical
  let R : ZMod (2*t+1) → Finset (ZMod (2*t+1)) :=
    fun j => Finset.univ.filter (fun i => (some i,some j) ∈ s)
  have hc : (rimSet t s).card = ∑ j, (R j).card := by
    simp only [rimSet, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type, R]
    rw [Finset.sum_comm]
  have hf : ∀ j, (R j).card ≤ if j ∈ mixedB t s then 0 else t := by
    intro j
    by_cases hj : j ∈ mixedB t s
    · have he : R j = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        have hr : (i,j) ∈ rimSet t s := by simpa [R] using hi
        have ha := rim_avoids_mixed t s hs hr
        exact (Finset.mem_compl.mp (Finset.mem_product.mp ha).2) hj
      simp [hj,he]
    · simp only [hj,ite_false]
      apply cycle_independent_card t ht
      intro x hx y hy hn he
      have hx' : (some x,some j) ∈ s := by simpa [R] using hx
      have hy' : (some y,some j) ∈ s := by simpa [R] using hy
      exact hs _ hx' _ hy' (by simpa using hn)
        (by simp [wheelSquare,SimpleGraph.boxProd,wheel,he])
  rw [hc]
  calc
    _ ≤ ∑ j, if j ∈ mixedB t s then 0 else t := Finset.sum_le_sum (fun j _ => hf j)
    _ = _ := by
      rw [Finset.sum_ite]
      simp only [Finset.sum_const_zero, zero_add]
      have he : (Finset.univ.filter (fun j => j ∉ mixedB t s)) = (mixedB t s)ᶜ := by ext; simp
      rw [he]
      simp [Finset.card_compl, ZMod.card]

theorem rim_row_bound (t : ℕ) (ht : 1 ≤ t) (s : WheelSet t)
    (hs : Independent (wheelSquare t) s) :
    (rimSet t s).card ≤ (2*t+1-(mixedA t s).card)*t := by
  classical
  let R : ZMod (2*t+1) → Finset (ZMod (2*t+1)) :=
    fun i => Finset.univ.filter (fun j => (some i,some j) ∈ s)
  have hc : (rimSet t s).card = ∑ i, (R i).card := by
    simp only [rimSet, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type, R]
  have hf : ∀ i, (R i).card ≤ if i ∈ mixedA t s then 0 else t := by
    intro i
    by_cases hi : i ∈ mixedA t s
    · have he : R i = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro j hj
        have hr : (i,j) ∈ rimSet t s := by simpa [R] using hj
        have ha := rim_avoids_mixed t s hs hr
        exact (Finset.mem_compl.mp (Finset.mem_product.mp ha).1) hi
      simp [hi,he]
    · simp only [hi,ite_false]
      apply cycle_independent_card t ht
      intro x hx y hy hn he
      exact rim_fibre_independent t s hs i x y (by simpa [R] using hx) (by simpa [R] using hy) hn he
  rw [hc]
  calc
    _ ≤ ∑ i, if i ∈ mixedA t s then 0 else t := Finset.sum_le_sum (fun i _ => hf i)
    _ = _ := by
      rw [Finset.sum_ite]
      simp only [Finset.sum_const_zero, zero_add]
      have he : (Finset.univ.filter (fun i => i ∉ mixedA t s)) = (mixedA t s)ᶜ := by ext; simp
      rw [he]
      simp [Finset.card_compl, ZMod.card]
end WheelFormal
