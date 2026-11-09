import FiniteEntropy333569

namespace MathDB333569
noncomputable section
open MeasureTheory Set
open scoped ENNReal

/-- Membership is determined by a finite integer interval. -/
def IntervalPast (E : Set (ℤ → Fin 2)) (k : ℤ) (n : ℕ) : Prop :=
  ∀ x y, (∀ i : ℤ, k ≤ i → i ≤ k+n → x i = y i) → (x ∈ E ↔ y ∈ E)

theorem intervalPast_mono {E : Set (ℤ → Fin 2)} {k : ℤ} {n m : ℕ}
    (h : IntervalPast E k n) (hn : n ≤ m) : IntervalPast E k m := by
  intro x y hxy
  exact h x y (fun i hi hj => hxy i hi (by omega))

theorem intervalPast_inter_endpoint {E : Set (ℤ → Fin 2)} {k : ℤ} {n : ℕ}
    (h : IntervalPast E k n) (a : Fin 2) :
    IntervalPast (E ∩ {x | x (k+n) = a}) k n := by
  intro x y hxy
  have he := h x y hxy
  have hp := hxy (k+n) (by omega) (by omega)
  simp only [mem_inter_iff, mem_ofPred_eq, hp, he]

/-- A finite block partitions every event, without a measurability assumption
on the event (the restrictions are evaluated on measurable block atoms). -/
theorem measure_block_partition (μ : Measure (ℤ → Fin 2))
    (E : Set (ℤ → Fin 2)) (k : ℤ) (n : ℕ) :
    μ E = ∑ w : Fin (n+1) → Fin 2,
      μ ({x | ∀ j : Fin (n+1), x (k+j.val) = w j} ∩ E) := by
  classical
  let f : (ℤ → Fin 2) → (Fin (n+1) → Fin 2) := fun x j => x (k+j.val)
  have hm (w : Fin (n+1) → Fin 2) : MeasurableSet (f ⁻¹' {w}) :=
    (measurableSet_singleton w).preimage (by fun_prop)
  have hs := sum_measure_preimage_singleton (μ := μ.restrict E) (f := f)
    Finset.univ (fun w _ => hm w)
  simp only [Finset.coe_univ, preimage_univ, Measure.restrict_apply_univ] at hs
  simp_rw [Measure.restrict_apply (hm _)] at hs
  simpa only [f, preimage, mem_singleton_iff, funext_iff] using hs.symm

/-- One-step factorization for any event determined by a finite past interval
and prescribing its final symbol. -/
theorem twoSidedLaw_past_next (z : ℝ × ℝ) (hz : z ∈ interior)
    (E : Set (ℤ → Fin 2)) (k : ℤ) (n : ℕ) (a b : Fin 2)
    (hE : IntervalPast E k n) (ha : ∀ x ∈ E, x (k+n) = a) :
    twoSidedLaw z hz (E ∩ {x | x (k+(n+1)) = b}) =
      twoSidedLaw z hz E * ENNReal.ofReal (trans z a b) := by
  classical
  rw [measure_block_partition _ (E ∩ _) k n, measure_block_partition _ E k n,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w _
  let B : Set (ℤ → Fin 2) := {x | ∀ j : Fin (n+1), x (k+j.val) = w j}
  by_cases hh : (B ∩ E).Nonempty
  · obtain ⟨v,hv,hvE⟩ := hh
    have hBE : B ⊆ E := by
      intro x hx
      apply (hE x v ?_).mpr hvE
      intro i hi hj
      let j : Fin (n+1) := ⟨(i-k).toNat, by omega⟩
      have he : k+(j.val : ℤ) = i := by dsimp [j]; omega
      rw [← he, hx j, hv j]
    have he : B ∩ E = B := inter_eq_left.mpr hBE
    have ha' : w (Fin.last n) = a := by
      have hw := hv (Fin.last n)
      simpa only [Fin.val_last] using hw.symm.trans (ha v hvE)
    change twoSidedLaw z hz (B ∩ (E ∩ _)) = _
    rw [← inter_assoc, he]
    change twoSidedLaw z hz {x | (∀ j : Fin (n+1), x (k+j.val) = w j) ∧
      x (k+(n+1)) = b} = _
    rw [twoSidedLaw_prefix_next, ha']
  · have he : B ∩ E = ∅ := not_nonempty_iff_eq_empty.mp hh
    change twoSidedLaw z hz (B ∩ (E ∩ _)) = twoSidedLaw z hz (B ∩ E) * _
    rw [← inter_assoc, he]
    simp

/-- Contract every unobserved symbol between a finite past and a future point.
The remaining expression is the explicit matrix-power kernel, not a marginal sum. -/
theorem twoSidedLaw_past_gap {l t : ℝ} (hl : 0 < l) (hl1 : l < 1)
    (ht : -1 < t) (ht1 : t < 1)
    (E : Set (ℤ → Fin 2)) (k : ℤ) (n : ℕ) (a b : Fin 2)
    (hE : IntervalPast E k n) (ha : ∀ x ∈ E, x (k+n) = a) (g : ℕ) :
    twoSidedLaw (chart l t) (chart_mem_interior hl hl1 ht ht1)
      (E ∩ {x | x (k+n+g) = b}) =
    twoSidedLaw (chart l t) (chart_mem_interior hl hl1 ht ht1) E *
      ENNReal.ofReal (kernel (l^g) t a b) := by
  classical
  let z := chart l t
  let hz := chart_mem_interior hl hl1 ht ht1
  let μ := twoSidedLaw z hz
  change μ _ = μ E * _
  induction g generalizing b with
  | zero =>
    by_cases hab : a = b
    · subst b
      have he : E ∩ {x | x (k+n+(0:ℕ)) = a} = E := by
        ext x; simp only [Nat.cast_zero, add_zero, mem_inter_iff, mem_ofPred_eq]
        exact ⟨fun h => h.1, fun h => ⟨h,ha x h⟩⟩
      rw [he]; simp [kernel]
    · have he : E ∩ {x | x (k+n+(0:ℕ)) = b} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro x ⟨hx,hb⟩
        exact hab ((ha x hx).symm.trans (by simpa using hb))
      rw [he]; simp [kernel, hab]
  | succ g ih =>
    have hm (c : Fin 2) : MeasurableSet {x : ℤ → Fin 2 | x (k+n+g) = c} :=
      measurableSet_eq_fun (by fun_prop) measurable_const
    have hs := sum_measure_preimage_singleton
      (μ := μ.restrict (E ∩ {x | x (k+n+(g+1:ℕ)) = b}))
      (f := fun x => x (k+n+g)) Finset.univ (fun c _ => hm c)
    simp only [Finset.coe_univ, preimage_univ, Measure.restrict_apply_univ] at hs
    change (∑ c : Fin 2, (μ.restrict (E ∩ {x | x (k+n+(g+1:ℕ)) = b}))
      {x | x (k+n+g) = c}) = μ (E ∩ {x | x (k+n+(g+1:ℕ)) = b}) at hs
    simp_rw [Measure.restrict_apply (hm _)] at hs
    have he (c : Fin 2) : {x : ℤ → Fin 2 | x (k+n+g) = c} ∩
        (E ∩ {x | x (k+n+(g+1:ℕ)) = b}) =
        (E ∩ {x | x (k+(n+g:ℕ)) = c}) ∩ {x | x (k+((n+g)+1:ℕ)) = b} := by
      ext x; simp only [mem_inter_iff, mem_ofPred_eq, Nat.cast_add, Nat.cast_one]
      have h₁ : k+(n:ℤ)+g = k+(n+g) := by ring
      have h₂ : k+(n:ℤ)+(g+1) = k+(n+g+1) := by ring
      simp only [h₁, h₂]
      tauto
    simp_rw [he] at hs
    have hp (c : Fin 2) : μ ((E ∩ {x | x (k+(n+g:ℕ)) = c}) ∩
        {x | x (k+((n+g)+1:ℕ)) = b}) =
        μ (E ∩ {x | x (k+(n+g:ℕ)) = c}) * ENNReal.ofReal (trans z c b) :=
      twoSidedLaw_past_next z hz
      (E ∩ {x | x (k+(n+g:ℕ)) = c}) k (n+g) c b
      (intervalPast_inter_endpoint (intervalPast_mono hE (by omega)) c)
      (fun x hx => hx.2)
    simp only [Nat.cast_add, Nat.cast_one] at hp hs
    simp_rw [hp] at hs
    have hi (c : Fin 2) : μ (E ∩ {x | x (k+(n+g:ℕ)) = c}) =
        μ E * ENNReal.ofReal (kernel (l^g) t a c) := by
      simpa only [Nat.cast_add, ← add_assoc] using ih (b := c)
    simp only [Nat.cast_add] at hi
    simp_rw [hi] at hs
    simp only [z, chart_trans, mul_assoc] at hs
    rw [← Finset.mul_sum] at hs
    have hn (c : Fin 2) : 0 ≤ kernel (l^g) t a c := by
      cases g with
      | zero => simp [kernel]; positivity
      | succ g => exact (kernel_pos (pow_pos hl _) (pow_lt_one₀ hl.le hl1 (by omega)) ht ht1 a c).le
    have hc : (∑ c : Fin 2, ENNReal.ofReal (kernel (l^g) t a c) *
        ENNReal.ofReal (kernel l t c b)) = ENNReal.ofReal (kernel (l^(g+1)) t a b) := by
      simp_rw [← ENNReal.ofReal_mul (hn _)]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ => mul_nonneg (hn c)
        (kernel_pos hl hl1 ht ht1 c b).le), kernel_comp, pow_succ]
    rw [hc] at hs
    exact hs.symm


/-- Exact arbitrary selected-cylinder probability for the actual two-sided law. -/
theorem twoSidedLaw_selected {l t : ℝ} (hl : 0 < l) (hl1 : l < 1)
    (ht : -1 < t) (ht1 : t < 1) (d : ℕ)
    (s : Fin (d+1) → ℤ) (hs : StrictMono s) (a : Fin (d+1) → Fin 2) :
    twoSidedLaw (chart l t) (chart_mem_interior hl hl1 ht ht1)
      {x | ∀ j, x (s j) = a j} =
    ENNReal.ofReal (pi t (a 0) * ∏ j : Fin d,
      kernel (l ^ (s j.succ - s j.castSucc).toNat) t (a j.castSucc) (a j.succ)) := by
  classical
  induction d with
  | zero =>
    have he : {x : ℤ → Fin 2 | ∀ j : Fin 1, x (s j) = a j} =
        {x | ∀ j : Fin 1, x (s 0+j.val) = a j} := by
      ext x; simp
    rw [he, twoSidedLaw_word]
    simp [wordProb, chart_stationary (ne_of_lt hl1)]
  | succ d ih =>
    let s' : Fin (d+1) → ℤ := fun j => s j.castSucc
    let a' : Fin (d+1) → Fin 2 := fun j => a j.castSucc
    have hs' : StrictMono s' := fun i j hij => hs (by simpa using hij)
    let E : Set (ℤ → Fin 2) := {x | ∀ j, x (s' j) = a' j}
    let n := (s' (Fin.last d) - s' 0).toNat
    let g := (s (Fin.last (d+1)) - s' (Fin.last d)).toNat
    have hn : s' 0 + (n : ℤ) = s' (Fin.last d) := by
      have := hs'.monotone (Fin.zero_le (Fin.last d))
      dsimp [n]; omega
    have hg : s' (Fin.last d) + (g : ℤ) = s (Fin.last (d+1)) := by
      have hh := hs (show (Fin.last d).castSucc < Fin.last (d+1) by exact Fin.castSucc_lt_last (Fin.last d))
      dsimp [g, s']; omega
    have hE : IntervalPast E (s' 0) n := by
      intro x y hxy
      have he (j : Fin (d+1)) : x (s' j) = y (s' j) :=
        hxy (s' j) (hs'.monotone (Fin.zero_le j))
          (by rw [hn]; exact hs'.monotone (Fin.le_last j))
      change (∀ j, x (s' j) = a' j) ↔ (∀ j, y (s' j) = a' j)
      simp_rw [he]
    have h := twoSidedLaw_past_gap hl hl1 ht ht1 E (s' 0) n
      (a' (Fin.last d)) (a (Fin.last (d+1))) hE
      (fun x hx => by rw [hn]; exact hx (Fin.last d)) g
    have he : E ∩ {x | x (s' 0+n+g) = a (Fin.last (d+1))} =
        {x | ∀ j, x (s j) = a j} := by
      rw [hn, hg]
      ext x
      constructor
      · rintro ⟨hx,hb⟩ j
        exact Fin.lastCases hb (fun i => hx i) j
      · intro hx; exact ⟨fun i => hx i.castSucc, hx (Fin.last (d+1))⟩
    rw [he] at h
    have hi := ih s' hs' a'
    change twoSidedLaw _ _ E = _ at hi
    rw [hi] at h
    have hp : 0 ≤ pi t (a' 0) * ∏ j : Fin d,
        kernel (l ^ (s' j.succ - s' j.castSucc).toNat) t (a' j.castSucc) (a' j.succ) := by
      have heq := chart_stationary (ne_of_lt hl1) t (a' 0)
      apply mul_nonneg
      · rw [← heq]; exact (stationary_pos (chart_mem_interior hl hl1 ht ht1) _).le
      · apply Finset.prod_nonneg
        intro j _
        have hj : 0 < (s' j.succ - s' j.castSucc).toNat := by
          have := hs' (show j.castSucc < j.succ by exact Fin.castSucc_lt_succ)
          omega
        exact (kernel_pos (pow_pos hl _) (pow_lt_one₀ hl.le hl1 (by omega)) ht ht1 _ _).le
    rw [← ENNReal.ofReal_mul hp] at h
    rw [h]
    congr 1
    rw [Fin.prod_univ_castSucc]
    simp only [s', a', g, Fin.castSucc_zero]
    simp only [Fin.succ_castSucc, Fin.succ_last]
    ring

end
end MathDB333569
