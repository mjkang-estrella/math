import Measurability
set_option autoImplicit false
namespace LiteralGame
attribute [local instance] Classical.propDecidable
open Filter
open scoped Topology

theorem eventProb_union_le (N : ℕ) (A B : Set (Outcome N)) :
    eventProb N (A∪B) ≤ eventProb N A+eventProb N B := by
  unfold eventProb
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro w _
  have hp : (0:ℝ)≤(P N w:ℝ) := by exact_mod_cast P_nonneg N w
  by_cases ha : w∈A <;> by_cases hb : w∈B <;> simp [ha,hb,hp]

theorem eventProb_cover (N : ℕ) (A B C : Set (Outcome N)) (h : A ⊆ B∪C) :
    eventProb N A ≤ eventProb N B+eventProb N C :=
  (eventProb_mono N h).trans (eventProb_union_le N B C)

noncomputable def cdf (N m : ℕ) : ℝ := eventProb N {w | w.val.length < m}

theorem cdf_end (N : ℕ) : cdf N (duration N+1) = 1 := by
  have he : {w : Outcome N | w.val.length < duration N+1} = Set.univ := by
    ext w
    simp only [Set.mem_univ,iff_true]
    exact Nat.lt_succ_of_le (length_le_duration w.property)
  unfold cdf
  rw [he,eventProb_univ]

theorem median_exists (N : ℕ) : ∃ m, (1:ℝ)/2 ≤ cdf N m :=
  ⟨duration N+1,by rw [cdf_end]; norm_num⟩
noncomputable def median (N : ℕ) : ℕ := Nat.find (median_exists N)

theorem median_lower (N : ℕ) : (1:ℝ)/2 ≤ cdf N (median N) :=
  Nat.find_spec (median_exists N)
theorem median_pos (N : ℕ) : 1 ≤ median N := by
  have h := median_lower N
  by_contra hn
  have hz : median N=0 := by omega
  simp [hz,cdf,eventProb] at h
theorem median_previous (N : ℕ) : cdf N (median N-1) < (1:ℝ)/2 := by
  exact lt_of_not_ge (Nat.find_min (median_exists N) (by have := median_pos N; omega))

noncomputable def window (N : ℕ) (a : ℤ) (h : ℕ) : Set (Outcome N) :=
  {w | a ≤ (w.val.length:ℤ) ∧ (w.val.length:ℤ) ≤ a+h}

theorem window_formula (N : ℕ) (a : ℤ) (h : ℕ) :
    eventProb N (window N a h) =
      ∑ w ∈ completeDomain N, (P N w:ℝ)*
        (if a≤(w.length:ℤ) ∧ (w.length:ℤ)≤a+h then 1 else 0) := by
  unfold eventProb window
  simp only [Set.mem_setOf_eq]
  simp only [mul_ite,mul_one,mul_zero]
  exact Finset.sum_attach _ _

theorem median_upper {N n : ℕ}
    (hi : ∀ a : ℤ, eventProb N (window N a (3*n^6)) ≤ intervalError n) :
    cdf N (median N) ≤ 1/2+intervalError n := by
  have hc := eventProb_cover N {w | w.val.length < median N}
    {w | w.val.length < median N-1} (window N (median N-1) (3*n^6)) (by
      intro w hw
      by_cases hh : w.val.length < median N-1
      · exact Or.inl hh
      · right; change (median N-1:ℕ)≤(w.val.length:ℤ) ∧ _
        have := median_pos N
        constructor <;> omega)
  have hprev := median_previous N
  have hbound := hi (median N-1)
  change cdf N (median N) ≤ cdf N (median N-1)+_ at hc
  linarith

noncomputable def late (N r : ℕ) : Set (Outcome N) := {w | r ≤ lastSplit w.val}
noncomputable def badSuffix (N n : ℕ) : Set (Outcome N) :=
  {w | n^6 < w.val.length-lastSplit w.val}

theorem badSuffix_formula (N n : ℕ) : eventProb N (badSuffix N n) = actualSuffixMass N n := by
  unfold eventProb badSuffix actualSuffixMass
  simp only [Set.mem_setOf_eq,mul_ite,mul_one,mul_zero]
  exact Finset.sum_attach _ _

theorem late_lower {N n k : ℕ} (hk : k≤n^6)
    (hi : ∀ a : ℤ, eventProb N (window N a (3*n^6)) ≤ intervalError n)
    (hs : actualSuffixMass N n ≤ suffixError n) :
    1/2-2*intervalError n-suffixError n ≤ eventProb N (late N (median N+k)) := by
  have hc := eventProb_cover N Set.univ
    ({w | w.val.length < median N} ∪ window N (median N) (3*n^6))
    (badSuffix N n ∪ late N (median N+k)) (by
      intro w _
      by_cases ha : w.val.length < median N
      · exact Or.inl (Or.inl ha)
      by_cases hb : n^6 < w.val.length-lastSplit w.val
      · exact Or.inr (Or.inl hb)
      by_cases hc : median N+k ≤ lastSplit w.val
      · exact Or.inr (Or.inr hc)
      · left; right
        change (median N:ℤ) ≤ (w.val.length:ℤ) ∧ _
        have := lastSplit_le w.val
        constructor <;> omega)
  rw [eventProb_univ] at hc
  have h₁ := eventProb_union_le N {w | w.val.length < median N} (window N (median N) (3*n^6))
  have h₂ := eventProb_union_le N (badSuffix N n) (late N (median N+k))
  rw [badSuffix_formula] at h₂
  have h₃ := median_upper hi
  have h₄ := hi (median N)
  change eventProb N _ ≤ cdf N (median N)+_ at h₁
  linarith

theorem alpha_stopping_lower {N m k : ℕ} (hk : 1≤k) (hm : m≤duration N) :
    cdf N m * eventProb N (late N (m+k)) ≤ literalAlpha N k := by
  let A : Set (Outcome N) := {w | w.val.length < m}
  let B := late N (m+k)
  have hd : A∩B = ∅ := Set.disjoint_iff_inter_eq_empty.mp (disjoint_stopping_events N m k hk)
  have hp := eventProb_nonneg N A
  have hq := eventProb_nonneg N B
  have he : |eventProb N (A∩B)-eventProb N A*eventProb N B| =
      cdf N m*eventProb N B := by
    rw [hd]
    simp only [eventProb,Set.mem_empty_iff_false,ite_false,Finset.sum_const_zero,
      zero_sub,abs_neg,abs_of_nonneg (mul_nonneg hp hq)]
    rfl
  rw [← he]
  apply le_csSup
  · exact ⟨1/4,by rintro x ⟨j,_,C,D,_,_,rfl⟩; exact covariance_abs_upper N C D⟩
  · exact ⟨m,hm,A,B,termination_measurable N m,
      lastSplit_measurable N (m+k) (by omega),rfl⟩

end LiteralGame
