import Product
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LiteralGame

theorem executes_append {a b c : Board} {u v : List Move}
    (hu : Executes a u b) (hv : Executes b v c) : Executes a (u ++ v) c := by
  induction hu with
  | nil => exact hv
  | cons hs _ ih => exact Executes.cons hs (ih hv)

theorem executes_split {a c : Board} {u v : List Move}
    (h : Executes a (u ++ v) c) : ∃ b, Executes a u b ∧ Executes b v c := by
  induction u generalizing a with
  | nil => exact ⟨a,Executes.nil a,h⟩
  | cons m u ih =>
    cases h with
    | cons hs hr =>
      obtain ⟨b,hu,hv⟩ := ih hr
      exact ⟨b,Executes.cons hs hu,hv⟩

noncomputable def cylinderDomain (N : ℕ) (u : List Move) : Finset (List Move) := by
  classical
  exact (completeDomain N).filter (fun w => u.IsPrefix w)
noncomputable def cylinderMass (N : ℕ) (u : List Move) : ℚ :=
  ∑ w ∈ cylinderDomain N u, P N w

theorem cylinder_image {N : ℕ} {u : List Move} {b : Board}
    (hu : Executes (initial N) u b) :
    cylinderDomain N u =
      (continuations (potential b).toNat b).image (fun v => u ++ v) := by
  classical
  have hb := executes_positive hu (initial_positive N)
  ext w
  simp only [cylinderDomain,Finset.mem_filter,Finset.mem_image]
  constructor
  · rintro ⟨hw,⟨v,rfl⟩⟩
    obtain ⟨c,he,ht⟩ := (domain_exact N _).mp hw
    obtain ⟨b',hu',hv⟩ := executes_split he
    have hbb := executes_deterministic hu hu'
    subst b'
    exact ⟨v,(continuation_iff _ _ hb (le_refl _) v).mpr ⟨c,hv,ht⟩,rfl⟩
  · rintro ⟨v,hv,rfl⟩
    obtain ⟨c,he,ht⟩ := (continuation_iff _ _ hb (le_refl _) v).mp hv
    exact ⟨(domain_exact N _).mpr ⟨c,executes_append hu he,ht⟩,⟨v,rfl⟩⟩

theorem continuation_product_normalized (b : Board) (hb : Positive b) :
    ∑ v ∈ continuations (potential b).toNat b, reciprocalProduct b v = 1 := by
  classical
  calc
    _ = ∑ v ∈ continuations (potential b).toNat b,
        depthWeight (potential b).toNat b v := by
      apply Finset.sum_congr rfl
      intro v hv
      obtain ⟨c,he,ht⟩ := (continuation_iff _ _ hb (le_refl _) v).mp hv
      exact (depth_product _ _ hb (le_refl _) he ht).symm
    _ = 1 := depth_normalized _ _

theorem actual_prefix_mass {N : ℕ} {u : List Move} {b : Board}
    (hu : Executes (initial N) u b) :
    cylinderMass N u = reciprocalProduct (initial N) u := by
  classical
  rw [cylinderMass,cylinder_image hu]
  rw [Finset.sum_image (by intros x hx y hy h; exact List.append_cancel_left h)]
  have hb := executes_positive hu (initial_positive N)
  have hf := executes_fold hu
  calc
    _ = ∑ v ∈ continuations (potential b).toNat b,
        reciprocalProduct (initial N) u * reciprocalProduct b v := by
      apply Finset.sum_congr rfl
      intro v hv
      obtain ⟨c,he,ht⟩ := (continuation_iff _ _ hb (le_refl _) v).mp hv
      rw [P_product N ⟨c,executes_append hu he,ht⟩,reciprocal_append,hf]
    _ = _ := by rw [← Finset.mul_sum,continuation_product_normalized b hb,mul_one]

theorem actual_prefix_positive {N : ℕ} {u : List Move} {b : Board}
    (hu : Executes (initial N) u b) : 0 < cylinderMass N u := by
  rw [actual_prefix_mass hu]
  exact execution_product_pos hu

theorem actual_prefix_transition {N : ℕ} {u : List Move} {b : Board} {m : Move}
    (hu : Executes (initial N) u b) (hm : m ∈ legalTypes b) :
    cylinderMass N (u ++ [m]) / cylinderMass N u = ((legalTypes b).card : ℚ)⁻¹ := by
  have he := executes_append hu (Executes.cons (next_step hm) (Executes.nil _))
  rw [actual_prefix_mass he,actual_prefix_mass hu,reciprocal_append,executes_fold hu]
  simp only [reciprocalProduct,ite_eq_left hm,mul_one]
  exact mul_div_cancel_left₀ _ (ne_of_gt (execution_product_pos hu))

theorem actual_prefix_continuation {N : ℕ} {u v : List Move} {b c : Board}
    (hu : Executes (initial N) u b) (hv : Executes b v c) :
    cylinderMass N (u ++ v) / cylinderMass N u = reciprocalProduct b v := by
  rw [actual_prefix_mass (executes_append hu hv),actual_prefix_mass hu,
    reciprocal_append,executes_fold hu]
  exact mul_div_cancel_left₀ _ (ne_of_gt (execution_product_pos hu))

theorem actual_empty_prefix (N : ℕ) : cylinderMass N [] = 1 := by
  rw [actual_prefix_mass (Executes.nil _)]
  rfl
end LiteralGame
