import Injection
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace LiteralGame
noncomputable def blockLower (n : ℕ) : ℚ := ((2*n : ℕ) : ℚ)⁻¹ ^ 3

theorem branch_reciprocal_lower {b : Board} {n : ℕ} {m : Move}
    (hm : m ∈ legalTypes b) (hn : 1 ≤ n) (hc : (legalTypes b).card ≤ 2*n) :
    (((2*n : ℕ) : ℚ)⁻¹) ≤ ((legalTypes b).card : ℚ)⁻¹ := by
  have hpos : (0 : ℚ) < (legalTypes b).card := by
    exact_mod_cast (Finset.card_pos.mpr ⟨m,hm⟩)
  have hbound : ((legalTypes b).card : ℚ) ≤ (2*n : ℕ) := by exact_mod_cast hc
  exact (inv_le_inv₀ (by positivity) hpos).mpr hbound

theorem actual_triple_conditional_lower {N n : ℕ} {u : List Move} {b c d e : Board}
    (hu : Executes (initial N) u b) (hn : 1 ≤ n) (hN : N < F (n+1))
    (h1 : Step b .C1 c) (h2 : Step c .C1 d) (h3 : Step d C2 e) :
    blockLower n ≤ cylinderMass N (u ++ [.C1,.C1,C2]) / cylinderMass N u := by
  have hm1 := (mem_legalTypes _ _).mpr ⟨c,h1⟩
  have hm2 := (mem_legalTypes _ _).mpr ⟨d,h2⟩
  have hm3 := (mem_legalTypes _ _).mpr ⟨e,h3⟩
  have hc := executes_append hu (Executes.cons h1 (Executes.nil _))
  have hd := executes_append hc (Executes.cons h2 (Executes.nil _))
  have hl1 := branch_reciprocal_lower hm1 hn (reachable_types_le hu hn hN)
  have hl2 := branch_reciprocal_lower hm2 hn (reachable_types_le hc hn hN)
  have hl3 := branch_reciprocal_lower hm3 hn (reachable_types_le hd hn hN)
  rw [actual_prefix_continuation hu
    (Executes.cons h1 (Executes.cons h2 (Executes.cons h3 (Executes.nil _))))]
  have hn1 := step_deterministic (next_step hm1) h1
  have hn2 := step_deterministic (next_step hm2) h2
  simp only [reciprocalProduct,ite_eq_left hm1,hn1,ite_eq_left hm2,hn2,
    ite_eq_left hm3,mul_one]
  dsimp [blockLower]
  have hz : (0 : ℚ) ≤ ((2*n : ℕ) : ℚ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  calc
    _ = ((2*n : ℕ) : ℚ)⁻¹ *
      (((2*n : ℕ) : ℚ)⁻¹ * ((2*n : ℕ) : ℚ)⁻¹) := by ring
    _ ≤ _ := mul_le_mul hl1 (mul_le_mul hl2 hl3 hz (le_trans hz hl2))
      (mul_nonneg hz hz) (le_trans hz hl1)

theorem actual_early_success_lower {N n j : ℕ} {u : List Move} {b : Board}
    (hu : Executes (initial N) u b) (hn : 1 ≤ n) (hN : N < F (n+1))
    (hlen : u.length=3*j) (hj : j<N/6) :
    (¬ Terminal b) ∧ (∃ c d e, Step b .C1 c ∧ Step c .C1 d ∧ Step d C2 e) ∧
      blockLower n ≤ cylinderMass N (u ++ [.C1,.C1,C2]) / cylinderMass N u := by
  have hsix := early_block_six hu hlen hj
  obtain ⟨c,d,e,h1,h2,h3⟩ := six_triple hsix
  exact ⟨six_not_terminal hsix,⟨c,d,e,h1,h2,h3⟩,
    actual_triple_conditional_lower hu hn hN h1 h2 h3⟩

-- This is the source-applicable combinatorial bridge, with no assumed marks.
theorem actual_success_count_le_marks {N : ℕ} {w : List Move}
    (hw : w ∈ completeWords N) :
    (successSlots (N/6) w).card ≤ (markedSlots (initial N) (compress w)).card := by
  obtain ⟨c,he,_⟩ := hw
  exact success_count_le_marks he _

theorem complete_length_blocks {N : ℕ} {w : List Move}
    (hw : w ∈ completeWords N) : 3*(N/6) ≤ w.length := by
  obtain ⟨c,he,ht⟩ := hw
  have ho := executes_ones he
  simp only [initial,Multiset.count_replicate_self] at ho
  by_contra h
  have htwo : 2 ≤ c.count 1 := by omega
  exact ht _ _ (next_step (C1_legal htwo))

noncomputable def badMarksMass (N t : ℕ) : ℚ := by
  classical
  exact ∑ w ∈ (completeDomain N).filter
    (fun w => (markedSlots (initial N) (compress w)).card < t), P N w
noncomputable def badSuccessMass (N t : ℕ) : ℚ := by
  classical
  exact ∑ w ∈ (completeDomain N).filter
    (fun w => (successSlots (N/6) w).card < t), P N w

theorem actual_bad_marks_le_bad_success (N t : ℕ) :
    badMarksMass N t ≤ badSuccessMass N t := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro w hw
    obtain ⟨hw,ht⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨hw,lt_of_le_of_lt
      (actual_success_count_le_marks ((domain_exact N w).mp hw)) ht⟩
  · intro w _ _; exact P_nonneg N w

theorem bad_threshold_zero (N : ℕ) : badMarksMass N 0 = 0 ∧ badSuccessMass N 0 = 0 := by
  simp [badMarksMass,badSuccessMass]

theorem zero_input_bad_mass (t : ℕ) :
    badMarksMass 0 t = (if 0<t then 1 else 0) := by
  classical
  simp [badMarksMass,completeDomain_zero,compress,markedSlots,P_zero]
end LiteralGame
