import Median
set_option autoImplicit false
namespace LiteralGame
attribute [local instance] Classical.propDecidable
open Filter
open scoped Topology

theorem index_exists (N : ℕ) : ∃ n, 1≤n ∧ N<F (n+1) := by
  refine ⟨N+1,by omega,?_⟩
  have := index_le_fib (N+2)
  omega
noncomputable def fibIndex (N : ℕ) : ℕ := Nat.find (index_exists N)
theorem fibIndex_pos (N : ℕ) : 1≤fibIndex N := (Nat.find_spec (index_exists N)).1
theorem fibIndex_upper (N : ℕ) : N<F (fibIndex N+1) := (Nat.find_spec (index_exists N)).2
theorem fibIndex_lower (N : ℕ) (hN : 1≤N) : F (fibIndex N) ≤ N := by
  have hp := fibIndex_pos N
  by_cases h : fibIndex N=1
  · simpa [h,F] using hN
  · have hm := Nat.find_min (index_exists N) (show fibIndex N-1 < fibIndex N from by omega)
    have hn : ¬ N < F (fibIndex N) := by
      intro hc
      apply hm
      exact ⟨by omega,by simpa [Nat.sub_add_cancel hp] using hc⟩
    omega

theorem F_strict_step (n : ℕ) (hn : 1≤n) : F n < F (n+1) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hn
  have hp : 0<F j := Nat.fib_pos.mpr (by omega)
  have := F_rec j
  omega

theorem fibIndex_unique {N n : ℕ} (hn : 1≤n) (hl : F n≤N) (hu : N<F (n+1)) :
    fibIndex N=n := by
  have hp := fibIndex_pos N
  have hl' := fibIndex_lower N (by have := index_le_fib n; omega)
  have hu' := fibIndex_upper N
  have mono (a b : ℕ) (h : a≤b) : F a≤F b := Nat.fib_mono (by omega)
  by_contra h
  rcases lt_or_gt_of_ne h with hh | hh
  · have := mono (fibIndex N+1) n (by omega); omega
  · have := mono (n+1) (fibIndex N) (by omega); omega

theorem fibIndex_tendsto : Tendsto fibIndex atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (F (b+1))] with N hN
  have hu := fibIndex_upper N
  by_contra h
  have hm : F (fibIndex N+1) ≤ F (b+1) := Nat.fib_mono (by omega)
  omega

theorem eventual_median_bounds : ∀ᶠ n : ℕ in atTop, ∀ N : ℕ,
    F n≤N → N<F (n+1) → ∀ k : ℕ, 1≤k → k≤n^6 →
    median N≤duration N ∧
    1/4-intervalError n-suffixError n/2 ≤ literalAlpha N k := by
  have hz : Tendsto (fun n => 1/2-2*intervalError n-suffixError n) atTop (𝓝 (1/2:ℝ)) := by
    convert (tendsto_const_nhds.sub (tendsto_const_nhds.mul intervalError_limit)).sub suffixError_limit using 1 <;> norm_num
  have he := hz.eventually (lt_mem_nhds (show (0:ℝ)<1/2 by norm_num))
  filter_upwards [actual_interval_uniform,actual_suffix_uniform,he] with n hi hs he
  intro N hl hu k hk hk'
  have hi' : ∀ a : ℤ, eventProb N (window N a (3*n^6)) ≤ intervalError n := by
    intro a; rw [window_formula]; exact hi N hl hu a
  have hs' := hs N hl hu
  have hb := late_lower hk' hi' hs'
  have hbpos : 0<eventProb N (late N (median N+k)) := lt_of_lt_of_le he hb
  have hm : median N≤duration N := by
    by_contra hn
    have heq : late N (median N+k)=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro w hw
      change median N+k≤lastSplit w.val at hw
      have := lastSplit_le w.val
      have := length_le_duration w.property
      omega
    simp [heq,eventProb] at hbpos
  refine ⟨hm,?_⟩
  have ha := median_lower N
  have hm' := alpha_stopping_lower hk hm
  have hp := mul_le_mul_of_nonneg_right ha (le_of_lt hbpos)
  nlinarith

theorem all_N_alpha_limit :
    Tendsto (fun N => literalAlpha N ((fibIndex N)^6)) atTop (𝓝 (1/4:ℝ)) := by
  have hlow : Tendsto (fun N => 1/4-intervalError (fibIndex N)-suffixError (fibIndex N)/2)
      atTop (𝓝 (1/4:ℝ)) := by
    convert (tendsto_const_nhds.sub (intervalError_limit.comp fibIndex_tendsto)).sub
      ((suffixError_limit.comp fibIndex_tendsto).div_const 2) using 1 <;> norm_num
  have he : ∀ᶠ N : ℕ in atTop,
      1/4-intervalError (fibIndex N)-suffixError (fibIndex N)/2 ≤
        literalAlpha N ((fibIndex N)^6) := by
    filter_upwards [fibIndex_tendsto.eventually eventual_median_bounds,eventually_ge_atTop 1] with N h hN
    exact (h N (fibIndex_lower N hN) (fibIndex_upper N) _
      (Nat.one_le_pow 6 _ (fibIndex_pos N)) le_rfl).2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds he
    (Filter.Eventually.of_forall (fun N => (literalAlpha_bounds N _).2))

end LiteralGame
