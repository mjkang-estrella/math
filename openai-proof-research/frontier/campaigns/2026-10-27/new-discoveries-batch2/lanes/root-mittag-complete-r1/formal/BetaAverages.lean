import SourceAssembly

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace MittagModulus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The mixture with mass beta at one and the Beta(k+1,1) density otherwise. -/
noncomputable def betaAverage (β : ℝ) (k : ℕ) (f : ℝ → E) (x : ℝ) : E :=
  β • f x + ((1 - β) * (k + 1 : ℝ)) • ∫ u in (0 : ℝ)..1, u ^ k • f (x * u)

omit [CompleteSpace E] in
theorem betaAverage_continuous (β : ℝ) (k : ℕ) {f : ℝ → E}
    (hf : Continuous f) : Continuous (betaAverage β k f) := by
  have hi : Continuous (fun x : ℝ => ∫ u in (0 : ℝ)..1, u ^ k • f (x * u)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact (continuous_snd.pow k).smul (hf.comp (continuous_fst.mul continuous_snd))
  exact (hf.const_smul β).add (hi.const_smul _)

omit [CompleteSpace E] in
theorem betaAverage_add (β : ℝ) (k : ℕ) {f g : ℝ → E}
    (hf : Continuous f) (hg : Continuous g) :
    betaAverage β k (f + g) = betaAverage β k f + betaAverage β k g := by
  funext x
  have hfi : IntervalIntegrable (fun u : ℝ => u ^ k • f (x * u)) MeasureTheory.volume 0 1 :=
    ((continuous_id.pow k).smul (hf.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hgi : IntervalIntegrable (fun u : ℝ => u ^ k • g (x * u)) MeasureTheory.volume 0 1 :=
    ((continuous_id.pow k).smul (hg.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  simp only [betaAverage, Pi.add_apply, smul_add, intervalIntegral.integral_add hfi hgi]
  abel

omit [CompleteSpace E] in
theorem betaAverage_const_smul (β : ℝ) (k : ℕ) (c : ℝ) (f : ℝ → E) :
    betaAverage β k (fun x => c • f x) = fun x => c • betaAverage β k f x := by
  funext x
  simp only [betaAverage]
  simp_rw [smul_comm (n := c)]
  rw [intervalIntegral.integral_smul]
  simp only [smul_add, smul_smul, mul_comm]

theorem betaAverage_const (β : ℝ) (k : ℕ) (c : E) :
    betaAverage β k (fun _ => c) = fun _ => c := by
  funext x
  simp only [betaAverage, intervalIntegral.integral_smul_const, integral_pow]
  simp only [one_pow, zero_pow (by omega : k + 1 ≠ 0), sub_zero]
  rw [smul_smul, ← add_smul]
  have hk : (k + 1 : ℝ) ≠ 0 := by positivity
  have he : β + (1 - β) * (k + 1 : ℝ) * (1 / (k + 1 : ℝ)) = 1 := by field_simp; ring
  rw [he, one_smul]

/-- A finite iterated average. Each additional step uses one new Beta factor. -/
noncomputable def finiteBetaAverage (β : ℝ) : ℕ → (ℝ → E) → ℝ → E
  | 0, f => f
  | n + 1, f => betaAverage β n (finiteBetaAverage β n f)

omit [CompleteSpace E] in
theorem finiteBetaAverage_continuous (β : ℝ) (n : ℕ) {f : ℝ → E}
    (hf : Continuous f) : Continuous (finiteBetaAverage β n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact betaAverage_continuous β n ih

theorem finiteBetaAverage_const (β : ℝ) (n : ℕ) (c : E) :
    finiteBetaAverage β n (fun _ => c) = fun _ => c := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [finiteBetaAverage, ih, betaAverage_const]

/-- Every point sampled by the integral stays in the same nonnegative interval. -/
theorem mul_mem_nonnegative_interval {C x u : ℝ} (hx : x ∈ Set.Icc 0 C)
    (hu : u ∈ Set.Icc 0 1) : x * u ∈ Set.Icc 0 C := by
  constructor
  · exact mul_nonneg hx.1 hu.1
  · calc x * u ≤ x * 1 := mul_le_mul_of_nonneg_left hu.2 hx.1
         _ ≤ C := by simpa using hx.2

theorem betaAverage_nonneg {β C x : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (k : ℕ) {f : ℝ → ℝ} (hpos : ∀ y ∈ Set.Icc 0 C, 0 ≤ f y)
    (hx : x ∈ Set.Icc 0 C) : 0 ≤ betaAverage β k f x := by
  unfold betaAverage
  apply add_nonneg (smul_nonneg hβ (hpos x hx))
  apply smul_nonneg (mul_nonneg (by linarith) (by positivity))
  apply intervalIntegral.integral_nonneg zero_le_one
  intro u hu
  exact smul_nonneg (pow_nonneg hu.1 _) (hpos _ (mul_mem_nonnegative_interval hx hu))

theorem finiteBetaAverage_nonneg {β C : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (n : ℕ) {f : ℝ → ℝ} (hpos : ∀ y ∈ Set.Icc 0 C, 0 ≤ f y) :
    ∀ x ∈ Set.Icc 0 C, 0 ≤ finiteBetaAverage β n f x := by
  induction n with
  | zero => exact hpos
  | succ n ih => exact fun x hx => betaAverage_nonneg hβ hβ1 n ih hx

theorem betaAverage_rpow {β q x : ℝ} (hq : 0 ≤ q) (hx : 0 ≤ x) (k : ℕ) :
    betaAverage β k (fun y : ℝ => y ^ q) x =
      x ^ q * ((1 + β * q + (k : ℝ)) / (1 + q + (k : ℝ))) := by
  have hpow : (∫ u in (0 : ℝ)..1, u ^ k * (x * u) ^ q) =
      x ^ q * (1 / ((k : ℝ) + q + 1)) := by
    calc
      (∫ u in (0 : ℝ)..1, u ^ k * (x * u) ^ q) =
          ∫ u in (0 : ℝ)..1, x ^ q * u ^ ((k : ℝ) + q) := by
        apply intervalIntegral.integral_congr
        intro u hu
        change u ^ k * (x * u) ^ q = x ^ q * u ^ ((k : ℝ) + q)
        rw [Set.uIcc_of_le zero_le_one] at hu
        rw [Real.mul_rpow hx hu.1,
          Real.rpow_add_of_nonneg hu.1 (by positivity : 0 ≤ (k : ℝ)) hq,
          Real.rpow_natCast]
        ring
      _ = x ^ q * (1 / ((k : ℝ) + q + 1)) := by
        rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith [Nat.cast_nonneg (α := ℝ) k]))]
        rw [Real.one_rpow, Real.zero_rpow (by positivity : (k : ℝ) + q + 1 ≠ 0)]
        ring
  change β * x ^ q + ((1 - β) * (k + 1 : ℝ)) *
    (∫ u in (0 : ℝ)..1, u ^ k * (x * u) ^ q) = _
  rw [hpow]
  have hden : 1 + q + (k : ℝ) ≠ 0 := by positivity
  have hden' : (k : ℝ) + q + 1 ≠ 0 := by positivity
  field_simp
  ring

omit [CompleteSpace E] in
theorem betaAverage_congr_nonneg (β : ℝ) (k : ℕ) {f g : ℝ → E}
    (hfg : ∀ x : ℝ, 0 ≤ x → f x = g x) {x : ℝ} (hx : 0 ≤ x) :
    betaAverage β k f x = betaAverage β k g x := by
  unfold betaAverage
  rw [hfg x hx]
  congr 1
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le zero_le_one] at hu
  change u ^ k • f (x * u) = u ^ k • g (x * u)
  rw [hfg (x * u) (mul_nonneg hx hu.1)]

omit [CompleteSpace E] in
theorem finiteBetaAverage_const_smul (β : ℝ) (n : ℕ) (c : ℝ) (f : ℝ → E) :
    finiteBetaAverage β n (fun x => c • f x) =
      fun x => c • finiteBetaAverage β n f x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finiteBetaAverage, ih, betaAverage_const_smul]

theorem finiteBetaAverage_rpow {β q : ℝ} (hq : 0 ≤ q) (n : ℕ) {x : ℝ}
    (hx : 0 ≤ x) :
    finiteBetaAverage β n (fun y : ℝ => y ^ q) x =
      x ^ q * ∏ k ∈ Finset.range n,
        ((1 + β * q + (k : ℝ)) / (1 + q + (k : ℝ))) := by
  induction n generalizing x with
  | zero => simp [finiteBetaAverage]
  | succ n ih =>
    let c : ℝ := ∏ k ∈ Finset.range n,
      ((1 + β * q + (k : ℝ)) / (1 + q + (k : ℝ)))
    have he : betaAverage β n (finiteBetaAverage β n (fun y : ℝ => y ^ q)) x =
        betaAverage β n (fun y : ℝ => c • y ^ q) x := by
      apply betaAverage_congr_nonneg β n _ hx
      intro y hy
      rw [ih hy]
      change y ^ q * c = c * y ^ q
      ring
    change betaAverage β n (finiteBetaAverage β n (fun y : ℝ => y ^ q)) x = _
    rw [he, betaAverage_const_smul]
    change c * betaAverage β n (fun y : ℝ => y ^ q) x = _
    rw [betaAverage_rpow hq hx, Finset.prod_range_succ]
    dsimp [c]
    ring

theorem momentApprox_eq_finiteBetaAverage {β q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    momentApprox β q n = finiteBetaAverage β (n + 2) (fun y : ℝ => y ^ q)
      (((n : ℝ) + 1) ^ (1 - β)) := by
  rw [finiteBetaAverage_rpow hq (n + 2) (Real.rpow_nonneg (by positivity) _)]
  rw [← Real.rpow_mul (by positivity : 0 ≤ (n : ℝ) + 1)]
  rfl

omit [CompleteSpace E] in
theorem betaAverage_norm_le {β C M x : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (k : ℕ) {f : ℝ → E}
    (hbound : ∀ y ∈ Set.Icc 0 C, ‖f y‖ ≤ M) (hx : x ∈ Set.Icc 0 C) :
    ‖betaAverage β k f x‖ ≤ M := by
  have hc : 0 ≤ (1 - β) * (k + 1 : ℝ) := by positivity
  have hi : ‖∫ u in (0 : ℝ)..1, u ^ k • f (x * u)‖ ≤ M / (k + 1 : ℝ) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le (μ := MeasureTheory.volume) zero_le_one
      (MeasureTheory.ae_of_all _ (fun u hu => show ‖u ^ k • f (x * u)‖ ≤ u ^ k * M from by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hu.1.le _)]
        exact mul_le_mul_of_nonneg_left
          (hbound _ (mul_mem_nonnegative_interval hx ⟨hu.1.le, hu.2⟩)) (pow_nonneg hu.1.le _)))
      (((continuous_id.pow k).mul continuous_const).intervalIntegrable 0 1)
    rw [intervalIntegral.integral_mul_const, integral_pow] at h
    simp only [one_pow, zero_pow (by omega : k + 1 ≠ 0), sub_zero] at h
    convert h using 1
    ring
  calc
    ‖betaAverage β k f x‖ ≤ ‖β • f x‖ +
        ‖((1 - β) * (k + 1 : ℝ)) • ∫ u in (0 : ℝ)..1, u ^ k • f (x * u)‖ := norm_add_le _ _
    _ = β * ‖f x‖ + ((1 - β) * (k + 1 : ℝ)) *
        ‖∫ u in (0 : ℝ)..1, u ^ k • f (x * u)‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hβ, abs_of_nonneg hc]
    _ ≤ β * M + ((1 - β) * (k + 1 : ℝ)) * (M / (k + 1 : ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left (hbound x hx) hβ)
        (mul_le_mul_of_nonneg_left hi hc)
    _ = M := by
      have hk : (k + 1 : ℝ) ≠ 0 := by positivity
      field_simp
      ring

omit [CompleteSpace E] in
theorem finiteBetaAverage_norm_le {β C M : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (n : ℕ) {f : ℝ → E}
    (hbound : ∀ y ∈ Set.Icc 0 C, ‖f y‖ ≤ M) :
    ∀ x ∈ Set.Icc 0 C, ‖finiteBetaAverage β n f x‖ ≤ M := by
  induction n with
  | zero => exact hbound
  | succ n ih => exact fun x hx => betaAverage_norm_le hβ hβ1 n ih hx

theorem betaAverage_positiveMixedDifferences {β C x : ℝ} (hβ : 0 ≤ β)
    (hβ1 : β ≤ 1) (k : ℕ) {F : ℝ → ℝ → ℝ}
    (hcont : ∀ t : ℝ, Continuous (fun y => F y t))
    (hpos : ∀ y ∈ Set.Icc 0 C, PositiveMixedDifferences (F y))
    (hx : x ∈ Set.Icc 0 C) :
    PositiveMixedDifferences (fun t => betaAverage β k (fun y => F y t) x) := by
  have hi : PositiveMixedDifferences (fun t => ∫ u in (0 : ℝ)..1, u ^ k * F (x * u) t) := by
    apply PositiveMixedDifferences.intervalIntegral zero_le_one
    · intro t
      exact ((continuous_id.pow k).mul ((hcont t).comp
        (continuous_const.mul continuous_id))).continuousOn
    · intro u hu
      exact (hpos _ (mul_mem_nonnegative_interval hx hu)).const_mul (pow_nonneg hu.1 _)
  exact ((hpos x hx).const_mul hβ).add
    (hi.const_mul (mul_nonneg (by linarith) (by positivity)))

theorem finiteBetaAverage_positiveMixedDifferences {β C : ℝ} (hβ : 0 ≤ β)
    (hβ1 : β ≤ 1) (n : ℕ) {F : ℝ → ℝ → ℝ}
    (hcont : ∀ t : ℝ, Continuous (fun y => F y t))
    (hpos : ∀ y ∈ Set.Icc 0 C, PositiveMixedDifferences (F y)) :
    ∀ x ∈ Set.Icc 0 C,
      PositiveMixedDifferences (fun t => finiteBetaAverage β n (fun y => F y t) x) := by
  induction n with
  | zero => exact hpos
  | succ n ih =>
    intro x hx
    exact betaAverage_positiveMixedDifferences hβ hβ1 n
      (fun t => finiteBetaAverage_continuous β n (hcont t)) ih hx

omit [CompleteSpace E] in
theorem betaAverage_tendsto {β C M x : ℝ} (k : ℕ) {F : ℕ → ℝ → E} {f : ℝ → E}
    (hcont : ∀ N, Continuous (F N))
    (hbound : ∀ N, ∀ y ∈ Set.Icc 0 C, ‖F N y‖ ≤ M)
    (hlim : ∀ y ∈ Set.Icc 0 C,
      Filter.Tendsto (fun N => F N y) Filter.atTop (nhds (f y)))
    (hx : x ∈ Set.Icc 0 C) :
    Filter.Tendsto (fun N => betaAverage β k (F N) x) Filter.atTop
      (nhds (betaAverage β k f x)) := by
  have hi : Filter.Tendsto (fun N => ∫ u in (0 : ℝ)..1, u ^ k • F N (x * u))
      Filter.atTop (nhds (∫ u in (0 : ℝ)..1, u ^ k • f (x * u))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun u : ℝ => u ^ k * M)
    · exact Filter.Eventually.of_forall (fun N =>
        ((continuous_id.pow k).smul ((hcont N).comp
          (continuous_const.mul continuous_id))).aestronglyMeasurable)
    · apply Filter.Eventually.of_forall
      intro N
      apply MeasureTheory.ae_of_all
      intro u hu
      rw [Set.uIoc_of_le zero_le_one] at hu
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hu.1.le _)]
      exact mul_le_mul_of_nonneg_left
        (hbound N _ (mul_mem_nonnegative_interval hx ⟨hu.1.le, hu.2⟩))
        (pow_nonneg hu.1.le _)
    · exact ((continuous_id.pow k).mul continuous_const).intervalIntegrable _ _
    · apply MeasureTheory.ae_of_all
      intro u hu
      rw [Set.uIoc_of_le zero_le_one] at hu
      exact (hlim _ (mul_mem_nonnegative_interval hx ⟨hu.1.le, hu.2⟩)).const_smul _
  exact ((hlim x hx).const_smul β).add (hi.const_smul _)

omit [CompleteSpace E] in
theorem finiteBetaAverage_tendsto {β C M : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (n : ℕ) {F : ℕ → ℝ → E} {f : ℝ → E}
    (hcont : ∀ N, Continuous (F N))
    (hbound : ∀ N, ∀ y ∈ Set.Icc 0 C, ‖F N y‖ ≤ M)
    (hlim : ∀ y ∈ Set.Icc 0 C,
      Filter.Tendsto (fun N => F N y) Filter.atTop (nhds (f y))) :
    ∀ x ∈ Set.Icc 0 C,
      Filter.Tendsto (fun N => finiteBetaAverage β n (F N) x) Filter.atTop
        (nhds (finiteBetaAverage β n f x)) := by
  induction n with
  | zero => exact hlim
  | succ n ih =>
    intro x hx
    exact betaAverage_tendsto n
      (fun N => finiteBetaAverage_continuous β n (hcont N))
      (fun N => finiteBetaAverage_norm_le hβ hβ1 n (hbound N)) ih hx

theorem betaAverage_smul_const (β : ℝ) (k : ℕ) (f : ℝ → ℝ) (c : E) :
    betaAverage β k (fun y => f y • c) = fun x => betaAverage β k f x • c := by
  funext x
  simp only [betaAverage, smul_smul, smul_eq_mul,
    intervalIntegral.integral_smul_const, add_smul]

theorem finiteBetaAverage_smul_const (β : ℝ) (n : ℕ) (f : ℝ → ℝ) (c : E) :
    finiteBetaAverage β n (fun y => f y • c) =
      fun x => finiteBetaAverage β n f x • c := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [finiteBetaAverage, ih, betaAverage_smul_const]

omit [CompleteSpace E] in
theorem finiteBetaAverage_add (β : ℝ) (n : ℕ) {f g : ℝ → E}
    (hf : Continuous f) (hg : Continuous g) :
    finiteBetaAverage β n (f + g) =
      finiteBetaAverage β n f + finiteBetaAverage β n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [finiteBetaAverage, ih]
    exact betaAverage_add β n (finiteBetaAverage_continuous β n hf)
      (finiteBetaAverage_continuous β n hg)

theorem finiteBetaAverage_sum {ι : Type*} (β : ℝ) (n : ℕ) (s : Finset ι)
    {F : ι → ℝ → E} (hF : ∀ i ∈ s, Continuous (F i)) :
    finiteBetaAverage β n (fun x => ∑ i ∈ s, F i x) =
      fun x => ∑ i ∈ s, finiteBetaAverage β n (F i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using finiteBetaAverage_const β n (0 : E)
  | @insert i s his ih =>
    simp only [Finset.sum_insert his]
    have he : (fun x => F i x + ∑ j ∈ s, F j x) = F i + (fun x => ∑ j ∈ s, F j x) := rfl
    rw [he, finiteBetaAverage_add β n (hF i (by simp))
      (continuous_finsetSum s (fun j hj => hF j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))]
    rfl

end MittagModulus
