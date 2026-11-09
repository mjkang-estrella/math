import TwoSided333569
import Consistency333569
import Mathlib.MeasureTheory.Constructions.Cylinders

namespace MathDB333569
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem halfLaw_ae_zero (z : ℝ × ℝ) (hz : z ∈ interior) (a : Fin 2) :
    ∀ᵐ x ∂halfLaw z hz a, x 0 = a := by
  have h := halfLaw_zero z hz a
  have ha : ∀ᵐ b ∂(halfLaw z hz a).map (fun x => x 0), b = a := by
    rw [h]
    simp
  exact (ae_map_iff (μ := halfLaw z hz a) (f := fun x : ℕ → Fin 2 => x 0) (p := fun b : Fin 2 => b = a) (measurable_pi_apply 0).aemeasurable
    (measurableSet_eq_fun measurable_id measurable_const)).mp ha

/-- Weighted reversal of an arbitrary finite backward path. -/
theorem path_balance (z : ℝ × ℝ) (n : ℕ) (w : ℕ → Fin 2) :
    stationary z (w 0) * (∏ i : Fin n, trans z (w i.val) (w (i.val+1))) =
    stationary z (w n) * (∏ i : Fin n, trans z (w (i.val+1)) (w i.val)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    calc
      _ = (stationary z (w 0) * ∏ i : Fin n, trans z (w i.val) (w (i.val+1))) *
          trans z (w n) (w (n+1)) := by ring
      _ = (stationary z (w n) * trans z (w n) (w (n+1))) *
          (∏ i : Fin n, trans z (w (i.val+1)) (w i.val)) := by rw [ih]; ring
      _ = _ := by rw [detailed_balance]; ring

/-- Exact mixed window; both branches include the shared initial symbol. -/
theorem twoSidedLaw_window (z : ℝ × ℝ) (hz : z ∈ interior)
    (m n : ℕ) (p q : ℕ → Fin 2) (h0 : p 0 = q 0) :
    twoSidedLaw z hz {x | (∀ i ≤ n, x (i : ℤ) = p i) ∧
      (∀ i ≤ m, x (-(i : ℤ)) = q i)} =
    ENNReal.ofReal (stationary z (p 0)) *
      (∏ i : Fin n, ENNReal.ofReal (trans z (p i.val) (p (i.val+1)))) *
      (∏ i : Fin m, ENNReal.ofReal (trans z (q i.val) (q (i.val+1)))) := by
  classical
  let A : Set (ℕ → Fin 2) := {x | ∀ i ≤ n, x i = p i}
  let B : Set (ℕ → Fin 2) := {x | ∀ i ≤ m, x i = q i}
  have hs : MeasurableSet {x : ℤ → Fin 2 | (∀ i ≤ n, x (i : ℤ) = p i) ∧
      (∀ i ≤ m, x (-(i : ℤ)) = q i)} := by
    change MeasurableSet ({x : ℤ → Fin 2 | ∀ i ≤ n, x (i : ℤ) = p i} ∩
      {x | ∀ i ≤ m, x (-(i : ℤ)) = q i})
    apply MeasurableSet.inter <;> simp only [Set.ofPred_forall] <;>
      exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
        measurableSet_eq_fun (by fun_prop) measurable_const
  rw [twoSidedLaw_apply z hz _ hs]
  have hc (a : Fin 2) :
      ((halfLaw z hz a).prod (halfLaw z hz a))
        (glue ⁻¹' {x | (∀ i ≤ n, x (i : ℤ) = p i) ∧
          (∀ i ≤ m, x (-(i : ℤ)) = q i)}) =
        halfLaw z hz a A * halfLaw z hz a B := by
    rw [← Measure.prod_prod]
    apply measure_congr
    have ha : ∀ᵐ v ∂(halfLaw z hz a).prod (halfLaw z hz a), v.1 0 = a ∧ v.2 0 = a := by
      apply (Measure.ae_prod_iff_ae_ae (by
        exact (measurableSet_eq_fun (by fun_prop) measurable_const).inter
          (measurableSet_eq_fun (by fun_prop) measurable_const))).mpr
      filter_upwards [halfLaw_ae_zero z hz a] with x hx
      filter_upwards [halfLaw_ae_zero z hz a] with y hy
      exact ⟨hx,hy⟩
    filter_upwards [ha] with v hv
    apply propext
    change ((∀ i ≤ n, glue v (i : ℤ) = p i) ∧
      (∀ i ≤ m, glue v (-(i : ℤ)) = q i)) ↔ _
    have hg (i : ℕ) : glue v (-(i : ℤ)) = v.2 i := by
      cases i with
      | zero => simp [glue, hv.1, hv.2]
      | succ i =>
        have hn : ¬ (0 : ℤ) ≤ -((i+1 : ℕ) : ℤ) := by omega
        simp only [glue, hn, ↓reduceIte, Int.natAbs_neg, Int.natAbs_natCast]
    simp_rw [hg]
    simp only [glue, Int.natCast_nonneg, ↓reduceIte, Int.natAbs_natCast]
    rfl
  simp_rw [hc]
  simp only [mul_assoc]
  change (∑ a : Fin 2, _ * ( halfLaw z hz a {x | ∀ i ≤ n, x i = p i} *
    halfLaw z hz a {x | ∀ i ≤ m, x i = q i})) = _
  simp_rw [halfLaw_word, ← h0]
  rw [Finset.sum_eq_single (p 0)]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- The mixed-window formula with the negative path read in chronological order. -/
theorem twoSidedLaw_window_forward (z : ℝ × ℝ) (hz : z ∈ interior)
    (m n : ℕ) (v : ℤ → Fin 2) :
    twoSidedLaw z hz {x | (∀ i ≤ n, x (i : ℤ) = v (i : ℤ)) ∧
      (∀ i ≤ m, x (-(i : ℤ)) = v (-(i : ℤ)))} =
    ENNReal.ofReal (stationary z (v (-(m : ℤ))) *
      (∏ i : Fin m, trans z (v (-((i.val+1 : ℕ) : ℤ))) (v (-(i.val : ℤ)))) *
      (∏ i : Fin n, trans z (v (i.val : ℤ)) (v ((i.val+1 : ℕ) : ℤ)))) := by
  rw [twoSidedLaw_window z hz m n (fun i => v (i : ℤ)) (fun i => v (-(i : ℤ))) (by simp)]
  have hp (k : ℕ) (f : Fin k → ℝ) (hf : ∀ i, 0 ≤ f i) :
      (∏ i, ENNReal.ofReal (f i)) = ENNReal.ofReal (∏ i, f i) := by
    exact (ENNReal.ofReal_prod_of_nonneg (fun i _ => hf i)).symm
  rw [hp n _ (fun _ => (trans_pos hz _ _).le), hp m _ (fun _ => (trans_pos hz _ _).le)]
  rw [← ENNReal.ofReal_mul (stationary_pos hz _).le,
    ← ENNReal.ofReal_mul (mul_nonneg (stationary_pos hz _).le
      (Finset.prod_nonneg (fun _ _ => (trans_pos hz _ _).le)))]
  congr 1
  have h := path_balance z m (fun i => v (-(i : ℤ)))
  simp only [Nat.cast_zero, neg_zero] at h
  simp only [Nat.cast_zero] 
  calc
    _ = (stationary z (v 0) * ∏ i : Fin m,
      trans z (v (-(i.val : ℤ))) (v (-((i.val+1 : ℕ) : ℤ)))) *
      (∏ i : Fin n, trans z (v (i.val : ℤ)) (v ((i.val+1 : ℕ) : ℤ))) := by ring
    _ = _ := by rw [h]

/-- Flatten a mixed window into precisely the chronological source word. -/
theorem window_wordProb (z : ℝ × ℝ) (m n : ℕ) (v : ℤ → Fin 2) :
    wordProb z (m+n) (fun j => v (-(m : ℤ) + j.val)) =
      stationary z (v (-(m : ℤ))) *
      (∏ i : Fin m, trans z (v (-((i.val+1 : ℕ) : ℤ))) (v (-(i.val : ℤ)))) *
      (∏ i : Fin n, trans z (v (i.val : ℤ)) (v ((i.val+1 : ℕ) : ℤ))) := by
  unfold wordProb
  rw [Fin.prod_univ_add]
  simp only [Fin.val_zero, Nat.cast_zero, add_zero, Fin.val_castSucc, Fin.val_succ,
    Fin.val_castAdd, Fin.val_natAdd, Nat.cast_add, Nat.cast_one]
  have hneg : (∏ i : Fin m, trans z (v (-(m : ℤ) + i.val))
      (v (-(m : ℤ) + (i.val + 1)))) =
      ∏ i : Fin m, trans z (v (-((i.val+1 : ℕ) : ℤ))) (v (-(i.val : ℤ))) := by
    rw [← (Equiv.prod_comp Fin.revPerm (fun i : Fin m =>
      trans z (v (-(m : ℤ) + i.val)) (v (-(m : ℤ) + (i.val+1)))))]
    apply Finset.prod_congr rfl
    intro i _
    congr 2 <;> simp only [Fin.revPerm_apply, Fin.val_rev] <;> omega
  rw [hneg]
  have hpos : (∏ i : Fin n, trans z (v (-(m : ℤ) + (m + i.val)))
      (v (-(m : ℤ) + (m + i.val + 1)))) =
      ∏ i : Fin n, trans z (v (i.val : ℤ)) (v ((i.val+1 : ℕ) : ℤ)) := by
    apply Finset.prod_congr rfl
    intro i _
    congr 2 <;> push_cast <;> ring
  rw [hpos]
  simp only [Nat.cast_add, Nat.cast_one]
  ring

theorem twoSidedLaw_crossing_block (z : ℝ × ℝ) (hz : z ∈ interior)
    (m n : ℕ) (v : ℤ → Fin 2) :
    twoSidedLaw z hz {x | ∀ j : Fin (m+n+1), x (-(m : ℤ) + j.val) =
      v (-(m : ℤ) + j.val)} =
      ENNReal.ofReal (wordProb z (m+n) (fun j => v (-(m : ℤ) + j.val))) := by
  rw [window_wordProb]
  rw [← twoSidedLaw_window_forward z hz m n v]
  congr 1
  ext x
  constructor
  · intro h
    constructor
    · intro i hi
      have hj : m+i < m+n+1 := by omega
      have he : -(m : ℤ) + ((m+i : ℕ) : ℤ) = i := by omega
      simpa only [he] using h ⟨m+i,hj⟩
    · intro i hi
      have hj : m-i < m+n+1 := by omega
      have he : -(m : ℤ) + ((m-i : ℕ) : ℤ) = -(i : ℤ) := by omega
      simpa only [he] using h ⟨m-i,hj⟩
  · rintro ⟨hp,hq⟩ j
    by_cases hj : j.val ≤ m
    · have hi : m-j.val ≤ m := by omega
      have he : -((m-j.val : ℕ) : ℤ) = -(m : ℤ) + j.val := by omega
      simpa only [he] using hq (m-j.val) hi
    · have hi : j.val-m ≤ n := by omega
      have he : ((j.val-m : ℕ) : ℤ) = -(m : ℤ) + j.val := by omega
      simpa only [he] using hp (j.val-m) hi

/-- The source formula for every prescribed word in a window containing zero. -/
theorem twoSidedLaw_crossing_word (z : ℝ × ℝ) (hz : z ∈ interior)
    (m n : ℕ) (w : Fin (m+n+1) → Fin 2) :
    twoSidedLaw z hz {x | ∀ j : Fin (m+n+1), x (-(m : ℤ) + j.val) = w j} =
      ENNReal.ofReal (wordProb z (m+n) w) := by
  classical
  let v : ℤ → Fin 2 := fun i => if hi : (i+m).toNat < m+n+1 then w ⟨(i+m).toNat,hi⟩ else 0
  have hv (j : Fin (m+n+1)) : v (-(m : ℤ) + j.val) = w j := by
    have he : -(m : ℤ) + j.val + m = (j.val : ℤ) := by omega
    simp only [v, he, Int.toNat_natCast, dite_eq_left j.isLt]
  have h := twoSidedLaw_crossing_block z hz m n v
  simpa only [hv] using h

/-- Delete the first coordinate of a consecutive cylinder using stationarity of
its finite initial vector; this is a finite disjoint marginalization. -/
theorem block_drop_left (μ : Measure (ℤ → Fin 2)) (z : ℝ × ℝ)
    (hz : z ∈ interior) (k : ℤ) (n : ℕ)
    (h : ∀ v : Fin (n+2) → Fin 2,
      μ {x | ∀ j : Fin (n+2), x (k+j.val) = v j} = ENNReal.ofReal (wordProb z (n+1) v))
    (w : Fin (n+1) → Fin 2) :
    μ {x | ∀ j : Fin (n+1), x (k+1+j.val) = w j} = ENNReal.ofReal (wordProb z n w) := by
  classical
  let E : Set (ℤ → Fin 2) := {x | ∀ j : Fin (n+1), x (k+1+j.val) = w j}
  have hm (a : Fin 2) : MeasurableSet {x : ℤ → Fin 2 | x k = a} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have hs := sum_measure_preimage_singleton (μ := μ.restrict E) (f := fun x => x k)
    Finset.univ (fun a _ => hm a)
  simp only [Finset.coe_univ, Set.preimage_univ,
    Measure.restrict_apply_univ] at hs
  have he (a : Fin 2) : {x : ℤ → Fin 2 | x k = a} ∩ E =
      {x | ∀ j : Fin (n+2), x (k+j.val) = Fin.cons (α := fun _ : Fin (n+2) => Fin 2) a w j} := by
    ext x
    constructor
    · rintro ⟨ha,hw⟩ j
      refine Fin.cases ?_ (fun i => ?_) j
      · simpa using ha
      · simpa only [Fin.cons_succ, Fin.val_succ, Nat.cast_add, Nat.cast_one,
          show ∀ r : ℤ, k+(r+1) = k+1+r by intro r; ring] using hw i
    · intro hx
      constructor
      · simpa using hx 0
      · intro i
        simpa only [Fin.cons_succ, Fin.val_succ, Nat.cast_add, Nat.cast_one,
          show ∀ r : ℤ, k+(r+1) = k+1+r by intro r; ring] using hx i.succ
  change (∑ a : Fin 2, (μ.restrict E) {x | x k = a}) = μ E at hs
  simp_rw [Measure.restrict_apply (hm _), he, h] at hs
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => (wordProb_pos hz _ _).le),
    wordProb_left_consistent hz] at hs
  exact hs.symm

theorem block_drop_right (μ : Measure (ℤ → Fin 2)) (z : ℝ × ℝ)
    (hz : z ∈ interior) (k : ℤ) (n : ℕ)
    (h : ∀ v : Fin (n+2) → Fin 2,
      μ {x | ∀ j : Fin (n+2), x (k+j.val) = v j} = ENNReal.ofReal (wordProb z (n+1) v))
    (w : Fin (n+1) → Fin 2) :
    μ {x | ∀ j : Fin (n+1), x (k+j.val) = w j} = ENNReal.ofReal (wordProb z n w) := by
  classical
  let E : Set (ℤ → Fin 2) := {x | ∀ j : Fin (n+1), x (k+j.val) = w j}
  have hm (a : Fin 2) : MeasurableSet {x : ℤ → Fin 2 | x (k+(n+1)) = a} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have hs := sum_measure_preimage_singleton (μ := μ.restrict E) (f := fun x => x (k+(n+1)))
    Finset.univ (fun a _ => hm a)
  simp only [Finset.coe_univ, Set.preimage_univ, Measure.restrict_apply_univ] at hs
  have he (a : Fin 2) : {x : ℤ → Fin 2 | x (k+(n+1)) = a} ∩ E =
      {x | ∀ j : Fin (n+2), x (k+j.val) = Fin.snoc (α := fun _ : Fin (n+2) => Fin 2) w a j} := by
    ext x
    constructor
    · rintro ⟨ha,hw⟩ j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa using ha
      · simpa using hw i
    · intro hx
      constructor
      · simpa using hx (Fin.last (n+1))
      · intro i
        simpa using hx i.castSucc
  change (∑ a : Fin 2, (μ.restrict E) {x | x (k+(n+1)) = a}) = μ E at hs
  simp_rw [Measure.restrict_apply (hm _), he, h] at hs
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => (wordProb_pos hz _ _).le),
    wordProb_right_consistent] at hs
  exact hs.symm

/-- All nonnegative translates, obtained by repeated left marginalization. -/
theorem twoSidedLaw_nonneg_word (z : ℝ × ℝ) (hz : z ∈ interior)
    (k n : ℕ) (w : Fin (n+1) → Fin 2) :
    twoSidedLaw z hz {x | ∀ j : Fin (n+1), x ((k : ℤ)+j.val) = w j} =
      ENNReal.ofReal (wordProb z n w) := by
  induction k generalizing n with
  | zero =>
    have h := twoSidedLaw_crossing_word z hz 0 n
    rw [Nat.zero_add] at h
    simpa only [Nat.cast_zero, neg_zero] using h w
  | succ k ih =>
    have h := block_drop_left (twoSidedLaw z hz) z hz (k : ℤ) n (ih (n+1)) w
    simpa only [Nat.cast_add, Nat.cast_one] using h

/-- Any right truncation of a block with the source distribution has the source distribution. -/
theorem block_truncate_right (μ : Measure (ℤ → Fin 2)) (z : ℝ × ℝ)
    (hz : z ∈ interior) (k : ℤ) (n d : ℕ)
    (h : ∀ v : Fin (n+d+1) → Fin 2,
      μ {x | ∀ j : Fin (n+d+1), x (k+j.val) = v j} = ENNReal.ofReal (wordProb z (n+d) v))
    (w : Fin (n+1) → Fin 2) :
    μ {x | ∀ j : Fin (n+1), x (k+j.val) = w j} = ENNReal.ofReal (wordProb z n w) := by
  induction d with
  | zero => exact h w
  | succ d ih =>
    apply ih
    intro v
    apply block_drop_right μ z hz k (n+d) _ v
    have he : n+(d+1) = n+d+1 := by omega
    rw [he] at h
    exact h

/-- The source (6.1) cylinder formula at every integer translate. -/
theorem twoSidedLaw_word (z : ℝ × ℝ) (hz : z ∈ interior)
    (k : ℤ) (n : ℕ) (w : Fin (n+1) → Fin 2) :
    twoSidedLaw z hz {x | ∀ j : Fin (n+1), x (k+j.val) = w j} =
      ENNReal.ofReal (wordProb z n w) := by
  cases k with
  | ofNat k => exact twoSidedLaw_nonneg_word z hz k n w
  | negSucc a =>
    let m := a+1
    have hk : Int.negSucc a = -(m : ℤ) := by dsimp [m]; omega
    rw [hk]
    by_cases hn : m ≤ n
    · have h := twoSidedLaw_crossing_word z hz m (n-m)
      have he : m+(n-m) = n := by omega
      rw [he] at h
      exact h w
    · have hn' : n ≤ m := by omega
      apply block_truncate_right (twoSidedLaw z hz) z hz (-(m : ℤ)) n (m-n)
      have h := twoSidedLaw_crossing_word z hz m 0
      have he : n+(m-n) = m := by omega
      rw [he]
      simpa only [Nat.add_zero] using h

/-- Consecutive finite words determine a finite two-sided measure. -/
theorem measure_eq_of_blocks (μ ν : Measure (ℤ → Fin 2)) [IsFiniteMeasure μ]
    (hu : μ Set.univ = ν Set.univ)
    (h : ∀ (k : ℤ) (n : ℕ) (w : Fin (n+1) → Fin 2),
      μ {x | ∀ j : Fin (n+1), x (k+j.val) = w j} =
      ν {x | ∀ j : Fin (n+1), x (k+j.val) = w j}) : μ = ν := by
  classical
  have hb (k : ℤ) (n : ℕ) :
      μ.map (fun (x : ℤ → Fin 2) (j : Fin (n+1)) => x (k+j.val)) =
      ν.map (fun (x : ℤ → Fin 2) (j : Fin (n+1)) => x (k+j.val)) := by
    apply Measure.ext_of_singleton
    intro w
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton w),
      Measure.map_apply (by fun_prop) (measurableSet_singleton w)]
    simpa only [Set.preimage, Set.mem_singleton_iff, funext_iff] using h k n w
  apply ext_of_generate_finite (measurableCylinders (fun _ : ℤ => Fin 2))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders _ hu
  intro C hC
  obtain ⟨S,T,hT,rfl⟩ := (mem_measurableCylinders C).mp hC
  let N := S.sup Int.natAbs
  have hi (i : S) : i.val.natAbs ≤ N := Finset.le_sup (f := Int.natAbs) i.property
  let f : (Fin (2*N+1) → Fin 2) → (S → Fin 2) :=
    fun w i => w ⟨(i.val+N).toNat, by have := hi i; have := Int.natCast_natAbs i.val; omega⟩
  have hf : Measurable f := by fun_prop
  have he : (fun x : ℤ → Fin 2 => f (fun j => x (-(N : ℤ)+j.val))) =
      (fun x => S.restrict x) := by
    funext x i
    dsimp [f]
    congr 1
    have := hi i
    have := Int.natCast_natAbs i.val
    omega
  have hm := congrArg (fun ρ => ρ.map f) (hb (-(N : ℤ)) (2*N))
  rw [Measure.map_map hf (by fun_prop), Measure.map_map hf (by fun_prop)] at hm
  change μ.map (fun x => f (fun j => x (-(N : ℤ)+j.val))) =
    ν.map (fun x => f (fun j => x (-(N : ℤ)+j.val))) at hm
  rw [he] at hm
  have ht := congrArg (fun ρ : Measure (S → Fin 2) => ρ T) hm
  rw [Measure.map_apply (by fun_prop) hT, Measure.map_apply (by fun_prop) hT] at ht
  exact ht

/-- Actual shift invariance of the constructed countably additive law. -/
theorem twoSidedLaw_shift (z : ℝ × ℝ) (hz : z ∈ interior) (r : ℤ) :
    (twoSidedLaw z hz).map (fun x i => x (r+i)) = twoSidedLaw z hz := by
  apply measure_eq_of_blocks
  · simp
  · intro k n w
    have hs : MeasurableSet {x : ℤ → Fin 2 | ∀ j : Fin (n+1), x (k+j.val) = w j} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun j => measurableSet_eq_fun (by fun_prop) measurable_const
    rw [Measure.map_apply (by fun_prop) hs]
    change twoSidedLaw z hz {x | ∀ j : Fin (n+1), x (r+(k+j.val)) = w j} = _
    simp only [← add_assoc]
    rw [twoSidedLaw_word, twoSidedLaw_word]

/-- Every finite selected-coordinate marginal of the actual law is the source
finite distribution, at every integer translate. -/
theorem twoSidedLaw_marginal (z : ℝ × ℝ) (hz : z ∈ interior) (k : ℤ) (n : ℕ)
    (S : Finset (Fin (n+1))) (a : S → Fin 2) :
    twoSidedLaw z hz {x | ∀ i : S, x (k+i.val.val) = a i} =
      ENNReal.ofReal (marginal z n S a) := by
  classical
  let μ := twoSidedLaw z hz
  let E : Set (ℤ → Fin 2) := {x | ∀ i : S, x (k+i.val.val) = a i}
  let f : (ℤ → Fin 2) → (Fin (n+1) → Fin 2) := fun x j => x (k+j.val)
  have hm (w : Fin (n+1) → Fin 2) : MeasurableSet (f ⁻¹' {w}) :=
    (measurableSet_singleton w).preimage (by fun_prop)
  have hs := sum_measure_preimage_singleton (μ := μ.restrict E) (f := f)
    Finset.univ (fun w _ => hm w)
  simp only [Finset.coe_univ, Set.preimage_univ, Measure.restrict_apply_univ] at hs
  have he (w : Fin (n+1) → Fin 2) : (f ⁻¹' {w}) ∩ E =
      if ∀ i : S, w i.val = a i then f ⁻¹' {w} else ∅ := by
    split_ifs with hw
    · ext x
      constructor
      · exact fun h => h.1
      · intro hx
        refine ⟨hx, fun i => ?_⟩
        change f x i.val = a i
        rw [show f x = w from hx]
        exact hw i
    · apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx,he⟩
      apply hw
      intro i
      change f x = w at hx
      rw [← hx]
      exact he i
  have hw (w : Fin (n+1) → Fin 2) : μ (f ⁻¹' {w}) = ENNReal.ofReal (wordProb z n w) := by
    have h := twoSidedLaw_word z hz k n w
    simpa only [Set.preimage, Set.mem_singleton_iff, funext_iff] using h
  simp_rw [Measure.restrict_apply (hm _), he] at hs
  have hh (w : Fin (n+1) → Fin 2) : μ (if ∀ i : S, w i.val = a i then f ⁻¹' {w} else ∅) =
      ENNReal.ofReal (if ∀ i : S, w i.val = a i then wordProb z n w else 0) := by
    split_ifs <;> simp [hw]
  simp_rw [hh] at hs
  rw [← ENNReal.ofReal_sum_of_nonneg] at hs
  · exact hs.symm
  · intro w _
    split_ifs
    · exact (wordProb_pos hz n w).le
    · exact le_rfl

/-- A specified finite past and the next symbol factor by the actual source
transition probability. No Markov assumption is added. -/
theorem twoSidedLaw_prefix_next (z : ℝ × ℝ) (hz : z ∈ interior) (k : ℤ) (n : ℕ)
    (w : Fin (n+1) → Fin 2) (b : Fin 2) :
    twoSidedLaw z hz {x | (∀ j : Fin (n+1), x (k+j.val) = w j) ∧ x (k+(n+1)) = b} =
      twoSidedLaw z hz {x | ∀ j : Fin (n+1), x (k+j.val) = w j} *
        ENNReal.ofReal (trans z (w (Fin.last n)) b) := by
  have he : {x : ℤ → Fin 2 | (∀ j : Fin (n+1), x (k+j.val) = w j) ∧ x (k+(n+1)) = b} =
      {x | ∀ j : Fin (n+2), x (k+j.val) = Fin.snoc (α := fun _ : Fin (n+2) => Fin 2) w b j} := by
    ext x
    constructor
    · rintro ⟨hw,hb⟩ j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa using hb
      · simpa using hw i
    · intro h
      constructor
      · intro i; simpa using h i.castSucc
      · simpa using h (Fin.last (n+1))
  rw [he, twoSidedLaw_word, twoSidedLaw_word, wordProb_snoc,
    ENNReal.ofReal_mul (wordProb_pos hz n w).le]

/-- Shannon entropy of joins of rank-zero coordinate atoms under an actual law.
The empty join is included through its singleton assignment space. -/
def rankZeroSampleEntropy (μ : Measure (ℤ → Fin 2)) (k : ℤ) (n : ℕ)
    (S : Finset (Fin (n+1))) : ℝ :=
  - ∑ a : S → Fin 2,
    (μ {x | ∀ i : S, x (k+i.val.val) = a i}).toReal *
      Real.log ((μ {x | ∀ i : S, x (k+i.val.val) = a i}).toReal)

/-- Literal finite uniform-subset intricacy for the rank-zero partition. -/
def rankZeroFiniteIntricacy (μ : Measure (ℤ → Fin 2)) (k : ℤ) (n : ℕ) : ℝ := by
  classical
  exact (2 * (∑ S : Finset (Fin (n+1)), rankZeroSampleEntropy μ k n S) / (2:ℝ)^(n+1)
    - rankZeroSampleEntropy μ k n Finset.univ) / (n+1:ℝ)

theorem rankZeroSampleEntropy_eq (z : ℝ × ℝ) (hz : z ∈ interior) (k : ℤ) (n : ℕ)
    (S : Finset (Fin (n+1))) :
    rankZeroSampleEntropy (twoSidedLaw z hz) k n S = sampleEntropy z n S := by
  unfold rankZeroSampleEntropy sampleEntropy
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [twoSidedLaw_marginal, ENNReal.toReal_ofReal (marginal_nonneg hz n S a)]

theorem rankZeroFiniteIntricacy_eq (z : ℝ × ℝ) (hz : z ∈ interior) (k : ℤ) (n : ℕ) :
    rankZeroFiniteIntricacy (twoSidedLaw z hz) k n = finiteIntricacy z n := by
  unfold rankZeroFiniteIntricacy finiteIntricacy
  simp_rw [rankZeroSampleEntropy_eq z hz]

end
end MathDB333569
