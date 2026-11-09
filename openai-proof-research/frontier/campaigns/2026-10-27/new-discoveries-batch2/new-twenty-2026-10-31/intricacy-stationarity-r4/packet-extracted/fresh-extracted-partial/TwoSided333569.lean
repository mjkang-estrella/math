import Cylinders333569
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.OpenPos

namespace MathDB333569
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

def rowPMF (z : ℝ × ℝ) (hz : z ∈ interior) (a : Fin 2) : PMF (Fin 2) :=
  PMF.ofFintype (fun b => ENNReal.ofReal (trans z a b)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ => (trans_pos hz a b).le), trans_sum]
    simp)

def historyKernel (z : ℝ × ℝ) (hz : z ∈ interior) (n : ℕ) :
    Kernel (∀ _i : Finset.Iic n, Fin 2) (Fin 2) :=
  Kernel.ofFunOfCountable (fun w => (rowPMF z hz (w ⟨n, by simp⟩)).toMeasure)

instance historyKernel_markov (z : ℝ × ℝ) (hz : z ∈ interior) (n : ℕ) :
    IsMarkovKernel (historyKernel z hz n) := ⟨fun _ => by
  change IsProbabilityMeasure (PMF.toMeasure _)
  infer_instance⟩

def halfLaw (z : ℝ × ℝ) (hz : z ∈ interior) (a : Fin 2) : Measure (ℕ → Fin 2) :=
  Kernel.traj (historyKernel z hz) 0 (fun _ => a)

instance halfLaw_probability (z : ℝ × ℝ) (hz : z ∈ interior) (a : Fin 2) :
    IsProbabilityMeasure (halfLaw z hz a) := by
  unfold halfLaw
  infer_instance

/-- Glue independent forward/backward chains conditionally on the symbol at zero.
The negative branch uses `natAbs`; zero is supplied by the forward branch. -/
def glue (w : (ℕ → Fin 2) × (ℕ → Fin 2)) (i : ℤ) : Fin 2 :=
  if 0 ≤ i then w.1 i.natAbs else w.2 i.natAbs

theorem measurable_glue : Measurable glue := by
  apply Measurable.of_eval
  intro i
  unfold glue
  split_ifs <;> fun_prop

def conditionalTwoSided (z : ℝ × ℝ) (hz : z ∈ interior) (a : Fin 2) :
    Measure (ℤ → Fin 2) :=
  ((halfLaw z hz a).prod (halfLaw z hz a)).map glue

instance conditionalTwoSided_probability (z : ℝ × ℝ) (hz : z ∈ interior) (a : Fin 2) :
    IsProbabilityMeasure (conditionalTwoSided z hz a) := by
  unfold conditionalTwoSided
  infer_instance

/-- Actual countably additive probability measure on the two-sided source space.
Stationarity and cylinder identification are separate proof obligations. -/
def twoSidedLaw (z : ℝ × ℝ) (hz : z ∈ interior) : Measure (ℤ → Fin 2) :=
  ∑ a : Fin 2, ENNReal.ofReal (stationary z a) • conditionalTwoSided z hz a

instance twoSidedLaw_probability (z : ℝ × ℝ) (hz : z ∈ interior) :
    IsProbabilityMeasure (twoSidedLaw z hz) := by
  constructor
  simp only [twoSidedLaw, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => (stationary_pos hz a).le), stationary_sum hz]
  simp

/-- Every finite trajectory projection is the existing library's iterated kernel. -/
theorem halfLaw_prefix (z : ℝ × ℝ) (hz : z ∈ interior) (a : Fin 2) (n : ℕ) :
    (halfLaw z hz a).map (Preorder.frestrictLe n) =
      Kernel.partialTraj (X := fun _ => Fin 2) (historyKernel z hz) 0 n (fun _ => a) := by
  exact Kernel.traj_map_frestrictLe_apply (X := fun _ => Fin 2) _ _ _

theorem halfLaw_one (z : ℝ × ℝ) (hz : z ∈ interior) (a : Fin 2) :
    (halfLaw z hz a).map (fun w => w 1) = (rowPMF z hz a).toMeasure := by
  have h := congrArg (fun k : Kernel (∀ _i : Finset.Iic 0, Fin 2) (Fin 2) =>
      k (fun _ => a)) (Kernel.map_traj_succ_self (X := fun _ => Fin 2) (κ := historyKernel z hz) (a := 0))
  rw [Kernel.map_apply _ (by fun_prop)] at h
  simpa [halfLaw, historyKernel, Kernel.ofFunOfCountable] using h

theorem halfLaw_zero (z : ℝ × ℝ) (hz : z ∈ interior) (a : Fin 2) :
    (halfLaw z hz a).map (fun w => w 0) = Measure.dirac a := by
  have he : (fun w : ℕ → Fin 2 => w 0) =
      (fun w : (∀ _i : Finset.Iic 0, Fin 2) => w ⟨0, by simp⟩) ∘
        Preorder.frestrictLe 0 := rfl
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop), halfLaw_prefix]
  simp [Kernel.partialTraj_self, Kernel.id_apply]

/-- Reversibility is needed when reading the negative-time branch forwards. -/
theorem detailed_balance (z : ℝ × ℝ) (a b : Fin 2) :
    stationary z a * trans z a b = stationary z b * trans z b a := by
  fin_cases a <;> fin_cases b <;> simp [stationary, trans] <;> ring

/-- Cylinder evaluation for any finite constraints, expressed by conditional
forward/backward trajectory probabilities. No stationarity is assumed here. -/
theorem twoSidedLaw_apply (z : ℝ × ℝ) (hz : z ∈ interior)
    (s : Set (ℤ → Fin 2)) (hs : MeasurableSet s) :
    twoSidedLaw z hz s = ∑ a : Fin 2, ENNReal.ofReal (stationary z a) *
      ((halfLaw z hz a).prod (halfLaw z hz a)) (glue ⁻¹' s) := by
  simp only [twoSidedLaw, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul, conditionalTwoSided, Measure.map_apply measurable_glue hs]

theorem halfLaw_one_cylinder (z : ℝ × ℝ) (hz : z ∈ interior) (a b : Fin 2) :
    halfLaw z hz a {w | w 1 = b} = ENNReal.ofReal (trans z a b) := by
  have h := congrArg (fun μ : Measure (Fin 2) => μ {b}) (halfLaw_one z hz a)
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton b),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b)] at h
  exact h

theorem conditional_nonneg_cylinder (z : ℝ × ℝ) (hz : z ∈ interior)
    (a b : Fin 2) (n : ℕ) :
    conditionalTwoSided z hz a {x | x (n : ℤ) = b} =
      halfLaw z hz a {w | w n = b} := by
  rw [conditionalTwoSided, Measure.map_apply measurable_glue (measurableSet_eq_fun (by fun_prop) measurable_const)]
  have he : glue ⁻¹' {x | x (n : ℤ) = b} =
      {w : ℕ → Fin 2 | w n = b} ×ˢ (Set.univ : Set (ℕ → Fin 2)) := by
    ext w
    simp [glue]
  rw [he, Measure.prod_prod, measure_univ, mul_one]

theorem twoSidedLaw_zero_cylinder (z : ℝ × ℝ) (hz : z ∈ interior) (b : Fin 2) :
    twoSidedLaw z hz {x | x 0 = b} = ENNReal.ofReal (stationary z b) := by
  have hc (a : Fin 2) : conditionalTwoSided z hz a {x | x 0 = b} =
      if a = b then 1 else 0 := by
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by rfl, conditional_nonneg_cylinder]
    have h := congrArg (fun μ : Measure (Fin 2) => μ {b}) (halfLaw_zero z hz a)
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton b)] at h
    change halfLaw z hz a {w | w 0 = b} = Measure.dirac a {b} at h
    simpa [Measure.dirac_apply' a (measurableSet_singleton b), Pi.single_apply, eq_comm] using h
  rw [twoSidedLaw, Measure.finsetSum_apply]
  simp_rw [Measure.smul_apply, smul_eq_mul, hc]
  fin_cases b <;> norm_num [Fin.sum_univ_two]

/-- A genuine selected-time cylinder evaluation across the origin. -/
theorem twoSidedLaw_neighbors (z : ℝ × ℝ) (hz : z ∈ interior) (b c : Fin 2) :
    twoSidedLaw z hz {x | x 1 = b ∧ x (-1) = c} =
      ∑ a : Fin 2, ENNReal.ofReal (stationary z a * trans z a b * trans z a c) := by
  rw [twoSidedLaw_apply z hz {x | x 1 = b ∧ x (-1) = c}
    (show MeasurableSet ({x : ℤ → Fin 2 | x 1 = b} ∩ {x | x (-1) = c}) from
      (measurableSet_eq_fun (by fun_prop) measurable_const).inter
        (measurableSet_eq_fun (by fun_prop) measurable_const))]
  apply Finset.sum_congr rfl
  intro a _
  have he : glue ⁻¹' {x | x 1 = b ∧ x (-1) = c} =
      {w : ℕ → Fin 2 | w 1 = b} ×ˢ {w : ℕ → Fin 2 | w 1 = c} := by
    ext w
    simp [glue]
  rw [he, Measure.prod_prod, halfLaw_one_cylinder, halfLaw_one_cylinder,
    ENNReal.ofReal_mul (mul_nonneg (stationary_pos hz a).le (trans_pos hz a b).le),
    ENNReal.ofReal_mul (stationary_pos hz a).le]
  exact (mul_assoc _ _ _).symm

/-- Finite cylinder evaluation for arbitrary positive and negative coordinates,
reduced to finite iterated kernels. The bound N is just a containing window. -/
theorem twoSidedLaw_finite_cylinder (z : ℝ × ℝ) (hz : z ∈ interior)
    (S : Finset ℤ) (a : S → Fin 2) (N : ℕ)
    (hN : ∀ i : S, i.val.natAbs ≤ N) :
    twoSidedLaw z hz {x | ∀ i : S, x i.val = a i} =
      ∑ b : Fin 2, ENNReal.ofReal (stationary z b) *
        ((Kernel.partialTraj (X := fun _ => Fin 2) (historyKernel z hz) 0 N (fun _ => b)).prod
          (Kernel.partialTraj (X := fun _ => Fin 2) (historyKernel z hz) 0 N (fun _ => b)))
        {w | ∀ i : S, (if 0 ≤ i.val then w.1 ⟨i.val.natAbs, Finset.mem_Iic.mpr (hN i)⟩
          else w.2 ⟨i.val.natAbs, Finset.mem_Iic.mpr (hN i)⟩) = a i} := by
  have hs : MeasurableSet {x : ℤ → Fin 2 | ∀ i : S, x i.val = a i} :=
    by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i => measurableSet_eq_fun (measurable_pi_apply i.val) measurable_const
  rw [twoSidedLaw_apply z hz _ hs]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  let E : Set ((Finset.Iic N → Fin 2) × (Finset.Iic N → Fin 2)) :=
    {w | ∀ i : S, (if 0 ≤ i.val then w.1 ⟨i.val.natAbs, Finset.mem_Iic.mpr (hN i)⟩
      else w.2 ⟨i.val.natAbs, Finset.mem_Iic.mpr (hN i)⟩) = a i}
  have hE : MeasurableSet E := by
    dsimp [E]
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    split_ifs <;> exact measurableSet_eq_fun (by fun_prop) measurable_const
  have hm := Measure.map_prod_map (halfLaw z hz b) (halfLaw z hz b)
    (Preorder.measurable_frestrictLe N) (Preorder.measurable_frestrictLe N)
  simp only [halfLaw_prefix] at hm
  rw [hm, Measure.map_apply (by fun_prop) hE]
  rfl

/-- The gap-two source transition formula, now for an actual two-sided cylinder. -/
theorem twoSidedLaw_gap_two {l t : ℝ} (hl : 0 < l) (hl1 : l < 1)
    (ht : -1 < t) (ht1 : t < 1) (b c : Fin 2) :
    twoSidedLaw (chart l t) (chart_mem_interior hl hl1 ht ht1)
      {x | x (-1) = c ∧ x 1 = b} =
        ENNReal.ofReal (pi t c * kernel (l^2) t c b) := by
  have hz := chart_mem_interior hl hl1 ht ht1
  have he : {x : ℤ → Fin 2 | x (-1) = c ∧ x 1 = b} =
      {x | x 1 = b ∧ x (-1) = c} := by ext x; exact and_comm
  rw [he, twoSidedLaw_neighbors]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ =>
    mul_nonneg (mul_nonneg (stationary_pos hz a).le (trans_pos hz a b).le)
      (trans_pos hz a c).le)]
  congr 1
  calc
    (∑ a : Fin 2, stationary (chart l t) a * trans (chart l t) a b *
      trans (chart l t) a c) =
      ∑ a : Fin 2, stationary (chart l t) c * trans (chart l t) c a *
        trans (chart l t) a b := by
          apply Finset.sum_congr rfl
          intro a _
          have hd := detailed_balance (chart l t) a c
          calc
            _ = (stationary (chart l t) a * trans (chart l t) a c) * trans (chart l t) a b := by ring
            _ = _ := by rw [hd]
    _ = pi t c * kernel (l^2) t c b := by
      simp_rw [chart_trans, chart_stationary (ne_of_lt hl1), mul_assoc]
      rw [← Finset.mul_sum, kernel_comp, pow_two]

/-- Exact one-step Markov factorization against an entire specified past prefix.
This is a proved cylinder identity, not a Markov hypothesis. -/
theorem halfLaw_prefix_next (z : ℝ × ℝ) (hz : z ∈ interior) (a : Fin 2)
    (n : ℕ) (w : Finset.Iic n → Fin 2) (b : Fin 2) :
    halfLaw z hz a {x | Preorder.frestrictLe n x = w ∧ x (n+1) = b} =
      halfLaw z hz a {x | Preorder.frestrictLe n x = w} *
        ENNReal.ofReal (trans z (w ⟨n, by simp⟩) b) := by
  have h := Kernel.partialTraj_compProd_eq_map_traj
    (X := fun _ => Fin 2) (κ := historyKernel z hz) (a := 0) (b := n)
    (x₀ := fun _ => a) (Nat.zero_le n)
  have hh := congrArg (fun μ => μ (({w} : Set (Finset.Iic n → Fin 2)) ×ˢ {b})) h
  rw [Measure.compProd_apply_prod (measurableSet_singleton w) (measurableSet_singleton b),
    lintegral_singleton, Measure.map_apply (by fun_prop)
      ((measurableSet_singleton w).prod (measurableSet_singleton b))] at hh
  have hr : historyKernel z hz n w {b} = ENNReal.ofReal (trans z (w ⟨n, by simp⟩) b) :=
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b)
  rw [hr] at hh
  have hp := congrArg (fun μ : Measure (Finset.Iic n → Fin 2) => μ {w})
    (halfLaw_prefix z hz a n)
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton w)] at hp
  change halfLaw z hz a {x | Preorder.frestrictLe n x = w} = _ at hp
  rw [← hp] at hh
  change ENNReal.ofReal (trans z (w ⟨n, by simp⟩) b) *
    halfLaw z hz a {x | Preorder.frestrictLe n x = w} =
    halfLaw z hz a {x | Preorder.frestrictLe n x = w ∧ x (n+1) = b} at hh
  exact hh.symm.trans (mul_comm _ _)

/-- Explicit finite forward cylinder product for the constructed infinite law. -/
theorem halfLaw_word (z : ℝ × ℝ) (hz : z ∈ interior) (a : Fin 2)
    (n : ℕ) (w : ℕ → Fin 2) :
    halfLaw z hz a {x | ∀ i ≤ n, x i = w i} =
      if w 0 = a then ∏ i : Fin n, ENNReal.ofReal (trans z (w i.val) (w (i.val+1)))
      else 0 := by
  have he (k : ℕ) : {x : ℕ → Fin 2 | Preorder.frestrictLe k x = Preorder.frestrictLe k w} =
      {x | ∀ i ≤ k, x i = w i} := by
    ext x
    constructor
    · intro h i hi
      exact congrFun h ⟨i, Finset.mem_Iic.mpr hi⟩
    · intro h
      funext i
      exact h i.val (Finset.mem_Iic.mp i.property)
  induction n with
  | zero =>
    have h := congrArg (fun μ : Measure (Fin 2) => μ {w 0}) (halfLaw_zero z hz a)
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at h
    have he0 : {x : ℕ → Fin 2 | ∀ i ≤ 0, x i = w i} = {x | x 0 = w 0} := by
      ext x; simp
    rw [he0]
    change halfLaw z hz a {x | x 0 = w 0} = Measure.dirac a {w 0} at h
    simpa [Measure.dirac_apply' a (measurableSet_singleton _), Pi.single_apply, eq_comm] using h
  | succ n ih =>
    have h := halfLaw_prefix_next z hz a n (Preorder.frestrictLe n w) (w (n+1))
    rw [he] at h
    have hs : {x : ℕ → Fin 2 | Preorder.frestrictLe n x = Preorder.frestrictLe n w ∧ x (n+1) = w (n+1)} =
        {x | ∀ i ≤ n+1, x i = w i} := by
      ext x
      constructor
      · rintro ⟨h, hn⟩ i hi
        by_cases hin : i ≤ n
        · exact congrFun h ⟨i, Finset.mem_Iic.mpr hin⟩
        · have hi' : i = n+1 := by omega
          simpa [hi'] using hn
      · intro h
        constructor
        · funext i; exact h i.val (by have := Finset.mem_Iic.mp i.property; omega)
        · exact h _ le_rfl
    rw [hs, ih] at h
    rw [h, Fin.prod_univ_castSucc]
    split_ifs <;> simp_all

/-- Every finite two-sided cylinder has positive mass under the constructed law. -/
theorem twoSidedLaw_cylinder_pos (z : ℝ × ℝ) (hz : z ∈ interior)
    (S : Finset ℤ) (v : ℤ → Fin 2) :
    0 < twoSidedLaw z hz {x | ∀ i ∈ S, x i = v i} := by
  classical
  let N := S.sup Int.natAbs
  let A : Set (ℕ → Fin 2) := {x | ∀ i ≤ N, x i = v (i : ℤ)}
  let B : Set (ℕ → Fin 2) := {x | ∀ i ≤ N, x i = v (-(i : ℤ))}
  have hA : 0 < halfLaw z hz (v 0) A := by
    rw [show A = {x | ∀ i ≤ N, x i = (fun j : ℕ => v (j : ℤ)) i} from rfl, halfLaw_word]
    simp only [Nat.cast_zero]
    apply bot_lt_iff_ne_bot.mpr
    exact Finset.prod_ne_zero_iff.mpr fun i _ => ne_of_gt (ENNReal.ofReal_pos.mpr (trans_pos hz _ _))
  have hB : 0 < halfLaw z hz (v 0) B := by
    rw [show B = {x | ∀ i ≤ N, x i = (fun j : ℕ => v (-(j : ℤ))) i} from rfl, halfLaw_word]
    simp only [Nat.cast_zero, neg_zero]
    apply bot_lt_iff_ne_bot.mpr
    exact Finset.prod_ne_zero_iff.mpr fun i _ => ne_of_gt (ENNReal.ofReal_pos.mpr (trans_pos hz _ _))
  have hsub : A ×ˢ B ⊆ glue ⁻¹' {x | ∀ i ∈ S, x i = v i} := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩ i hi
    have hni : i.natAbs ≤ N := Finset.le_sup (f := Int.natAbs) hi
    dsimp [glue]
    split_ifs with hsign
    · simpa only [Int.natCast_natAbs, abs_of_nonneg hsign] using hx i.natAbs hni
    · simpa only [Int.natCast_natAbs, abs_of_neg (lt_of_not_ge hsign), neg_neg] using hy i.natAbs hni
  have hc : 0 < conditionalTwoSided z hz (v 0) {x | ∀ i ∈ S, x i = v i} := by
    rw [conditionalTwoSided, Measure.map_apply measurable_glue
      (by simp only [Set.ofPred_forall]; exact MeasurableSet.iInter fun i =>
        MeasurableSet.iInter fun _ => measurableSet_eq_fun (measurable_pi_apply i) measurable_const)]
    exact lt_of_lt_of_le (by rw [Measure.prod_prod]; exact bot_lt_iff_ne_bot.mpr (mul_ne_zero (ne_of_gt hA) (ne_of_gt hB))) (measure_mono hsub)
  have hle : ENNReal.ofReal (stationary z (v 0)) *
      conditionalTwoSided z hz (v 0) {x | ∀ i ∈ S, x i = v i} ≤
      twoSidedLaw z hz {x | ∀ i ∈ S, x i = v i} := by
    rw [twoSidedLaw, Measure.finsetSum_apply]
    simp_rw [Measure.smul_apply, smul_eq_mul]
    exact Finset.single_le_sum
      (f := fun b : Fin 2 => ENNReal.ofReal (stationary z b) *
        conditionalTwoSided z hz b {x | ∀ i ∈ S, x i = v i})
      (fun _ _ => bot_le) (Finset.mem_univ (v 0))
  exact lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr (mul_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr (stationary_pos hz _))) (ne_of_gt hc))) hle

/-- Full topological support, on the actual two-sided product space. -/
instance twoSidedLaw_fullSupport (z : ℝ × ℝ) (hz : z ∈ interior) :
    (twoSidedLaw z hz).IsOpenPosMeasure := by
  constructor
  intro U hU hne
  obtain ⟨v,hv⟩ := hne
  obtain ⟨S,u,hu,hsub⟩ := isOpen_pi_iff.mp hU v hv
  have hc := twoSidedLaw_cylinder_pos z hz S v
  have hs : {x : ℤ → Fin 2 | ∀ i ∈ S, x i = v i} ⊆ U := by
    intro x hx
    apply hsub
    intro i hi
    rw [hx i hi]
    exact (hu i hi).2
  exact ne_of_gt (lt_of_lt_of_le hc (measure_mono hs))

end
end MathDB333569
