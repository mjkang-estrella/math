import SourceParameter333569
import Mathlib.MeasureTheory.Measure.Portmanteau

namespace MathDB333569
noncomputable section
open MeasureTheory Set Filter

abbrev ShiftSpace := ℤ → Fin 2

def OneStepMarkovLaw (μ : ProbabilityMeasure ShiftSpace) : Prop :=
  ∃ (z : ℝ × ℝ) (p : Fin 2 → ℝ),
    (0 ≤ z.1 ∧ z.1 ≤ 1 ∧ 0 ≤ z.2 ∧ z.2 ≤ 1) ∧
    (∀ a, 0 ≤ p a) ∧ (∑ a, p a = 1) ∧
    (∀ b, ∑ a, p a * trans z a b = p b) ∧
    ∀ (k : ℤ) (n : ℕ) (w : Fin (n+1) → Fin 2),
      (μ : Measure ShiftSpace) {x | ∀ j : Fin (n+1), x (k+j.val) = w j} =
        ENNReal.ofReal (p (w 0) * ∏ j : Fin n, trans z (w j.castSucc) (w j.succ))

def lawMass (μ : ProbabilityMeasure ShiftSpace) (E : Set ShiftSpace) : ℝ := (μ E : ℝ)
def stateCylinder (a : Fin 2) : Set ShiftSpace := {x | x 0 = a}
def diagonalCylinder (a : Fin 2) : Set ShiftSpace := {x | x 0 = a ∧ x 1 = a}
def recoveredTransitions (μ : ProbabilityMeasure ShiftSpace) : ℝ × ℝ :=
  (lawMass μ (diagonalCylinder 0)/lawMass μ (stateCylinder 0),
   lawMass μ (diagonalCylinder 1)/lawMass μ (stateCylinder 1))

def bundledLaw (z : ℝ × ℝ) (hz : z ∈ interior) : ProbabilityMeasure ShiftSpace :=
  ⟨twoSidedLaw z hz,inferInstance⟩

def actualIntricacy (μ : ProbabilityMeasure ShiftSpace) : ℝ :=
  Filter.limUnder atTop (rankZeroFiniteIntricacy (μ : Measure ShiftSpace) 0)

theorem stateCylinder_isClopen (a : Fin 2) : IsClopen (stateCylinder a) := by
  exact (isClopen_discrete ({a} : Set (Fin 2))).preimage (continuous_apply 0)

theorem diagonalCylinder_isClopen (a : Fin 2) : IsClopen (diagonalCylinder a) := by
  exact (stateCylinder_isClopen a).inter
    ((isClopen_discrete ({a} : Set (Fin 2))).preimage (continuous_apply 1))

theorem lawMass_continuous {E : Set ShiftSpace} (hE : IsClopen E) :
    Continuous (fun μ : ProbabilityMeasure ShiftSpace => lawMass μ E) := by
  apply continuous_iff_continuousAt.mpr
  intro μ
  exact NNReal.continuous_coe.continuousAt.comp
    (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto continuous_id.continuousAt hE)

theorem stationary_unique {z : ℝ × ℝ} {p : Fin 2 → ℝ}
    (hs : ∑ a, p a = 1) (hp : ∀ b, ∑ a, p a * trans z a b = p b)
    (hd : 2-z.1-z.2 ≠ 0) : p = stationary z := by
  have h0 := hp 0
  norm_num [Fin.sum_univ_two,trans] at h0
  simp only [Fin.sum_univ_two] at hs
  have he : p 1 = 1-p 0 := by linarith
  rw [he] at h0
  funext a
  fin_cases a
  · change p 0 = (1-z.2)/(2-z.1-z.2)
    apply (eq_div_iff hd).mpr
    nlinarith
  · change p 1 = (1-z.1)/(2-z.1-z.2)
    apply (eq_div_iff hd).mpr
    rw [he]
    nlinarith


theorem lawMass_initial {μ : ProbabilityMeasure ShiftSpace} {z : ℝ × ℝ} {p : Fin 2 → ℝ}
    (hp : ∀ a, 0 ≤ p a)
    (hblock : ∀ (k : ℤ) (n : ℕ) (w : Fin (n+1) → Fin 2),
      (μ : Measure ShiftSpace) {x | ∀ j : Fin (n+1), x (k+j.val) = w j} =
      ENNReal.ofReal (p (w 0)*∏ j : Fin n, trans z (w j.castSucc) (w j.succ)))
    (a : Fin 2) : lawMass μ (stateCylinder a) = p a := by
  have he : stateCylinder a = {x : ShiftSpace | ∀ j : Fin 1, x ((0:ℤ)+j.val) = a} := by
    ext x; simp [stateCylinder]
  change ((μ : Measure ShiftSpace) (stateCylinder a)).toReal = _
  rw [he,hblock]
  simp [hp]

theorem lawMass_diagonal {μ : ProbabilityMeasure ShiftSpace} {z : ℝ × ℝ} {p : Fin 2 → ℝ}
    (hp : ∀ a, 0 ≤ p a) (hz : 0 ≤ z.1 ∧ z.1 ≤ 1 ∧ 0 ≤ z.2 ∧ z.2 ≤ 1)
    (hblock : ∀ (k : ℤ) (n : ℕ) (w : Fin (n+1) → Fin 2),
      (μ : Measure ShiftSpace) {x | ∀ j : Fin (n+1), x (k+j.val) = w j} =
      ENNReal.ofReal (p (w 0)*∏ j : Fin n, trans z (w j.castSucc) (w j.succ)))
    (a : Fin 2) : lawMass μ (diagonalCylinder a) = p a * trans z a a := by
  have he : diagonalCylinder a = {x : ShiftSpace | ∀ j : Fin 2, x ((0:ℤ)+j.val) = a} := by
    ext x; simp [diagonalCylinder,Fin.forall_fin_two]
  have hK : 0 ≤ trans z a a := by
    fin_cases a
    · simpa [trans] using hz.1
    · simpa [trans] using hz.2.2.1
  change ((μ : Measure ShiftSpace) (diagonalCylinder a)).toReal = _
  rw [he,hblock]
  simp [ENNReal.toReal_ofReal (mul_nonneg (hp a) hK)]

theorem recoveredTransitions_eq {μ : ProbabilityMeasure ShiftSpace} {z : ℝ × ℝ} {p : Fin 2 → ℝ}
    (hp : ∀ a, 0 < p a) (hz : 0 ≤ z.1 ∧ z.1 ≤ 1 ∧ 0 ≤ z.2 ∧ z.2 ≤ 1)
    (hblock : ∀ (k : ℤ) (n : ℕ) (w : Fin (n+1) → Fin 2),
      (μ : Measure ShiftSpace) {x | ∀ j : Fin (n+1), x (k+j.val) = w j} =
      ENNReal.ofReal (p (w 0)*∏ j : Fin n, trans z (w j.castSucc) (w j.succ))) :
    recoveredTransitions μ = z := by
  unfold recoveredTransitions
  simp_rw [lawMass_initial (fun a => (hp a).le) hblock,
    lawMass_diagonal (fun a => (hp a).le) hz hblock]
  apply Prod.ext <;> dsimp <;> norm_num [trans] <;> field_simp [ne_of_gt (hp 0),ne_of_gt (hp 1)]

theorem bundledLaw_block (z : ℝ × ℝ) (hz : z ∈ interior) (k : ℤ) (n : ℕ) (w : Fin (n+1) → Fin 2) :
    (bundledLaw z hz : Measure ShiftSpace) {x | ∀ j : Fin (n+1), x (k+j.val) = w j} =
      ENNReal.ofReal (stationary z (w 0)*∏ j : Fin n, trans z (w j.castSucc) (w j.succ)) :=
  twoSidedLaw_word z hz k n w

theorem bundledLaw_recovered (z : ℝ × ℝ) (hz : z ∈ interior) :
    recoveredTransitions (bundledLaw z hz) = z :=
  recoveredTransitions_eq (stationary_pos hz) ⟨hz.1.le,hz.2.1.le,hz.2.2.1.le,hz.2.2.2.le⟩
    (bundledLaw_block z hz)

theorem recoveredTransitions_continuousAt {μ : ProbabilityMeasure ShiftSpace}
    (h0 : lawMass μ (stateCylinder 0) ≠ 0) (h1 : lawMass μ (stateCylinder 1) ≠ 0) :
    ContinuousAt recoveredTransitions μ := by
  exact ((lawMass_continuous (diagonalCylinder_isClopen 0)).continuousAt.div
    (lawMass_continuous (stateCylinder_isClopen 0)).continuousAt h0).prodMk
    ((lawMass_continuous (diagonalCylinder_isClopen 1)).continuousAt.div
      (lawMass_continuous (stateCylinder_isClopen 1)).continuousAt h1)


theorem bundledLaw_markov (z : ℝ × ℝ) (hz : z ∈ interior) :
    OneStepMarkovLaw (bundledLaw z hz) :=
  ⟨z,stationary z,⟨hz.1.le,hz.2.1.le,hz.2.2.1.le,hz.2.2.2.le⟩,
    fun a => (stationary_pos hz a).le,stationary_sum hz,stationary_invariant hz,bundledLaw_block z hz⟩

/-- Every stationary one-step law with positive state masses and an interior
recovered matrix equals the constructed law. Boundary and nonergodic laws are
included in the definition of OneStepMarkovLaw; no ergodicity is assumed. -/
theorem markovLaw_eq_bundled {μ : ProbabilityMeasure ShiftSpace}
    (hμ : OneStepMarkovLaw μ) (h0 : 0 < lawMass μ (stateCylinder 0))
    (h1 : 0 < lawMass μ (stateCylinder 1)) (hz : recoveredTransitions μ ∈ interior) :
    μ = bundledLaw (recoveredTransitions μ) hz := by
  obtain ⟨z,p,hzclosed,hp,hs,hstat,hblock⟩ := hμ
  have hpp (a : Fin 2) : 0 < p a := by
    fin_cases a
    · rwa [lawMass_initial hp hblock] at h0
    · rwa [lawMass_initial hp hblock] at h1
  have hrec : recoveredTransitions μ = z := recoveredTransitions_eq hpp hzclosed hblock
  have hzi : z ∈ interior := hrec ▸ hz
  have hd : 2-z.1-z.2 ≠ 0 := by linarith [hzi.2.1,hzi.2.2.2]
  have hpstat : p = stationary z := stationary_unique hs hstat hd
  apply Subtype.ext
  change (μ : Measure ShiftSpace) = twoSidedLaw (recoveredTransitions μ) hz
  apply measure_eq_of_blocks (μ := (μ : Measure ShiftSpace))
  · simp
  · intro k n w
    change (μ : Measure ShiftSpace) _ = twoSidedLaw (recoveredTransitions μ) hz _
    rw [hblock,twoSidedLaw_word]
    simp only [wordProb,hpstat,hrec]

theorem bundledLaw_actualIntricacy (z : ℝ × ℝ) (hz : z ∈ interior) :
    actualIntricacy (bundledLaw z hz) = sourceIntricacy z := by
  unfold actualIntricacy sourceIntricacy
  congr 1
  funext n
  exact rankZeroFiniteIntricacy_eq z hz 0 n


/-- The literal finite intricacy limit exists for every nearby comparison law;
thus local comparison does not exploit junk values of limUnder. -/
theorem markov_neighborhood_convergence {l : ℝ} (hl : 0 < l) (hl1 : l < 1) :
    ∀ᶠ ν in nhds (bundledLaw (chart l 0) (chart_mem_interior hl hl1 (by norm_num) (by norm_num))),
      OneStepMarkovLaw ν → Tendsto (rankZeroFiniteIntricacy (ν : Measure ShiftSpace) 0)
        atTop (nhds (actualIntricacy ν)) := by
  let z := chart l 0
  have hz : z ∈ interior := chart_mem_interior hl hl1 (by norm_num) (by norm_num)
  let μ := bundledLaw z hz
  have hm (a : Fin 2) : lawMass μ (stateCylinder a) = stationary z a :=
    lawMass_initial (fun a => (stationary_pos hz a).le) (bundledLaw_block z hz) a
  have h0 : 0 < lawMass μ (stateCylinder 0) := by rw [hm]; exact stationary_pos hz 0
  have h1 : 0 < lawMass μ (stateCylinder 1) := by rw [hm]; exact stationary_pos hz 1
  have hrec : recoveredTransitions μ = z := bundledLaw_recovered z hz
  have hc := recoveredTransitions_continuousAt (ne_of_gt h0) (ne_of_gt h1)
  have hd : 2-z.1-z.2 ≠ 0 := by linarith [hz.2.1,hz.2.2.2]
  have hIcont : ContinuousAt inverseParameters z := by
    unfold inverseParameters; fun_prop (disch := exact hd)
  have hcomp : ContinuousAt (fun ν => inverseParameters (recoveredTransitions ν)) μ :=
    hIcont.comp_of_eq hc hrec
  have hp : ∀ᶠ ν in nhds μ, (inverseParameters (recoveredTransitions ν)).1 ∈ Ioo (0:ℝ) 1 ∧
      (inverseParameters (recoveredTransitions ν)).2 ∈ Ioo (-1:ℝ) 1 := by
    have hneigh : Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 1 ∈ nhds (inverseParameters (recoveredTransitions μ)) := by
      rw [hrec,inverseParameters_chart (ne_of_lt hl1)]
      exact prod_mem_nhds (Ioo_mem_nhds hl hl1) (Ioo_mem_nhds (by norm_num) (by norm_num))
    exact hcomp hneigh
  have hD : ∀ᶠ ν in nhds μ, 2-(recoveredTransitions ν).1-(recoveredTransitions ν).2 ≠ 0 := by
    have hcD : ContinuousAt (fun ν => 2-(recoveredTransitions ν).1-(recoveredTransitions ν).2) μ :=
      (continuousAt_const.sub hc.fst).sub hc.snd
    apply hcD.eventually_ne
    simpa only [hrec] using hd
  have hN0 := (lawMass_continuous (stateCylinder_isClopen 0)).continuousAt.eventually (isOpen_Ioi.mem_nhds h0)
  have hN1 := (lawMass_continuous (stateCylinder_isClopen 1)).continuousAt.eventually (isOpen_Ioi.mem_nhds h1)
  filter_upwards [hp,hD,hN0,hN1] with ν hν hDν hν0 hν1
  intro hMarkov
  let w := recoveredTransitions ν
  have he : chart (inverseParameters w).1 (inverseParameters w).2 = w := inverse_chart hDν
  have hw : w ∈ interior := he ▸ chart_mem_interior hν.1.1 hν.1.2 hν.2.1 hν.2.2
  have hlim : Tendsto (finiteIntricacy w) atTop (nhds (sourceIntricacy w)) := by
    rw [← he,sourceIntricacy_eq_series hν.1.1 hν.1.2 hν.2.1 hν.2.2]
    exact finiteIntricacy_tendsto_series hν.1.1 hν.1.2 hν.2.1 hν.2.2
  have hEq : ν = bundledLaw w hw := markovLaw_eq_bundled hMarkov hν0 hν1 hw
  have hseq : rankZeroFiniteIntricacy (ν : Measure ShiftSpace) 0 = finiteIntricacy w := by
    rw [hEq]
    exact funext (rankZeroFiniteIntricacy_eq w hw 0)
  have hval : actualIntricacy ν = sourceIntricacy w :=
    (congrArg actualIntricacy hEq).trans (bundledLaw_actualIntricacy w hw)
  rw [hseq,hval]
  exact hlim

/-- A literal measure-space local maximum, in the weak topology of probability
measures, relative to all stationary one-step binary Markov laws. -/
theorem fullySupported_stationary_oneStep_localMaximum :
    ∃ μ : ProbabilityMeasure ShiftSpace,
      (μ : Measure ShiftSpace).IsOpenPosMeasure ∧
      (∀ r : ℤ, (μ : Measure ShiftSpace).map (fun x i => x (r+i)) = (μ : Measure ShiftSpace)) ∧
      OneStepMarkovLaw μ ∧
      Tendsto (rankZeroFiniteIntricacy (μ : Measure ShiftSpace) 0) atTop (nhds (actualIntricacy μ)) ∧
      (∀ᶠ ν in nhds μ, OneStepMarkovLaw ν →
        Tendsto (rankZeroFiniteIntricacy (ν : Measure ShiftSpace) 0) atTop (nhds (actualIntricacy ν))) ∧
      IsLocalMaxOn actualIntricacy {ν | OneStepMarkovLaw ν} μ := by
  obtain ⟨l,hl,hmax,hconv⟩ := source_parameter_claim_chart
  let z := chart l 0
  have hz : z ∈ interior := chart_mem_interior hl.1 hl.2 (by norm_num) (by norm_num)
  let μ := bundledLaw z hz
  have hm (a : Fin 2) : lawMass μ (stateCylinder a) = stationary z a :=
    lawMass_initial (fun a => (stationary_pos hz a).le) (bundledLaw_block z hz) a
  have h0 : 0 < lawMass μ (stateCylinder 0) := by rw [hm]; exact stationary_pos hz 0
  have h1 : 0 < lawMass μ (stateCylinder 1) := by rw [hm]; exact stationary_pos hz 1
  have hrec : recoveredTransitions μ = z := bundledLaw_recovered z hz
  have hc := recoveredTransitions_continuousAt (ne_of_gt h0) (ne_of_gt h1)
  have hopen : IsOpen interior := by
    have he : interior = Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1 := by
      ext w; simp only [interior,mem_prod,mem_Ioo,mem_ofPred_eq]; tauto
    rw [he]
    exact isOpen_Ioo.prod isOpen_Ioo
  have hnear : ∀ᶠ ν in nhds μ, recoveredTransitions ν ∈ interior :=
    hc.eventually (hrec ▸ hopen.mem_nhds hz)
  have hnear0 : ∀ᶠ ν in nhds μ, 0 < lawMass ν (stateCylinder 0) :=
    (lawMass_continuous (stateCylinder_isClopen 0)).continuousAt.eventually
      (isOpen_Ioi.mem_nhds h0)
  have hnear1 : ∀ᶠ ν in nhds μ, 0 < lawMass ν (stateCylinder 1) :=
    (lawMass_continuous (stateCylinder_isClopen 1)).continuousAt.eventually
      (isOpen_Ioi.mem_nhds h1)
  have hevent : ∀ᶠ w in nhds z, w ∈ interior → sourceIntricacy w ≤ sourceIntricacy z := by
    exact eventually_nhdsWithin_iff.mp hmax
  have hmaxnear := hc.eventually (hrec ▸ hevent)
  have hconvactual : Tendsto (rankZeroFiniteIntricacy (μ : Measure ShiftSpace) 0) atTop
      (nhds (actualIntricacy μ)) := by
    change Tendsto (rankZeroFiniteIntricacy (twoSidedLaw z hz) 0) atTop
      (nhds (actualIntricacy (bundledLaw z hz)))
    rw [bundledLaw_actualIntricacy]
    have he : rankZeroFiniteIntricacy (twoSidedLaw z hz) 0 = finiteIntricacy z :=
      funext (rankZeroFiniteIntricacy_eq z hz 0)
    rw [he]
    exact hconv
  refine ⟨μ,?_,fun r => twoSidedLaw_shift z hz r,bundledLaw_markov z hz,hconvactual,markov_neighborhood_convergence hl.1 hl.2,?_⟩
  · change (twoSidedLaw z hz).IsOpenPosMeasure
    infer_instance
  · change ∀ᶠ ν in nhdsWithin μ {ν | OneStepMarkovLaw ν}, actualIntricacy ν ≤ actualIntricacy μ
    apply eventually_nhdsWithin_iff.mpr
    filter_upwards [hnear,hnear0,hnear1,hmaxnear] with ν hν hν0 hν1 hmaxν
    intro hMarkov
    calc
      actualIntricacy ν = sourceIntricacy (recoveredTransitions ν) := by
        exact (congrArg actualIntricacy (markovLaw_eq_bundled hMarkov hν0 hν1 hν)).trans
          (bundledLaw_actualIntricacy (recoveredTransitions ν) hν)
      _ ≤ sourceIntricacy z := by simpa only [hrec] using hmaxν hν
      _ = actualIntricacy μ := (bundledLaw_actualIntricacy z hz).symm

end
end MathDB333569
