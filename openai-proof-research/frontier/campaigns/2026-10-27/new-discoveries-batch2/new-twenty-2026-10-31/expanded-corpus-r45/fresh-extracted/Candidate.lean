import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Tactic
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
noncomputable section
namespace MathDB352038
def M : Fin 85 → ℤ := ![55,55,53,47,37,43,47,37,23,19,45,51,33,37,35,41,49,23,47,49,5,51,53,37,19,29,17,43,37,47,53,43,7,53,55,53,27,31,41,35,13,47,51,45,51,47,13,35,41,31,27,53,55,53,7,43,53,47,37,43,17,29,19,37,53,51,5,49,47,23,49,41,35,37,33,51,45,19,23,37,47,43,37,47,53]
def D : Fin 85 → ℤ := ![2,12,20,42,40,30,28,60,42,64,16,28,70,24,76,18,36,70,12,54,56,8,30,56,48,46,60,20,84,10,24,50,60,4,6,40,58,36,38,48,60,14,32,32,14,60,48,38,36,58,40,6,4,60,50,24,10,84,20,60,46,48,56,30,8,56,54,12,70,36,18,76,24,70,28,16,64,42,60,28,30,40,42,20,12]
def A : Fin 85 → ℤ := ![55,9,5,2,2,3,3,1,1,1,6,3,1,3,1,5,2,1,8,1,1,13,3,1,1,1,1,4,1,10,4,1,1,27,18,2,1,2,2,1,1,7,3,3,7,1,1,2,2,1,2,18,27,1,1,4,10,1,4,1,1,1,1,3,13,1,1,8,1,2,5,1,3,1,3,6,1,1,1,3,3,2,2,5,9]
def next (i : Fin 85) : Fin 85 := ⟨(i.val+1)%85, Nat.mod_lt _ (by decide)⟩
def idx (n : ℕ) : Fin 85 := ⟨n%85, Nat.mod_lt _ (by decide)⟩
def q (i : Fin 85) : ℝ := ((M i : ℝ) + Real.sqrt 3049) / (D i : ℝ)
def delta : ℝ := (55 + Real.sqrt 3049) / 2

theorem table : ∀ i : Fin 85, 0 < D i ∧
    A i * D i ≤ M i + 55 ∧ M i + 56 ≤ (A i + 1) * D i ∧
    M (next i) = A i * D i - M i ∧
    D i * D (next i) = 3049 - M (next i)^2 := by decide

theorem sqrt_bounds : 55 < Real.sqrt 3049 ∧ Real.sqrt 3049 < 56 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3049 by norm_num)
  have hp := Real.sqrt_nonneg (3049:ℝ)
  constructor <;> nlinarith

theorem q_bounds (i : Fin 85) : (A i : ℝ) < q i ∧ q i < (A i : ℝ)+1 := by
  obtain ⟨hd, hlo, hhi, _, _⟩ := table i
  have hd' : (0:ℝ) < D i := by exact_mod_cast hd
  have hl' : (A i : ℝ) * D i ≤ M i + 55 := by exact_mod_cast hlo
  have hh' : (M i : ℝ) + 56 ≤ ((A i : ℝ)+1) * D i := by exact_mod_cast hhi
  obtain ⟨hslo,hshi⟩ := sqrt_bounds
  constructor
  · apply (lt_div_iff₀ hd').2; linarith
  · apply (div_lt_iff₀ hd').2; linarith

theorem q_floor (i : Fin 85) : ⌊q i⌋ = A i :=
  Int.floor_eq_iff.mpr ⟨le_of_lt (q_bounds i).1, (q_bounds i).2⟩

theorem q_step (i : Fin 85) : q (next i) = (q i - (A i : ℝ))⁻¹ := by
  obtain ⟨hd, _, _, hm, he⟩ := table i
  have hd' : (D i : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  have hn' : (D (next i) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (table (next i)).1)
  have hm' : (M (next i) : ℝ) = (A i : ℝ)*D i-M i := by exact_mod_cast hm
  have he' : (D i : ℝ)*D (next i) = 3049-(M (next i) : ℝ)^2 := by exact_mod_cast he
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3049 by norm_num)
  apply eq_inv_of_mul_eq_one_left
  dsimp [q]
  field_simp
  rw [show (M i : ℝ) + Real.sqrt 3049 - (D i : ℝ)*A i = Real.sqrt 3049 - M (next i) by linarith]
  nlinarith

theorem idx_succ (n : ℕ) : idx (n+1) = next (idx n) := by
  apply Fin.ext
  simp [idx, next, Nat.add_mod]

theorem actual_stream (n : ℕ) :
    GenContFract.IntFractPair.stream delta n =
      some (GenContFract.IntFractPair.of (q (idx n))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [GenContFract.IntFractPair.stream, ih]
    have hf : Int.fract (q (idx n)) ≠ 0 := by
      rw [Int.fract, q_floor]
      exact ne_of_gt (sub_pos.mpr (q_bounds _).1)
    simp only [GenContFract.IntFractPair.of, Option.bind_some, hf, ite_false]
    have heq : (Int.fract (q (idx n)))⁻¹ = q (idx (n+1)) := by
      rw [Int.fract, q_floor, idx_succ, q_step]
    rw [heq]

def coefficients : Finset ℤ := Finset.univ.image A

theorem seventh_largest : 8 ∈ coefficients ∧
    (coefficients.filter (fun a => 8 < a)).card = 6 ∧ (55:ℚ)/7 < 8 := by
  refine ⟨by decide, by decide, by norm_num⟩

theorem delta_quadratic : delta^2 - 55*delta - 6 = 0 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 3049 by norm_num)
  dsimp [delta]
  nlinarith

theorem delta_integral : IsIntegral ℤ delta := by
  refine ⟨Polynomial.X^2 - (Polynomial.C 55 * Polynomial.X + Polynomial.C 6), ?_, ?_⟩
  · apply Polynomial.monic_X_pow_sub
    compute_degree; norm_num
  · norm_num [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C]
    nlinarith [delta_quadratic]

theorem delta_irrational : Irrational delta := by
  have h : Irrational (Real.sqrt 3049) := by norm_num [irrational_sqrt_ofNat_iff]
  simpa [delta] using (h.intCast_add 55).div_ratCast (show (2:ℚ) ≠ 0 by norm_num)

/-- The literal claim for all purely periodic quadratic integers, with distinct
coefficients ranked by the number of strictly greater distinct values. -/
def SourceConjecture : Prop :=
  ∀ (x : ℝ) (a : ℕ → ℤ) (period : ℕ),
    IsIntegral ℤ x → Irrational x →
    (∃ b c : ℤ, x^2 + (b:ℝ)*x + c = 0) → 0 < period →
    (∀ n, ∃ p : GenContFract.IntFractPair ℝ,
      GenContFract.IntFractPair.stream x n = some p ∧ p.b = a n) →
    (∀ n, a (n+period) = a n) →
    let C := Finset.univ.image (fun i : Fin period => a i.val)
    ∀ w ∈ C, (w:ℝ) ≤ (a 0:ℝ) / ((C.filter (fun z => w < z)).card + 1 : ℕ)

theorem source_refutation : ¬ SourceConjecture := by
  intro h
  have hp (n : ℕ) : A (idx (n+85)) = A (idx n) := by
    congr 1
    apply Fin.ext
    simp [idx]
  have hc : (fun i : Fin 85 => A (idx i.val)) = A := by
    funext i
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt i.isLt)
  have hb : ∃ b c : ℤ, delta^2 + (b:ℝ)*delta + c = 0 := by
    refine ⟨-55, -6, ?_⟩
    push_cast
    nlinarith [delta_quadratic]
  have H := h delta (fun n => A (idx n)) 85 delta_integral delta_irrational hb
    (by norm_num) (fun n => ⟨_, actual_stream n, q_floor _⟩) hp
  dsimp only at H
  rw [hc] at H
  change ∀ w ∈ coefficients, (w:ℝ) ≤ (A (idx 0):ℝ) /
    ((coefficients.filter (fun z => w < z)).card + 1 : ℕ) at H
  have H8 := H 8 seventh_largest.1
  rw [seventh_largest.2.1] at H8
  norm_num [A, idx] at H8

end MathDB352038
