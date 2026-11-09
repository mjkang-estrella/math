from diagnostics import *
w=json.load(open(O/'cf-output.json'))['counterexample'];m,d=55,2;states=[]
for a in w['period']:
 states.append((m,d));m=a*d-m;d=(3049-m*m)//d
assert (m,d)==(55,2)
s='''import Mathlib.Algebra.ContinuedFractions.Computation.Translations
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Tactic
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace MathDB352038
'''
for name,vals in [('M',[x[0] for x in states]),('D',[x[1] for x in states]),('A',w['period'])]:s+=f'def {name} : Fin 85 → ℤ := !['+','.join(map(str,vals))+']\n'
s+='''def next (i : Fin 85) : Fin 85 := ⟨(i.val+1)%85, Nat.mod_lt _ (by decide)⟩
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
  have hf : q i - (A i : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr (q_bounds i).1)
  apply (eq_inv_iff_mul_eq_one₀ hf).2
  dsimp [q]
  field_simp
  nlinarith [sq_nonneg ((M (next i) : ℝ) + M i - (A i : ℝ)*D i)]

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
    simp only [GenContFract.IntFractPair.of, Option.bind_some, hf, if_false]
    congr 2
    rw [Int.fract, q_floor, idx_succ, q_step]

def coefficients : Finset ℤ := Finset.univ.image A

theorem seventh_largest : 8 ∈ coefficients ∧
    (coefficients.filter (fun a => 8 < a)).card = 6 ∧ (55:ℚ)/7 < 8 := by
  decide

end MathDB352038
'''
(O/'Candidate.lean').write_text(s)
