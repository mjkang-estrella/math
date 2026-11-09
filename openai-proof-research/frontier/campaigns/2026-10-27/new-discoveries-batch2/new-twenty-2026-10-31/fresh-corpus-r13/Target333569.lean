import Mathlib

/- Exact finite-cylinder formulation of the target. This file contains definitions
   only. No theorem asserting SourceClaim has been proved. -/
namespace MathDB333569
noncomputable section
open Filter

def interior : Set (ℝ × ℝ) := {z | 0 < z.1 ∧ z.1 < 1 ∧ 0 < z.2 ∧ z.2 < 1}

def trans (z : ℝ × ℝ) (a b : Fin 2) : ℝ :=
  if a = 0 then (if b = 0 then z.1 else 1-z.1)
  else (if b = 0 then 1-z.2 else z.2)

def stationary (z : ℝ × ℝ) (a : Fin 2) : ℝ :=
  if a = 0 then (1-z.2)/(2-z.1-z.2) else (1-z.1)/(2-z.1-z.2)

def wordProb (z : ℝ × ℝ) (n : ℕ) (w : Fin (n+1) → Fin 2) : ℝ :=
  stationary z (w 0) * ∏ i : Fin n, trans z (w i.castSucc) (w i.succ)

def marginal (z : ℝ × ℝ) (n : ℕ) (S : Finset (Fin (n+1)))
    (a : S → Fin 2) : ℝ := by
  classical
  exact ∑ w : Fin (n+1) → Fin 2,
    if ∀ i : S, w i.val = a i then wordProb z n w else 0

def sampleEntropy (z : ℝ × ℝ) (n : ℕ) (S : Finset (Fin (n+1))) : ℝ :=
  - ∑ a : S → Fin 2, marginal z n S a * Real.log (marginal z n S a)

def finiteIntricacy (z : ℝ × ℝ) (n : ℕ) : ℝ := by
  classical
  exact (2 * (∑ S : Finset (Fin (n+1)), sampleEntropy z n S) / (2:ℝ)^(n+1)
    - sampleEntropy z n Finset.univ) / (n+1:ℝ)

def sourceIntricacy (z : ℝ × ℝ) : ℝ :=
  Filter.limUnder atTop (finiteIntricacy z)

def SourceClaim : Prop :=
  ∃ z ∈ interior, IsLocalMaxOn sourceIntricacy interior z ∧
    Tendsto (finiteIntricacy z) atTop (nhds (sourceIntricacy z))

end
end MathDB333569
