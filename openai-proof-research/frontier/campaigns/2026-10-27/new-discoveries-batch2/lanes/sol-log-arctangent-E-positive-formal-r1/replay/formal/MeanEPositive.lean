import MeanEHighPositive
import MeanJets0
import MeanJets1
import MeanJets2
import MeanJets3
import MeanJets4
import MeanJets5
import Mathlib.Tactic.IntervalCases
set_option autoImplicit false
set_option warningAsError true
namespace LogArctangentMean
theorem E_initial_jets {n : ℕ} (hn : n < 24) :
    iteratedDeriv n E 0 =
      match n with
      | 10 => 37847040
      | 12 => 19891322880
      | 14 => 5550283554816
      | 16 => 1162696473968640
      | 18 => 206947471161556992
      | 20 => 33226670114812723200
      | 22 => 4978839848478924865536
      | _ => 0 := by
  interval_cases n <;> first
  | exact E_jet_0
  | exact E_jet_1
  | exact E_jet_2
  | exact E_jet_3
  | exact E_jet_4
  | exact E_jet_5
  | exact E_jet_6
  | exact E_jet_7
  | exact E_jet_8
  | exact E_jet_9
  | exact E_jet_10
  | exact E_jet_11
  | exact E_jet_12
  | exact E_jet_13
  | exact E_jet_14
  | exact E_jet_15
  | exact E_jet_16
  | exact E_jet_17
  | exact E_jet_18
  | exact E_jet_19
  | exact E_jet_20
  | exact E_jet_21
  | exact E_jet_22
  | exact E_jet_23
theorem E_initial_jets_nonneg {n : ℕ} (hn : n < 24) :
    0 ≤ iteratedDeriv n E 0 := by
  rw [E_initial_jets hn]
  split <;> norm_num
/-- Closed positivity for the literal E formed from A, B and their derivatives. -/
theorem E_pos {t : ℝ} (ht : 0 < t) : 0 < E t :=
  derivative_ladder E 24
    (fun j _ => contDiff_E.continuous_iteratedDeriv j le_top)
    (fun _ hn => E_initial_jets_nonneg hn)
    (fun _ ht => E_derivative24_pos ht) t ht
end LogArctangentMean
