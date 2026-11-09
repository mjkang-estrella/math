import SemFinal
namespace ChanLevine.SemRegression
/-- Six fixed kernel-decided convention checks, n = 3 through 8. -/
theorem canonical3 : ∀ i : ZMod 3, CycleTest (canonical 1 i) ∧ chipWeight (canonical 1 i) = i := by unfold CycleTest; decide
theorem canonical4 : ∀ i : ZMod 4, CycleTest (canonical 1 i) ∧ chipWeight (canonical 1 i) = i := by unfold CycleTest; decide
theorem canonical5 : ∀ i : ZMod 5, CycleTest (canonical 1 i) ∧ chipWeight (canonical 1 i) = i := by unfold CycleTest; decide
theorem canonical6 : ∀ i : ZMod 6, CycleTest (canonical 1 i) ∧ chipWeight (canonical 1 i) = i := by unfold CycleTest; decide
theorem canonical7 : ∀ i : ZMod 7, CycleTest (canonical 1 i) ∧ chipWeight (canonical 1 i) = i := by unfold CycleTest; decide
theorem canonical8 : ∀ i : ZMod 8, CycleTest (canonical 1 i) ∧ chipWeight (canonical 1 i) = i := by unfold CycleTest; decide

def start : SignedConfig 3 := ⟨fun k => if k = 0 then 1 else 0, fun _ => true⟩
def period : List (ZMod 3) := [0, 2, 1, 0, 1, 2]
def afterPeriod : SignedConfig 3 := period.foldl fire start
theorem period_chips : ∀ k, afterPeriod.x k = start.x k := by decide
theorem period_rotors : ∀ k, afterPeriod.q k = start.q k := by decide
theorem period_coverage : ∀ k : ZMod 3, k ∈ period := by decide
theorem empty_facing_rejected :
    ¬ CycleTest (Config.mk (fun _ : ZMod 3 => 0) (fun k => k == 0)) := by unfold CycleTest; decide
end ChanLevine.SemRegression
