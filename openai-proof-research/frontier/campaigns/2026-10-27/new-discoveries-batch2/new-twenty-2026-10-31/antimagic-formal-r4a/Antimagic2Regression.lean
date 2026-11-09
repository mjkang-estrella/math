import Antimagic2Finite
import AntimagicRegression
namespace Antimagic
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem literal21 : FiniteCertificate 2 1 2 (by decide) := by
  refine ⟨by decide, by decide, ?_, by decide, by decide⟩
  decide
theorem literal22 : FiniteCertificate 2 2 6 (by decide) := by
  refine ⟨by decide, by decide, ?_, by decide, by decide⟩
  decide
theorem literal23 : FiniteCertificate 2 3 14 (by decide) := by
  refine ⟨by decide, by decide, ?_, by decide, by decide⟩
  decide
theorem literal41 : FiniteCertificate 4 1 4 (by decide) := by
  refine ⟨by decide, by decide, ?_, by decide, by decide⟩
  decide
theorem literal42 : FiniteCertificate 4 2 20 (by decide) := by
  refine ⟨by decide, by decide, ?_, by decide, by decide⟩
  decide
theorem literal43 : FiniteCertificate 4 3 84 (by decide) := by
  refine ⟨by decide, by decide, ?_, by decide, by decide⟩
  decide

#print axioms literal43
#print axioms certified_construction
end Antimagic
