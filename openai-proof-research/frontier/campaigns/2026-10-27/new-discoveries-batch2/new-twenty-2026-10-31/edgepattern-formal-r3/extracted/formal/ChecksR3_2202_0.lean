import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2202_0 : MaskR3.blockCheck (graph ⟨2,2,0,2⟩) 8 {4049} 0 256 := by decide
theorem check_2202_1 : MaskR3.blockCheck (graph ⟨2,2,0,2⟩) 8 {4049} 256 256 := by decide
theorem check_2202_2 : MaskR3.blockCheck (graph ⟨2,2,0,2⟩) 8 {4049} 512 256 := by decide
theorem check_2202_3 : MaskR3.blockCheck (graph ⟨2,2,0,2⟩) 8 {4049} 768 256 := by decide
end EdgePattern.TreeModelsR3
