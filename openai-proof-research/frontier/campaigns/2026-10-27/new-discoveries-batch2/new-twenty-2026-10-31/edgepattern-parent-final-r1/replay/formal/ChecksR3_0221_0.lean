import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_0221_0 : MaskR3.blockCheck (graph ⟨0,2,2,1⟩) 7 {1990} 0 256 := by decide
theorem check_0221_1 : MaskR3.blockCheck (graph ⟨0,2,2,1⟩) 7 {1990} 256 256 := by decide
theorem check_0221_2 : MaskR3.blockCheck (graph ⟨0,2,2,1⟩) 7 {1990} 512 256 := by decide
theorem check_0221_3 : MaskR3.blockCheck (graph ⟨0,2,2,1⟩) 7 {1990} 768 256 := by decide
end EdgePattern.TreeModelsR3
