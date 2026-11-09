import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_0021_0 : MaskR3.blockCheck (graph ⟨0,0,2,1⟩) 6 {462} 0 256 := by decide
theorem check_0021_1 : MaskR3.blockCheck (graph ⟨0,0,2,1⟩) 6 {462} 256 256 := by decide
end EdgePattern.TreeModelsR3
