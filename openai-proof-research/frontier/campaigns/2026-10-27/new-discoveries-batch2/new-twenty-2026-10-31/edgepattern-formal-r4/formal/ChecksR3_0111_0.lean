import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_0111_0 : MaskR3.blockCheck (graph ⟨0,1,1,1⟩) 5 {398,454} 0 256 := by decide
theorem check_0111_1 : MaskR3.blockCheck (graph ⟨0,1,1,1⟩) 5 {398,454} 256 256 := by decide
end EdgePattern.TreeModelsR3
