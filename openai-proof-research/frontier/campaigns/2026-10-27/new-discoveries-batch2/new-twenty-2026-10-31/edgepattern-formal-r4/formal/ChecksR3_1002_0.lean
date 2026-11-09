import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_1002_0 : MaskR3.blockCheck (graph ⟨1,0,0,2⟩) 5 {398,412,458,465,472} 0 256 := by decide
theorem check_1002_1 : MaskR3.blockCheck (graph ⟨1,0,0,2⟩) 5 {398,412,458,465,472} 256 256 := by decide
end EdgePattern.TreeModelsR3
