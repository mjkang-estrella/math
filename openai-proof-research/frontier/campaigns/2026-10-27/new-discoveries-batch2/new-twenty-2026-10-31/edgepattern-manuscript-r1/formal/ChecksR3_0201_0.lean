import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_0201_0 : MaskR3.blockCheck (graph ⟨0,2,0,1⟩) 5 {241,244,454,465,468} 0 256 := by decide
theorem check_0201_1 : MaskR3.blockCheck (graph ⟨0,2,0,1⟩) 5 {241,244,454,465,468} 256 256 := by decide
end EdgePattern.TreeModelsR3
