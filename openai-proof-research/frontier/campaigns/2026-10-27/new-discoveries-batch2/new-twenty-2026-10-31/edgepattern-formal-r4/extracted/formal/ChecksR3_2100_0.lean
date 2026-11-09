import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2100_0 : MaskR3.blockCheck (graph ⟨2,1,0,0⟩) 6 {497} 0 256 := by decide
theorem check_2100_1 : MaskR3.blockCheck (graph ⟨2,1,0,0⟩) 6 {497} 256 256 := by decide
end EdgePattern.TreeModelsR3
