import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_1200_0 : MaskR3.blockCheck (graph ⟨1,2,0,0⟩) 6 {497} 0 256 := by decide
theorem check_1200_1 : MaskR3.blockCheck (graph ⟨1,2,0,0⟩) 6 {497} 256 256 := by decide
end EdgePattern.TreeModelsR3
