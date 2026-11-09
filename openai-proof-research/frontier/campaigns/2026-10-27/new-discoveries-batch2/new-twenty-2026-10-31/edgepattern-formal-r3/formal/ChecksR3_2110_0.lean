import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2110_0 : MaskR3.blockCheck (graph ⟨2,1,1,0⟩) 6 {497,993} 0 256 := by decide
theorem check_2110_1 : MaskR3.blockCheck (graph ⟨2,1,1,0⟩) 6 {497,993} 256 256 := by decide
theorem check_2110_2 : MaskR3.blockCheck (graph ⟨2,1,1,0⟩) 6 {497,993} 512 256 := by decide
theorem check_2110_3 : MaskR3.blockCheck (graph ⟨2,1,1,0⟩) 6 {497,993} 768 256 := by decide
end EdgePattern.TreeModelsR3
