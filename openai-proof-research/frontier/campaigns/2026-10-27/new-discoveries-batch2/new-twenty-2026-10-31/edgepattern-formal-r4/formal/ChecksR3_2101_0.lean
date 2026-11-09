import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2101_0 : MaskR3.blockCheck (graph ⟨2,1,0,1⟩) 6 {497,977} 0 256 := by decide
theorem check_2101_1 : MaskR3.blockCheck (graph ⟨2,1,0,1⟩) 6 {497,977} 256 256 := by decide
theorem check_2101_2 : MaskR3.blockCheck (graph ⟨2,1,0,1⟩) 6 {497,977} 512 256 := by decide
theorem check_2101_3 : MaskR3.blockCheck (graph ⟨2,1,0,1⟩) 6 {497,977} 768 256 := by decide
end EdgePattern.TreeModelsR3
