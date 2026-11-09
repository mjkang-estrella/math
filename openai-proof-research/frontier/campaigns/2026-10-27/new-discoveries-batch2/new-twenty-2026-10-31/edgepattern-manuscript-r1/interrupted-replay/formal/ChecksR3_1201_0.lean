import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_1201_0 : MaskR3.blockCheck (graph ⟨1,2,0,1⟩) 6 {497,977} 0 256 := by decide
theorem check_1201_1 : MaskR3.blockCheck (graph ⟨1,2,0,1⟩) 6 {497,977} 256 256 := by decide
theorem check_1201_2 : MaskR3.blockCheck (graph ⟨1,2,0,1⟩) 6 {497,977} 512 256 := by decide
theorem check_1201_3 : MaskR3.blockCheck (graph ⟨1,2,0,1⟩) 6 {497,977} 768 256 := by decide
end EdgePattern.TreeModelsR3
