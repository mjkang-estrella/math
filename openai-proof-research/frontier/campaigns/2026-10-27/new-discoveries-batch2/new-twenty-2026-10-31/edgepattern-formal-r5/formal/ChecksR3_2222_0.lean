import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2222_0 : MaskR3.blockCheck (graph ⟨2,2,2,2⟩) 9 {16321,16322} 0 256 := by decide
theorem check_2222_1 : MaskR3.blockCheck (graph ⟨2,2,2,2⟩) 9 {16321,16322} 256 256 := by decide
theorem check_2222_2 : MaskR3.blockCheck (graph ⟨2,2,2,2⟩) 9 {16321,16322} 512 256 := by decide
theorem check_2222_3 : MaskR3.blockCheck (graph ⟨2,2,2,2⟩) 9 {16321,16322} 768 256 := by decide
end EdgePattern.TreeModelsR3
