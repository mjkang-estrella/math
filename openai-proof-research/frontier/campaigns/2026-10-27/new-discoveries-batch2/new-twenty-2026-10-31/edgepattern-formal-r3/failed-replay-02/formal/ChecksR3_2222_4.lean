import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2222_16 : MaskR3.blockCheck (graph ⟨2,2,2,2⟩) 9 {16321,16322} 4096 256 := by decide
theorem check_2222_17 : MaskR3.blockCheck (graph ⟨2,2,2,2⟩) 9 {16321,16322} 4352 256 := by decide
theorem check_2222_18 : MaskR3.blockCheck (graph ⟨2,2,2,2⟩) 9 {16321,16322} 4608 256 := by decide
theorem check_2222_19 : MaskR3.blockCheck (graph ⟨2,2,2,2⟩) 9 {16321,16322} 4864 256 := by decide
end EdgePattern.TreeModelsR3
