import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2222_8 : MaskR3.blockCheck (graph ⟨2,2,2,2⟩) 9 {16321,16322} 2048 256 := by decide
theorem check_2222_9 : MaskR3.blockCheck (graph ⟨2,2,2,2⟩) 9 {16321,16322} 2304 256 := by decide
theorem check_2222_10 : MaskR3.blockCheck (graph ⟨2,2,2,2⟩) 9 {16321,16322} 2560 256 := by decide
theorem check_2222_11 : MaskR3.blockCheck (graph ⟨2,2,2,2⟩) 9 {16321,16322} 2816 256 := by decide
end EdgePattern.TreeModelsR3
