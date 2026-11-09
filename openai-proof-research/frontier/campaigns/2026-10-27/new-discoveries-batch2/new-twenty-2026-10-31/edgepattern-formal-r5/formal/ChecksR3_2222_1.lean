import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2222_4 : MaskR3.blockCheck (graph ⟨2,2,2,2⟩) 9 {16321,16322} 1024 256 := by decide
theorem check_2222_5 : MaskR3.blockCheck (graph ⟨2,2,2,2⟩) 9 {16321,16322} 1280 256 := by decide
theorem check_2222_6 : MaskR3.blockCheck (graph ⟨2,2,2,2⟩) 9 {16321,16322} 1536 256 := by decide
theorem check_2222_7 : MaskR3.blockCheck (graph ⟨2,2,2,2⟩) 9 {16321,16322} 1792 256 := by decide
end EdgePattern.TreeModelsR3
