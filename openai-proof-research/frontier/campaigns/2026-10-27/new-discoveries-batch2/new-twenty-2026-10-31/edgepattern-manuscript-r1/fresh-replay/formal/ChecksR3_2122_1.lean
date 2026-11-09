import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2122_4 : MaskR3.blockCheck (graph ⟨2,1,2,2⟩) 8 {7882,8129,8130} 1024 256 := by decide
theorem check_2122_5 : MaskR3.blockCheck (graph ⟨2,1,2,2⟩) 8 {7882,8129,8130} 1280 256 := by decide
theorem check_2122_6 : MaskR3.blockCheck (graph ⟨2,1,2,2⟩) 8 {7882,8129,8130} 1536 256 := by decide
theorem check_2122_7 : MaskR3.blockCheck (graph ⟨2,1,2,2⟩) 8 {7882,8129,8130} 1792 256 := by decide
end EdgePattern.TreeModelsR3
