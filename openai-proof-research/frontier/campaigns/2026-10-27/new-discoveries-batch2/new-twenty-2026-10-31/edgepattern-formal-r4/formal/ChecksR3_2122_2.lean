import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2122_8 : MaskR3.blockCheck (graph ⟨2,1,2,2⟩) 8 {7882,8129,8130} 2048 256 := by decide
theorem check_2122_9 : MaskR3.blockCheck (graph ⟨2,1,2,2⟩) 8 {7882,8129,8130} 2304 256 := by decide
theorem check_2122_10 : MaskR3.blockCheck (graph ⟨2,1,2,2⟩) 8 {7882,8129,8130} 2560 256 := by decide
theorem check_2122_11 : MaskR3.blockCheck (graph ⟨2,1,2,2⟩) 8 {7882,8129,8130} 2816 256 := by decide
end EdgePattern.TreeModelsR3
