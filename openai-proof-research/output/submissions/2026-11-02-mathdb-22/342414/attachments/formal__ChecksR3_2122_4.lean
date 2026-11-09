import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2122_16 : MaskR3.blockCheck (graph ⟨2,1,2,2⟩) 8 {7882,8129,8130} 4096 256 := by decide
theorem check_2122_17 : MaskR3.blockCheck (graph ⟨2,1,2,2⟩) 8 {7882,8129,8130} 4352 256 := by decide
theorem check_2122_18 : MaskR3.blockCheck (graph ⟨2,1,2,2⟩) 8 {7882,8129,8130} 4608 256 := by decide
theorem check_2122_19 : MaskR3.blockCheck (graph ⟨2,1,2,2⟩) 8 {7882,8129,8130} 4864 256 := by decide
end EdgePattern.TreeModelsR3
