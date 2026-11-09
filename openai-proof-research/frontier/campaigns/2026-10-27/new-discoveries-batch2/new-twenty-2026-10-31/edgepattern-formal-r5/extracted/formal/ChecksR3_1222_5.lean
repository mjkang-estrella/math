import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_1222_20 : MaskR3.blockCheck (graph ⟨1,2,2,2⟩) 8 {8070,8129,8130} 5120 256 := by decide
theorem check_1222_21 : MaskR3.blockCheck (graph ⟨1,2,2,2⟩) 8 {8070,8129,8130} 5376 256 := by decide
theorem check_1222_22 : MaskR3.blockCheck (graph ⟨1,2,2,2⟩) 8 {8070,8129,8130} 5632 256 := by decide
theorem check_1222_23 : MaskR3.blockCheck (graph ⟨1,2,2,2⟩) 8 {8070,8129,8130} 5888 256 := by decide
end EdgePattern.TreeModelsR3
