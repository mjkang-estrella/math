import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2221_20 : MaskR3.blockCheck (graph ⟨2,2,2,1⟩) 8 {4065,8129,8130} 5120 256 := by decide
theorem check_2221_21 : MaskR3.blockCheck (graph ⟨2,2,2,1⟩) 8 {4065,8129,8130} 5376 256 := by decide
theorem check_2221_22 : MaskR3.blockCheck (graph ⟨2,2,2,1⟩) 8 {4065,8129,8130} 5632 256 := by decide
theorem check_2221_23 : MaskR3.blockCheck (graph ⟨2,2,2,1⟩) 8 {4065,8129,8130} 5888 256 := by decide
end EdgePattern.TreeModelsR3
