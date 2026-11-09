import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_1222_12 : MaskR3.blockCheck (graph ⟨1,2,2,2⟩) 8 {8070,8129,8130} 3072 256 := by decide
theorem check_1222_13 : MaskR3.blockCheck (graph ⟨1,2,2,2⟩) 8 {8070,8129,8130} 3328 256 := by decide
theorem check_1222_14 : MaskR3.blockCheck (graph ⟨1,2,2,2⟩) 8 {8070,8129,8130} 3584 256 := by decide
theorem check_1222_15 : MaskR3.blockCheck (graph ⟨1,2,2,2⟩) 8 {8070,8129,8130} 3840 256 := by decide
end EdgePattern.TreeModelsR3
