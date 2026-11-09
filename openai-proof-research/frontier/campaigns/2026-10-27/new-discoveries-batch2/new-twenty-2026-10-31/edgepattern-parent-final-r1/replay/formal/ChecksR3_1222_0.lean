import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_1222_0 : MaskR3.blockCheck (graph ⟨1,2,2,2⟩) 8 {8070,8129,8130} 0 256 := by decide
theorem check_1222_1 : MaskR3.blockCheck (graph ⟨1,2,2,2⟩) 8 {8070,8129,8130} 256 256 := by decide
theorem check_1222_2 : MaskR3.blockCheck (graph ⟨1,2,2,2⟩) 8 {8070,8129,8130} 512 256 := by decide
theorem check_1222_3 : MaskR3.blockCheck (graph ⟨1,2,2,2⟩) 8 {8070,8129,8130} 768 256 := by decide
end EdgePattern.TreeModelsR3
