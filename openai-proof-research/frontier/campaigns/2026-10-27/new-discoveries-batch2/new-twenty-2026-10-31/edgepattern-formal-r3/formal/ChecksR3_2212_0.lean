import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2212_0 : MaskR3.blockCheck (graph ⟨2,2,1,2⟩) 8 {7121,8129,8130} 0 256 := by decide
theorem check_2212_1 : MaskR3.blockCheck (graph ⟨2,2,1,2⟩) 8 {7121,8129,8130} 256 256 := by decide
theorem check_2212_2 : MaskR3.blockCheck (graph ⟨2,2,1,2⟩) 8 {7121,8129,8130} 512 256 := by decide
theorem check_2212_3 : MaskR3.blockCheck (graph ⟨2,2,1,2⟩) 8 {7121,8129,8130} 768 256 := by decide
end EdgePattern.TreeModelsR3
