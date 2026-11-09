import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2212_24 : MaskR3.blockCheck (graph ⟨2,2,1,2⟩) 8 {7121,8129,8130} 6144 256 := by decide
theorem check_2212_25 : MaskR3.blockCheck (graph ⟨2,2,1,2⟩) 8 {7121,8129,8130} 6400 256 := by decide
theorem check_2212_26 : MaskR3.blockCheck (graph ⟨2,2,1,2⟩) 8 {7121,8129,8130} 6656 256 := by decide
theorem check_2212_27 : MaskR3.blockCheck (graph ⟨2,2,1,2⟩) 8 {7121,8129,8130} 6912 256 := by decide
end EdgePattern.TreeModelsR3
