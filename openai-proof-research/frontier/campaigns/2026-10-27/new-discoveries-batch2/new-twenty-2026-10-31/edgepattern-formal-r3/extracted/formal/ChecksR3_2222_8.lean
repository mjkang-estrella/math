import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2222_32 : MaskR3.blockCheck (graph ⟨2,2,2,2⟩) 9 {16321,16322} 8192 256 := by decide
theorem check_2222_33 : MaskR3.blockCheck (graph ⟨2,2,2,2⟩) 9 {16321,16322} 8448 256 := by decide
theorem check_2222_34 : MaskR3.blockCheck (graph ⟨2,2,2,2⟩) 9 {16321,16322} 8704 256 := by decide
theorem check_2222_35 : MaskR3.blockCheck (graph ⟨2,2,2,2⟩) 9 {16321,16322} 8960 256 := by decide
end EdgePattern.TreeModelsR3
