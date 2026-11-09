import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_0222_0 : MaskR3.blockCheck (graph ⟨0,2,2,2⟩) 8 {4038} 0 256 := by decide
theorem check_0222_1 : MaskR3.blockCheck (graph ⟨0,2,2,2⟩) 8 {4038} 256 256 := by decide
theorem check_0222_2 : MaskR3.blockCheck (graph ⟨0,2,2,2⟩) 8 {4038} 512 256 := by decide
theorem check_0222_3 : MaskR3.blockCheck (graph ⟨0,2,2,2⟩) 8 {4038} 768 256 := by decide
end EdgePattern.TreeModelsR3
