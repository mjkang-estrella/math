import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_0222_8 : MaskR3.blockCheck (graph ⟨0,2,2,2⟩) 8 {4038} 2048 256 := by decide
theorem check_0222_9 : MaskR3.blockCheck (graph ⟨0,2,2,2⟩) 8 {4038} 2304 256 := by decide
theorem check_0222_10 : MaskR3.blockCheck (graph ⟨0,2,2,2⟩) 8 {4038} 2560 256 := by decide
theorem check_0222_11 : MaskR3.blockCheck (graph ⟨0,2,2,2⟩) 8 {4038} 2816 256 := by decide
end EdgePattern.TreeModelsR3
