import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_0222_4 : MaskR3.blockCheck (graph ⟨0,2,2,2⟩) 8 {4038} 1024 256 := by decide
theorem check_0222_5 : MaskR3.blockCheck (graph ⟨0,2,2,2⟩) 8 {4038} 1280 256 := by decide
theorem check_0222_6 : MaskR3.blockCheck (graph ⟨0,2,2,2⟩) 8 {4038} 1536 256 := by decide
theorem check_0222_7 : MaskR3.blockCheck (graph ⟨0,2,2,2⟩) 8 {4038} 1792 256 := by decide
end EdgePattern.TreeModelsR3
