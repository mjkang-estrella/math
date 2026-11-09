import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_0212_4 : MaskR3.blockCheck (graph ⟨0,2,1,2⟩) 7 {1990} 1024 256 := by decide
theorem check_0212_5 : MaskR3.blockCheck (graph ⟨0,2,1,2⟩) 7 {1990} 1280 256 := by decide
theorem check_0212_6 : MaskR3.blockCheck (graph ⟨0,2,1,2⟩) 7 {1990} 1536 256 := by decide
theorem check_0212_7 : MaskR3.blockCheck (graph ⟨0,2,1,2⟩) 7 {1990} 1792 256 := by decide
end EdgePattern.TreeModelsR3
