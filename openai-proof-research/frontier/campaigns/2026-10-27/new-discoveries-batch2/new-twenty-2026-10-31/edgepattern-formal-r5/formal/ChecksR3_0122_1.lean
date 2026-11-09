import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_0122_4 : MaskR3.blockCheck (graph ⟨0,1,2,2⟩) 7 {1934,1990} 1024 256 := by decide
theorem check_0122_5 : MaskR3.blockCheck (graph ⟨0,1,2,2⟩) 7 {1934,1990} 1280 256 := by decide
theorem check_0122_6 : MaskR3.blockCheck (graph ⟨0,1,2,2⟩) 7 {1934,1990} 1536 256 := by decide
theorem check_0122_7 : MaskR3.blockCheck (graph ⟨0,1,2,2⟩) 7 {1934,1990} 1792 256 := by decide
end EdgePattern.TreeModelsR3
