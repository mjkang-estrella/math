import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2201_4 : MaskR3.blockCheck (graph ⟨2,2,0,1⟩) 7 {1009,2001} 1024 256 := by decide
theorem check_2201_5 : MaskR3.blockCheck (graph ⟨2,2,0,1⟩) 7 {1009,2001} 1280 256 := by decide
theorem check_2201_6 : MaskR3.blockCheck (graph ⟨2,2,0,1⟩) 7 {1009,2001} 1536 256 := by decide
theorem check_2201_7 : MaskR3.blockCheck (graph ⟨2,2,0,1⟩) 7 {1009,2001} 1792 256 := by decide
end EdgePattern.TreeModelsR3
