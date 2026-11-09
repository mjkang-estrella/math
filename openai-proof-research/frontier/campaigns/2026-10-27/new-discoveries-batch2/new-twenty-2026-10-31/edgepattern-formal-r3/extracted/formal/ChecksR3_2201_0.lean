import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2201_0 : MaskR3.blockCheck (graph ⟨2,2,0,1⟩) 7 {1009,2001} 0 256 := by decide
theorem check_2201_1 : MaskR3.blockCheck (graph ⟨2,2,0,1⟩) 7 {1009,2001} 256 256 := by decide
theorem check_2201_2 : MaskR3.blockCheck (graph ⟨2,2,0,1⟩) 7 {1009,2001} 512 256 := by decide
theorem check_2201_3 : MaskR3.blockCheck (graph ⟨2,2,0,1⟩) 7 {1009,2001} 768 256 := by decide
end EdgePattern.TreeModelsR3
