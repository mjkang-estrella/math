import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2200_0 : MaskR3.blockCheck (graph ⟨2,2,0,0⟩) 7 {1009} 0 256 := by decide
theorem check_2200_1 : MaskR3.blockCheck (graph ⟨2,2,0,0⟩) 7 {1009} 256 256 := by decide
theorem check_2200_2 : MaskR3.blockCheck (graph ⟨2,2,0,0⟩) 7 {1009} 512 256 := by decide
theorem check_2200_3 : MaskR3.blockCheck (graph ⟨2,2,0,0⟩) 7 {1009} 768 256 := by decide
end EdgePattern.TreeModelsR3
