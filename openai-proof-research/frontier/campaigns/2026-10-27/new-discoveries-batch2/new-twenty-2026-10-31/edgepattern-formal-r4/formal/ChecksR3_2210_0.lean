import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2210_0 : MaskR3.blockCheck (graph ⟨2,2,1,0⟩) 7 {1009,2017} 0 256 := by decide
theorem check_2210_1 : MaskR3.blockCheck (graph ⟨2,2,1,0⟩) 7 {1009,2017} 256 256 := by decide
theorem check_2210_2 : MaskR3.blockCheck (graph ⟨2,2,1,0⟩) 7 {1009,2017} 512 256 := by decide
theorem check_2210_3 : MaskR3.blockCheck (graph ⟨2,2,1,0⟩) 7 {1009,2017} 768 256 := by decide
end EdgePattern.TreeModelsR3
