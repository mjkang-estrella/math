import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2020_0 : MaskR3.blockCheck (graph ⟨2,0,2,0⟩) 6 {970,993,1000} 0 256 := by decide
theorem check_2020_1 : MaskR3.blockCheck (graph ⟨2,0,2,0⟩) 6 {970,993,1000} 256 256 := by decide
theorem check_2020_2 : MaskR3.blockCheck (graph ⟨2,0,2,0⟩) 6 {970,993,1000} 512 256 := by decide
theorem check_2020_3 : MaskR3.blockCheck (graph ⟨2,0,2,0⟩) 6 {970,993,1000} 768 256 := by decide
end EdgePattern.TreeModelsR3
