import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2011_0 : MaskR3.blockCheck (graph ⟨2,0,1,1⟩) 6 {970} 0 256 := by decide
theorem check_2011_1 : MaskR3.blockCheck (graph ⟨2,0,1,1⟩) 6 {970} 256 256 := by decide
theorem check_2011_2 : MaskR3.blockCheck (graph ⟨2,0,1,1⟩) 6 {970} 512 256 := by decide
theorem check_2011_3 : MaskR3.blockCheck (graph ⟨2,0,1,1⟩) 6 {970} 768 256 := by decide
end EdgePattern.TreeModelsR3
