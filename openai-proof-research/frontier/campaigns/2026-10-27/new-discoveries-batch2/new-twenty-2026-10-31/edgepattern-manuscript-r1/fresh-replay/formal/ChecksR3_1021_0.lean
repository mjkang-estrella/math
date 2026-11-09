import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_1021_0 : MaskR3.blockCheck (graph ⟨1,0,2,1⟩) 6 {910,970} 0 256 := by decide
theorem check_1021_1 : MaskR3.blockCheck (graph ⟨1,0,2,1⟩) 6 {910,970} 256 256 := by decide
theorem check_1021_2 : MaskR3.blockCheck (graph ⟨1,0,2,1⟩) 6 {910,970} 512 256 := by decide
theorem check_1021_3 : MaskR3.blockCheck (graph ⟨1,0,2,1⟩) 6 {910,970} 768 256 := by decide
end EdgePattern.TreeModelsR3
