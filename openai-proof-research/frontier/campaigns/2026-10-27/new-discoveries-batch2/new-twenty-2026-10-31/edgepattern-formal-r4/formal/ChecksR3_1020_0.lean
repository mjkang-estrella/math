import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_1020_0 : MaskR3.blockCheck (graph ⟨1,0,2,0⟩) 5 {398,428,458,481,488} 0 256 := by decide
theorem check_1020_1 : MaskR3.blockCheck (graph ⟨1,0,2,0⟩) 5 {398,428,458,481,488} 256 256 := by decide
end EdgePattern.TreeModelsR3
