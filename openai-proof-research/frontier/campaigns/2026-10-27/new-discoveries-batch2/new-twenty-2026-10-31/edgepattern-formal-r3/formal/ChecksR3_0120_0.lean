import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_0120_0 : MaskR3.blockCheck (graph ⟨0,1,2,0⟩) 5 {398,428,454,481,484} 0 256 := by decide
theorem check_0120_1 : MaskR3.blockCheck (graph ⟨0,1,2,0⟩) 5 {398,428,454,481,484} 256 256 := by decide
end EdgePattern.TreeModelsR3
