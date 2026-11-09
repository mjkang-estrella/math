import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_1001_0 : MaskR3.blockCheck (graph ⟨1,0,0,1⟩) 4 {60,113,120,142,156,202,209,216} 0 256 := by decide
end EdgePattern.TreeModelsR3
