import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_1010_0 : MaskR3.blockCheck (graph ⟨1,0,1,0⟩) 4 {60,113,120,142,172,202,225,232} 0 256 := by decide
end EdgePattern.TreeModelsR3
