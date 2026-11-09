import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_0110_0 : MaskR3.blockCheck (graph ⟨0,1,1,0⟩) 4 {60,113,116,142,172,198,225,228} 0 256 := by decide
end EdgePattern.TreeModelsR3
