import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_1110_0 : MaskR3.blockCheck (graph ⟨1,1,1,0⟩) 5 {241,481} 0 256 := by decide
theorem check_1110_1 : MaskR3.blockCheck (graph ⟨1,1,1,0⟩) 5 {241,481} 256 256 := by decide
end EdgePattern.TreeModelsR3
