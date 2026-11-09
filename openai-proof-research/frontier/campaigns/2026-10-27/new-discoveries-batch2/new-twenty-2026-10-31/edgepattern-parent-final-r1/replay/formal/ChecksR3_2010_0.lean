import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2010_0 : MaskR3.blockCheck (graph ⟨2,0,1,0⟩) 5 {241,248,458,481,488} 0 256 := by decide
theorem check_2010_1 : MaskR3.blockCheck (graph ⟨2,0,1,0⟩) 5 {241,248,458,481,488} 256 256 := by decide
end EdgePattern.TreeModelsR3
