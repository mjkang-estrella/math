import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2012_0 : MaskR3.blockCheck (graph ⟨2,0,1,2⟩) 7 {1994} 0 256 := by decide
theorem check_2012_1 : MaskR3.blockCheck (graph ⟨2,0,1,2⟩) 7 {1994} 256 256 := by decide
theorem check_2012_2 : MaskR3.blockCheck (graph ⟨2,0,1,2⟩) 7 {1994} 512 256 := by decide
theorem check_2012_3 : MaskR3.blockCheck (graph ⟨2,0,1,2⟩) 7 {1994} 768 256 := by decide
end EdgePattern.TreeModelsR3
