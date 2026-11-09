import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2012_4 : MaskR3.blockCheck (graph ⟨2,0,1,2⟩) 7 {1994} 1024 256 := by decide
theorem check_2012_5 : MaskR3.blockCheck (graph ⟨2,0,1,2⟩) 7 {1994} 1280 256 := by decide
theorem check_2012_6 : MaskR3.blockCheck (graph ⟨2,0,1,2⟩) 7 {1994} 1536 256 := by decide
theorem check_2012_7 : MaskR3.blockCheck (graph ⟨2,0,1,2⟩) 7 {1994} 1792 256 := by decide
end EdgePattern.TreeModelsR3
