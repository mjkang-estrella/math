import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_1022_4 : MaskR3.blockCheck (graph ⟨1,0,2,2⟩) 7 {1934,1994} 1024 256 := by decide
theorem check_1022_5 : MaskR3.blockCheck (graph ⟨1,0,2,2⟩) 7 {1934,1994} 1280 256 := by decide
theorem check_1022_6 : MaskR3.blockCheck (graph ⟨1,0,2,2⟩) 7 {1934,1994} 1536 256 := by decide
theorem check_1022_7 : MaskR3.blockCheck (graph ⟨1,0,2,2⟩) 7 {1934,1994} 1792 256 := by decide
end EdgePattern.TreeModelsR3
