import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_1022_0 : MaskR3.blockCheck (graph ⟨1,0,2,2⟩) 7 {1934,1994} 0 256 := by decide
theorem check_1022_1 : MaskR3.blockCheck (graph ⟨1,0,2,2⟩) 7 {1934,1994} 256 256 := by decide
theorem check_1022_2 : MaskR3.blockCheck (graph ⟨1,0,2,2⟩) 7 {1934,1994} 512 256 := by decide
theorem check_1022_3 : MaskR3.blockCheck (graph ⟨1,0,2,2⟩) 7 {1934,1994} 768 256 := by decide
end EdgePattern.TreeModelsR3
