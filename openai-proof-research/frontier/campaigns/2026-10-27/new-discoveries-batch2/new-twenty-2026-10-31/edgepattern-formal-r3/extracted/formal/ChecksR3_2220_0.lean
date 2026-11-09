import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2220_0 : MaskR3.blockCheck (graph ⟨2,2,2,0⟩) 8 {4065} 0 256 := by decide
theorem check_2220_1 : MaskR3.blockCheck (graph ⟨2,2,2,0⟩) 8 {4065} 256 256 := by decide
theorem check_2220_2 : MaskR3.blockCheck (graph ⟨2,2,2,0⟩) 8 {4065} 512 256 := by decide
theorem check_2220_3 : MaskR3.blockCheck (graph ⟨2,2,2,0⟩) 8 {4065} 768 256 := by decide
end EdgePattern.TreeModelsR3
