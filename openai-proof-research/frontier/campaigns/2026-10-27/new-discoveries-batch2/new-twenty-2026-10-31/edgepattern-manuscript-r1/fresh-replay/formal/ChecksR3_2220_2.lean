import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2220_8 : MaskR3.blockCheck (graph ⟨2,2,2,0⟩) 8 {4065} 2048 256 := by decide
theorem check_2220_9 : MaskR3.blockCheck (graph ⟨2,2,2,0⟩) 8 {4065} 2304 256 := by decide
theorem check_2220_10 : MaskR3.blockCheck (graph ⟨2,2,2,0⟩) 8 {4065} 2560 256 := by decide
theorem check_2220_11 : MaskR3.blockCheck (graph ⟨2,2,2,0⟩) 8 {4065} 2816 256 := by decide
end EdgePattern.TreeModelsR3
