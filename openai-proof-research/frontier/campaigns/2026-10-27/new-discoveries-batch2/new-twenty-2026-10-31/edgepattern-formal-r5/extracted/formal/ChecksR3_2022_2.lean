import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2022_8 : MaskR3.blockCheck (graph ⟨2,0,2,2⟩) 8 {4042} 2048 256 := by decide
theorem check_2022_9 : MaskR3.blockCheck (graph ⟨2,0,2,2⟩) 8 {4042} 2304 256 := by decide
theorem check_2022_10 : MaskR3.blockCheck (graph ⟨2,0,2,2⟩) 8 {4042} 2560 256 := by decide
theorem check_2022_11 : MaskR3.blockCheck (graph ⟨2,0,2,2⟩) 8 {4042} 2816 256 := by decide
end EdgePattern.TreeModelsR3
