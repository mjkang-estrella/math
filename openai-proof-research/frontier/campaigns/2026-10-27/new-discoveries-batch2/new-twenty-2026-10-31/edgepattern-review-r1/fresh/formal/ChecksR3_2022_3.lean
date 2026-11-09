import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2022_12 : MaskR3.blockCheck (graph ⟨2,0,2,2⟩) 8 {4042} 3072 256 := by decide
theorem check_2022_13 : MaskR3.blockCheck (graph ⟨2,0,2,2⟩) 8 {4042} 3328 256 := by decide
theorem check_2022_14 : MaskR3.blockCheck (graph ⟨2,0,2,2⟩) 8 {4042} 3584 256 := by decide
theorem check_2022_15 : MaskR3.blockCheck (graph ⟨2,0,2,2⟩) 8 {4042} 3840 256 := by decide
end EdgePattern.TreeModelsR3
