import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2022_0 : MaskR3.blockCheck (graph ⟨2,0,2,2⟩) 8 {4042} 0 256 := by decide
theorem check_2022_1 : MaskR3.blockCheck (graph ⟨2,0,2,2⟩) 8 {4042} 256 256 := by decide
theorem check_2022_2 : MaskR3.blockCheck (graph ⟨2,0,2,2⟩) 8 {4042} 512 256 := by decide
theorem check_2022_3 : MaskR3.blockCheck (graph ⟨2,0,2,2⟩) 8 {4042} 768 256 := by decide
end EdgePattern.TreeModelsR3
