import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_0022_0 : MaskR3.blockCheck (graph ⟨0,0,2,2⟩) 7 {974} 0 256 := by decide
theorem check_0022_1 : MaskR3.blockCheck (graph ⟨0,0,2,2⟩) 7 {974} 256 256 := by decide
theorem check_0022_2 : MaskR3.blockCheck (graph ⟨0,0,2,2⟩) 7 {974} 512 256 := by decide
theorem check_0022_3 : MaskR3.blockCheck (graph ⟨0,0,2,2⟩) 7 {974} 768 256 := by decide
end EdgePattern.TreeModelsR3
