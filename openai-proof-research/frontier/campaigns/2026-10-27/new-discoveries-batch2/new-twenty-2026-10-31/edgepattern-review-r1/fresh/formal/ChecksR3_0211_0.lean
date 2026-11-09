import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_0211_0 : MaskR3.blockCheck (graph ⟨0,2,1,1⟩) 6 {966} 0 256 := by decide
theorem check_0211_1 : MaskR3.blockCheck (graph ⟨0,2,1,1⟩) 6 {966} 256 256 := by decide
theorem check_0211_2 : MaskR3.blockCheck (graph ⟨0,2,1,1⟩) 6 {966} 512 256 := by decide
theorem check_0211_3 : MaskR3.blockCheck (graph ⟨0,2,1,1⟩) 6 {966} 768 256 := by decide
end EdgePattern.TreeModelsR3
