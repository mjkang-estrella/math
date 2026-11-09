import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2211_0 : MaskR3.blockCheck (graph ⟨2,2,1,1⟩) 7 {1009,2017,3025,4033,4034} 0 256 := by decide
theorem check_2211_1 : MaskR3.blockCheck (graph ⟨2,2,1,1⟩) 7 {1009,2017,3025,4033,4034} 256 256 := by decide
theorem check_2211_2 : MaskR3.blockCheck (graph ⟨2,2,1,1⟩) 7 {1009,2017,3025,4033,4034} 512 256 := by decide
theorem check_2211_3 : MaskR3.blockCheck (graph ⟨2,2,1,1⟩) 7 {1009,2017,3025,4033,4034} 768 256 := by decide
end EdgePattern.TreeModelsR3
