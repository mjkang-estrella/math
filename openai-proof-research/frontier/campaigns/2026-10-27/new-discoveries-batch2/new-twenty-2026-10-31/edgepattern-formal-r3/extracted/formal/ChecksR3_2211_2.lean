import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2211_8 : MaskR3.blockCheck (graph ⟨2,2,1,1⟩) 7 {1009,2017,3025,4033,4034} 2048 256 := by decide
theorem check_2211_9 : MaskR3.blockCheck (graph ⟨2,2,1,1⟩) 7 {1009,2017,3025,4033,4034} 2304 256 := by decide
theorem check_2211_10 : MaskR3.blockCheck (graph ⟨2,2,1,1⟩) 7 {1009,2017,3025,4033,4034} 2560 256 := by decide
theorem check_2211_11 : MaskR3.blockCheck (graph ⟨2,2,1,1⟩) 7 {1009,2017,3025,4033,4034} 2816 256 := by decide
end EdgePattern.TreeModelsR3
