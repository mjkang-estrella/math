import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2211_4 : MaskR3.blockCheck (graph ⟨2,2,1,1⟩) 7 {1009,2017,3025,4033,4034} 1024 256 := by decide
theorem check_2211_5 : MaskR3.blockCheck (graph ⟨2,2,1,1⟩) 7 {1009,2017,3025,4033,4034} 1280 256 := by decide
theorem check_2211_6 : MaskR3.blockCheck (graph ⟨2,2,1,1⟩) 7 {1009,2017,3025,4033,4034} 1536 256 := by decide
theorem check_2211_7 : MaskR3.blockCheck (graph ⟨2,2,1,1⟩) 7 {1009,2017,3025,4033,4034} 1792 256 := by decide
end EdgePattern.TreeModelsR3
