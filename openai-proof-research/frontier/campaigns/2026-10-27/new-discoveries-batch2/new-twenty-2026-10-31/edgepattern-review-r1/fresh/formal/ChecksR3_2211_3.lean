import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2211_12 : MaskR3.blockCheck (graph ⟨2,2,1,1⟩) 7 {1009,2017,3025,4033,4034} 3072 256 := by decide
theorem check_2211_13 : MaskR3.blockCheck (graph ⟨2,2,1,1⟩) 7 {1009,2017,3025,4033,4034} 3328 256 := by decide
theorem check_2211_14 : MaskR3.blockCheck (graph ⟨2,2,1,1⟩) 7 {1009,2017,3025,4033,4034} 3584 256 := by decide
theorem check_2211_15 : MaskR3.blockCheck (graph ⟨2,2,1,1⟩) 7 {1009,2017,3025,4033,4034} 3840 256 := by decide
end EdgePattern.TreeModelsR3
