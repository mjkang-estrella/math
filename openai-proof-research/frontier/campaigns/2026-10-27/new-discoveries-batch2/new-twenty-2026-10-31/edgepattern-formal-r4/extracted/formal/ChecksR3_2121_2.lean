import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2121_8 : MaskR3.blockCheck (graph ⟨2,1,2,1⟩) 7 {2017,3786,4033,4034} 2048 256 := by decide
theorem check_2121_9 : MaskR3.blockCheck (graph ⟨2,1,2,1⟩) 7 {2017,3786,4033,4034} 2304 256 := by decide
theorem check_2121_10 : MaskR3.blockCheck (graph ⟨2,1,2,1⟩) 7 {2017,3786,4033,4034} 2560 256 := by decide
theorem check_2121_11 : MaskR3.blockCheck (graph ⟨2,1,2,1⟩) 7 {2017,3786,4033,4034} 2816 256 := by decide
end EdgePattern.TreeModelsR3
