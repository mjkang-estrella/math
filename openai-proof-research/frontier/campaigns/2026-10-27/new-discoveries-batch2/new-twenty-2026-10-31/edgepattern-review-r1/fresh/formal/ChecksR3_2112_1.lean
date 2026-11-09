import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2112_4 : MaskR3.blockCheck (graph ⟨2,1,1,2⟩) 7 {3537,3786,4033,4034} 1024 256 := by decide
theorem check_2112_5 : MaskR3.blockCheck (graph ⟨2,1,1,2⟩) 7 {3537,3786,4033,4034} 1280 256 := by decide
theorem check_2112_6 : MaskR3.blockCheck (graph ⟨2,1,1,2⟩) 7 {3537,3786,4033,4034} 1536 256 := by decide
theorem check_2112_7 : MaskR3.blockCheck (graph ⟨2,1,1,2⟩) 7 {3537,3786,4033,4034} 1792 256 := by decide
end EdgePattern.TreeModelsR3
