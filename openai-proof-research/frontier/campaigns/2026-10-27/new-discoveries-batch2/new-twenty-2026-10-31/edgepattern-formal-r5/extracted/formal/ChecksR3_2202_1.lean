import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2202_4 : MaskR3.blockCheck (graph ⟨2,2,0,2⟩) 8 {4049} 1024 256 := by decide
theorem check_2202_5 : MaskR3.blockCheck (graph ⟨2,2,0,2⟩) 8 {4049} 1280 256 := by decide
theorem check_2202_6 : MaskR3.blockCheck (graph ⟨2,2,0,2⟩) 8 {4049} 1536 256 := by decide
theorem check_2202_7 : MaskR3.blockCheck (graph ⟨2,2,0,2⟩) 8 {4049} 1792 256 := by decide
end EdgePattern.TreeModelsR3
