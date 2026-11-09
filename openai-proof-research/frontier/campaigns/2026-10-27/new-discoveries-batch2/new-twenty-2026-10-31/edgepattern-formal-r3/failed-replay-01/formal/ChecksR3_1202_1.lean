import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_1202_4 : MaskR3.blockCheck (graph ⟨1,2,0,2⟩) 7 {2001} 1024 256 := by decide
theorem check_1202_5 : MaskR3.blockCheck (graph ⟨1,2,0,2⟩) 7 {2001} 1280 256 := by decide
theorem check_1202_6 : MaskR3.blockCheck (graph ⟨1,2,0,2⟩) 7 {2001} 1536 256 := by decide
theorem check_1202_7 : MaskR3.blockCheck (graph ⟨1,2,0,2⟩) 7 {2001} 1792 256 := by decide
end EdgePattern.TreeModelsR3
