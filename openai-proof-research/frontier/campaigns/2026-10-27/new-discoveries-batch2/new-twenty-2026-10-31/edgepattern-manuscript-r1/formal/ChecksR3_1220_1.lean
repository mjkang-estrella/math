import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_1220_4 : MaskR3.blockCheck (graph ⟨1,2,2,0⟩) 7 {2017} 1024 256 := by decide
theorem check_1220_5 : MaskR3.blockCheck (graph ⟨1,2,2,0⟩) 7 {2017} 1280 256 := by decide
theorem check_1220_6 : MaskR3.blockCheck (graph ⟨1,2,2,0⟩) 7 {2017} 1536 256 := by decide
theorem check_1220_7 : MaskR3.blockCheck (graph ⟨1,2,2,0⟩) 7 {2017} 1792 256 := by decide
end EdgePattern.TreeModelsR3
