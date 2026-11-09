import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_1102_0 : MaskR3.blockCheck (graph ⟨1,1,0,2⟩) 6 {977} 0 256 := by decide
theorem check_1102_1 : MaskR3.blockCheck (graph ⟨1,1,0,2⟩) 6 {977} 256 256 := by decide
theorem check_1102_2 : MaskR3.blockCheck (graph ⟨1,1,0,2⟩) 6 {977} 512 256 := by decide
theorem check_1102_3 : MaskR3.blockCheck (graph ⟨1,1,0,2⟩) 6 {977} 768 256 := by decide
end EdgePattern.TreeModelsR3
