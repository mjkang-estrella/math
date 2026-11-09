import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_0220_0 : MaskR3.blockCheck (graph ⟨0,2,2,0⟩) 6 {966,993,996} 0 256 := by decide
theorem check_0220_1 : MaskR3.blockCheck (graph ⟨0,2,2,0⟩) 6 {966,993,996} 256 256 := by decide
theorem check_0220_2 : MaskR3.blockCheck (graph ⟨0,2,2,0⟩) 6 {966,993,996} 512 256 := by decide
theorem check_0220_3 : MaskR3.blockCheck (graph ⟨0,2,2,0⟩) 6 {966,993,996} 768 256 := by decide
end EdgePattern.TreeModelsR3
