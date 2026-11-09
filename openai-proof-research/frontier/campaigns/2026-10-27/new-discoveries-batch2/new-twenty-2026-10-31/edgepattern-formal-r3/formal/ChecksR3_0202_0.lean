import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_0202_0 : MaskR3.blockCheck (graph ⟨0,2,0,2⟩) 6 {966,977,980} 0 256 := by decide
theorem check_0202_1 : MaskR3.blockCheck (graph ⟨0,2,0,2⟩) 6 {966,977,980} 256 256 := by decide
theorem check_0202_2 : MaskR3.blockCheck (graph ⟨0,2,0,2⟩) 6 {966,977,980} 512 256 := by decide
theorem check_0202_3 : MaskR3.blockCheck (graph ⟨0,2,0,2⟩) 6 {966,977,980} 768 256 := by decide
end EdgePattern.TreeModelsR3
