import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2002_0 : MaskR3.blockCheck (graph ⟨2,0,0,2⟩) 6 {970,977,984} 0 256 := by decide
theorem check_2002_1 : MaskR3.blockCheck (graph ⟨2,0,0,2⟩) 6 {970,977,984} 256 256 := by decide
theorem check_2002_2 : MaskR3.blockCheck (graph ⟨2,0,0,2⟩) 6 {970,977,984} 512 256 := by decide
theorem check_2002_3 : MaskR3.blockCheck (graph ⟨2,0,0,2⟩) 6 {970,977,984} 768 256 := by decide
end EdgePattern.TreeModelsR3
