import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_2111_0 : MaskR3.blockCheck (graph ⟨2,1,1,1⟩) 6 {497,993,1489,1738,1985,1986} 0 256 := by decide
theorem check_2111_1 : MaskR3.blockCheck (graph ⟨2,1,1,1⟩) 6 {497,993,1489,1738,1985,1986} 256 256 := by decide
theorem check_2111_2 : MaskR3.blockCheck (graph ⟨2,1,1,1⟩) 6 {497,993,1489,1738,1985,1986} 512 256 := by decide
theorem check_2111_3 : MaskR3.blockCheck (graph ⟨2,1,1,1⟩) 6 {497,993,1489,1738,1985,1986} 768 256 := by decide
end EdgePattern.TreeModelsR3
