import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_1112_0 : MaskR3.blockCheck (graph ⟨1,1,1,2⟩) 6 {1745,1806,1866,1926,1985,1986} 0 256 := by decide
theorem check_1112_1 : MaskR3.blockCheck (graph ⟨1,1,1,2⟩) 6 {1745,1806,1866,1926,1985,1986} 256 256 := by decide
theorem check_1112_2 : MaskR3.blockCheck (graph ⟨1,1,1,2⟩) 6 {1745,1806,1866,1926,1985,1986} 512 256 := by decide
theorem check_1112_3 : MaskR3.blockCheck (graph ⟨1,1,1,2⟩) 6 {1745,1806,1866,1926,1985,1986} 768 256 := by decide
end EdgePattern.TreeModelsR3
