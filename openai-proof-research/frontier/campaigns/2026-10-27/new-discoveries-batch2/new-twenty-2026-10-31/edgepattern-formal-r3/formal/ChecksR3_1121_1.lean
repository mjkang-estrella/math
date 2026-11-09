import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_1121_4 : MaskR3.blockCheck (graph ⟨1,1,2,1⟩) 6 {993,1806,1866,1926,1985,1986} 1024 256 := by decide
theorem check_1121_5 : MaskR3.blockCheck (graph ⟨1,1,2,1⟩) 6 {993,1806,1866,1926,1985,1986} 1280 256 := by decide
theorem check_1121_6 : MaskR3.blockCheck (graph ⟨1,1,2,1⟩) 6 {993,1806,1866,1926,1985,1986} 1536 256 := by decide
theorem check_1121_7 : MaskR3.blockCheck (graph ⟨1,1,2,1⟩) 6 {993,1806,1866,1926,1985,1986} 1792 256 := by decide
end EdgePattern.TreeModelsR3
