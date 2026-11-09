import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_1211_4 : MaskR3.blockCheck (graph ⟨1,2,1,1⟩) 6 {497,993,1489,1926,1985,1986} 1024 256 := by decide
theorem check_1211_5 : MaskR3.blockCheck (graph ⟨1,2,1,1⟩) 6 {497,993,1489,1926,1985,1986} 1280 256 := by decide
theorem check_1211_6 : MaskR3.blockCheck (graph ⟨1,2,1,1⟩) 6 {497,993,1489,1926,1985,1986} 1536 256 := by decide
theorem check_1211_7 : MaskR3.blockCheck (graph ⟨1,2,1,1⟩) 6 {497,993,1489,1926,1985,1986} 1792 256 := by decide
end EdgePattern.TreeModelsR3
