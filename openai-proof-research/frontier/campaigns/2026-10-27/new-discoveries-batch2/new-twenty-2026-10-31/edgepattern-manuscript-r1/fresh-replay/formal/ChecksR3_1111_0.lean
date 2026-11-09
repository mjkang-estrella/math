import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_1111_0 : MaskR3.blockCheck (graph ⟨1,1,1,1⟩) 5 {241,481,721,782,842,902,961,962} 0 256 := by decide
theorem check_1111_1 : MaskR3.blockCheck (graph ⟨1,1,1,1⟩) 5 {241,481,721,782,842,902,961,962} 256 256 := by decide
theorem check_1111_2 : MaskR3.blockCheck (graph ⟨1,1,1,1⟩) 5 {241,481,721,782,842,902,961,962} 512 256 := by decide
theorem check_1111_3 : MaskR3.blockCheck (graph ⟨1,1,1,1⟩) 5 {241,481,721,782,842,902,961,962} 768 256 := by decide
end EdgePattern.TreeModelsR3
