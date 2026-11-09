import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_1212_12 : MaskR3.blockCheck (graph ⟨1,2,1,2⟩) 7 {3537,3974,4033,4034} 3072 256 := by decide
theorem check_1212_13 : MaskR3.blockCheck (graph ⟨1,2,1,2⟩) 7 {3537,3974,4033,4034} 3328 256 := by decide
theorem check_1212_14 : MaskR3.blockCheck (graph ⟨1,2,1,2⟩) 7 {3537,3974,4033,4034} 3584 256 := by decide
theorem check_1212_15 : MaskR3.blockCheck (graph ⟨1,2,1,2⟩) 7 {3537,3974,4033,4034} 3840 256 := by decide
end EdgePattern.TreeModelsR3
