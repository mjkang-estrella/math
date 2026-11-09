import TreeModelsR3
namespace EdgePattern.TreeModelsR3
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem check_1122_0 : MaskR3.blockCheck (graph ⟨1,1,2,2⟩) 7 {3854,3914,3974,4033,4034} 0 256 := by decide
theorem check_1122_1 : MaskR3.blockCheck (graph ⟨1,1,2,2⟩) 7 {3854,3914,3974,4033,4034} 256 256 := by decide
theorem check_1122_2 : MaskR3.blockCheck (graph ⟨1,1,2,2⟩) 7 {3854,3914,3974,4033,4034} 512 256 := by decide
theorem check_1122_3 : MaskR3.blockCheck (graph ⟨1,1,2,2⟩) 7 {3854,3914,3974,4033,4034} 768 256 := by decide
end EdgePattern.TreeModelsR3
