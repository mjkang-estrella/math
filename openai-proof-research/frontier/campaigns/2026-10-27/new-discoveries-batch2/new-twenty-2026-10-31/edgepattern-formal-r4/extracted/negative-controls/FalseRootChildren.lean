import StructureR4
namespace EdgePattern.TreeModelsR4
example {W : Type} [Fintype W] (T : Rooted W) (hT : TreeFamily T 3 2) :
    (children T T.left T.right).card = 3 := by
  exact (root_children_card T hT).1
end EdgePattern.TreeModelsR4
