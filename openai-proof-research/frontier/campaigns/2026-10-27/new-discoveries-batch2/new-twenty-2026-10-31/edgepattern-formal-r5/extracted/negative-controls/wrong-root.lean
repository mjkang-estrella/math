import EndpointR5
open EdgePattern EdgePattern.TreeModelsR5
example {W : Type} [Fintype W] (T : Rooted W) (B : Branches T) (hT : TreeFamily T 3 2) :
  vertexEquiv T B hT (TreeModelsR3.pattern (branchCounts T B hT)).left = T.right := by
  exact vertexEquiv_left T B hT
