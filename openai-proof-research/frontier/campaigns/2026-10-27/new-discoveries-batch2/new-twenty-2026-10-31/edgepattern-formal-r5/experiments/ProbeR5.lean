import NumberingR5
open EdgePattern EdgePattern.TreeModelsR5
example {W : Type} [Fintype W] (T : Rooted W) (B : Branches T) (hT : TreeFamily T 3 2) (i : Fin 4) :
    (number T B hT (.inr (.inl i))).val = 2 + i.val := by
  rfl
example {W : Type} [Fintype W] (T : Rooted W) (B : Branches T) (hT : TreeFamily T 3 2) (i : Fin 2) :
    (number T B hT (.inl i)).val = i.val := by
  rfl
