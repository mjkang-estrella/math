import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

#check @Fin.ext
#check @Fin.val_injective
#check @Fin.mk.injEq
#check @Finset.card_insert_of_notMem
#check @Finset.card_singleton
#check @Finset.card_image_of_injective
#check @Finset.eq_of_subset_of_card_le
#check @Finset.mem_filter
#check @Finset.card_univ
#check @Fintype.card_fin
example (m n : Nat) (h : m ≤ n) (j : Fin m) : (Fin.castLE h j).val = j.val := rfl
example (n : Nat) (j : Fin n) : j.val < n := j.isLt
example (n : Nat) (h : n = n + 0) (j : Fin n) (k : Fin n) (h2 : j.val = k.val) : j = k := Fin.ext h2
