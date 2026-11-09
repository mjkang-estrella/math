import Mathlib.Data.List.Permutation
def l7 : List Nat := [1,2,3,4,5,6,7]
#eval (List.permutations' l7).length
#eval IO.FS.writeFile "perm-order.txt" (String.intercalate "\n" ((List.permutations' l7).map (fun l => String.intercalate "," (l.map toString))) ++ "\n")
#check @List.mem_permutations'
