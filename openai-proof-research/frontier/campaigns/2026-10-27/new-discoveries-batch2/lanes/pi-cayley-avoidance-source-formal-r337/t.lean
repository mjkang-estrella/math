def allWords : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, 0 => []
  | n + 1, m + 1 => (allWords n (m + 1)).flatMap
      fun w => (List.range (m + 1)).map fun a => (a + 1) :: w
def packedB (w : List Nat) : Bool := true
def containsB (p w : List Nat) : Bool := true
def dedupNat (l : List Nat) : List Nat := l
def CayAvoiderList (n : Nat) (p : List Nat) : List Nat :=
  dedupNat ((allWords n n).filter (fun W => packedB W && !(containsB p W)))
