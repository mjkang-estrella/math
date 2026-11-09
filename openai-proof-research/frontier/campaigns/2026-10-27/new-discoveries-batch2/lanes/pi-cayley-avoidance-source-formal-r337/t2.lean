def allWords : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, 0 => []
  | n + 1, m + 1 => (allWords n (m + 1)).flatMap
      fun w => (List.range (m + 1)).map fun a => (a + 1) :: w
#check (allWords 3 3)
#check @List.filter
def packedB (w : List Nat) : Bool := true
#check fun (W : List Nat) => packedB W
#check ((allWords 3 3) : List (List Nat))
