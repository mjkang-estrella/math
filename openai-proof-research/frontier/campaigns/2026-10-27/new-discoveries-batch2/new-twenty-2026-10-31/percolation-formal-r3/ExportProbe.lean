import PG5CNF
open Percolation
private def enc : SatVar → Nat
  | .a p => p.val+1
  | .x p => p.val+32
  | .i p => p.val+63
  | .j p => p.val+94
  | .b v p => 125+31*v.val+p.val
#eval do
  IO.println "BEGIN_DIMACS"
  IO.println s!"p cnf 1085 {inputCNF5.length}"
  for c in inputCNF5 do
    IO.println (String.intercalate " " (c.map fun (z : SatVar × Bool) => (if z.2 then "-" else "") ++ toString (enc z.1)) ++ " 0")
  IO.println "END_DIMACS"
