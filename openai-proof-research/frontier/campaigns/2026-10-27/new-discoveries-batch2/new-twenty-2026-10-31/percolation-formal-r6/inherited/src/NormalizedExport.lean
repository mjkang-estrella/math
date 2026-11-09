import Normalize
open Percolation
private def numberVar : SatVar → Nat
  | .a p => p.val+1
  | .x p => p.val+32
  | .i p => p.val+63
  | .j p => p.val+94
  | .b v p => 125+31*v.val+p.val
#eval do
  IO.println "BEGIN_DIMACS"
  IO.println s!"p cnf 1085 {normalizedCNF5.length}"
  for c in normalizedCNF5 do
    IO.println (String.intercalate " " (c.map fun (z : SatVar × Bool) =>
      (if z.2 then "-" else "") ++ toString (numberVar z.1)) ++ " 0")
  IO.println "END_DIMACS"
