import R6_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem slice4094_1 : (((submasks 12 4094).drop 512).take 512).all (fun a => if a = 0 ∨ a = 4094 ∨ 4094 ^^^ a < a then true else bitCheck 24 (table a) (table (4094 ^^^ a)) (table 4094)) = true := by decide
end R6_6_1
