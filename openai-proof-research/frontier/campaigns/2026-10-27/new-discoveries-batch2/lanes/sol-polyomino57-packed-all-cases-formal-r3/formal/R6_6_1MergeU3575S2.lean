import R6_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem slice3575_2 : (((submasks 12 3575).drop 512).take 256).all (fun a => if a = 0 ∨ a = 3575 then true else bitCheck 24 (table a) (table (3575 ^^^ a)) (table 3575)) = true := by decide
end R6_6_1
