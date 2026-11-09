import R6_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem slice4087_3 : ((submasks 12 4087).drop 1536).all (fun a => if a = 0 ∨ a = 4087 ∨ 4087 ^^^ a < a then true else bitCheck 24 (table a) (table (4087 ^^^ a)) (table 4087)) = true := by decide
end R6_6_1
