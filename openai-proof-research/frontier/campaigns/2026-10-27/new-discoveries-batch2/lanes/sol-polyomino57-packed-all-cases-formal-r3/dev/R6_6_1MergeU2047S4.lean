import R6_6_1Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R6_6_1
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem slice2047_4 : (((submasks 12 2047).drop 1024).take 256).all (fun a => if a = 0 ∨ a = 2047 then true else bitCheck 24 (table a) (table (2047 ^^^ a)) (table 2047)) = true := by decide
end R6_6_1
