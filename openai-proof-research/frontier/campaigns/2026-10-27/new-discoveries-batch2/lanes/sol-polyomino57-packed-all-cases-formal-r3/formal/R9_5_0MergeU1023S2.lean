import R9_5_0Data
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace R9_5_0
open Polyomino57 Polyomino57.Diagonal Polyomino57.Diagonal.FiniteProof Polyomino57.Diagonal.FiniteProof.Packed
theorem slice1023_2 : (((submasks 10 1023).drop 512).take 256).all (fun a => if a = 0 ∨ a = 1023 then true else bitCheck 30 (table a) (table (1023 ^^^ a)) (table 1023)) = true := by decide
end R9_5_0
