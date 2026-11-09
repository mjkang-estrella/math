import Enumeration27Proof
set_option maxRecDepth 20000
example : Schrijver.endMasks 27 12 = 0 :: Schrijver.vertexMasks27.toList := by decide +kernel
