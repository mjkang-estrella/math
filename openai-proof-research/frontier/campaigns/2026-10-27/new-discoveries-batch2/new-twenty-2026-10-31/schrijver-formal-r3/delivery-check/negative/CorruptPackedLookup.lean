import TableLinks
import Masks27
set_option maxRecDepth 20000
set_option exponentiation.threshold 200000
example : Schrijver.tableLinkCheck Schrijver.vertexMasks27
    (fun i => Schrijver.maskAt27 i + 1) 0 1 = true := by decide
