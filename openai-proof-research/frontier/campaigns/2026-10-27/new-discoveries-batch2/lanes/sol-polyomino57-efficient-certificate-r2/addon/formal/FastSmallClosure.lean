import SortedCertificate
import SmallClosure
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57
theorem fastSmallClosure0 : arrayFastClosureCheck smallLayer0 smallLayer1 smallChoices0 = true := by decide
theorem fastSmallClosure1 : arrayFastClosureCheck smallLayer1 smallLayer2 smallChoices1 = true := by decide
theorem fastSmallClosure2 : arrayFastClosureCheck smallLayer2 smallLayer3 smallChoices2 = true := by decide
theorem fastSmallClosure3 : arrayFastClosureCheck smallLayer3 smallLayer4 smallChoices3 = true := by decide
end Polyomino57
