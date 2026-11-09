import LabelBlocks
import Tree27_000
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 200000
namespace Schrijver
theorem Label27_018_checked : labelRangeCheck 819 maskAt27 Tree27_000.depths 288 16 = true := by decide
end Schrijver
