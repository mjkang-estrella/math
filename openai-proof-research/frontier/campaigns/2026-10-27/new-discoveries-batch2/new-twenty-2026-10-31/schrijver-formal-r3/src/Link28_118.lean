import TableLinks
import Masks28
set_option maxRecDepth 20000
set_option exponentiation.threshold 200000
set_option maxHeartbeats 10000000
namespace Schrijver
theorem Link28_118_checked : tableLinkCheck (vertexMasks28.toArray) maskAt28 2880 16 = true := by decide
end Schrijver
