import TableLinks
import Masks27
set_option maxRecDepth 20000
set_option exponentiation.threshold 200000
set_option maxHeartbeats 10000000
namespace Schrijver
theorem Link27_000_checked : tableLinkCheck vertexMasks27 maskAt27 0 128 = true := by decide
end Schrijver
