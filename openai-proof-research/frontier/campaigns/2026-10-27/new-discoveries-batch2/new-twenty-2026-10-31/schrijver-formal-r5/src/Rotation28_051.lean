import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_051_checked : rotationChunkCheck 1632 32 #[12,12,12,12,12,12,15,15,15,15,15,15,18,12,12,12,12,20,12,12,12,22,12,12,24,12,26,17,17,17,17,17] #[46,47,48,55,56,63,11,23,34,44,53,61,86,104,105,106,107,82,115,116,117,77,125,126,71,134,64,10,22,33,43,52] = true := by decide
end Schrijver
