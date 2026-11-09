import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_024_checked : rotationChunkCheck 768 32 #[15,18,15,15,15,15,20,20,15,27,22,22,27,24,24,26,17,17,17,17,17,20,17,17,17,22,22,27,24,24,26,19] #[56,61,107,117,126,134,52,130,192,150,42,120,151,31,109,19,5,17,28,38,47,53,106,116,125,43,121,156,32,110,20,4] = true := by decide
end Schrijver
