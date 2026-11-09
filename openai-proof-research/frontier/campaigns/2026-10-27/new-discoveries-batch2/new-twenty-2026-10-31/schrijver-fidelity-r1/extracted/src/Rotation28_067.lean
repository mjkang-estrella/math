import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_067_checked : rotationChunkCheck 2144 32 #[21,26,23,23,25,16,16,16,16,16,19,16,16,16,21,21,26,23,23,25,18,18,18,18,21,18,18,23,23,25,20,20] #[120,151,31,109,19,5,17,28,38,47,53,106,116,125,43,121,156,32,110,20,4,16,27,37,44,105,115,33,111,21,3,15] = true := by decide
end Schrijver
