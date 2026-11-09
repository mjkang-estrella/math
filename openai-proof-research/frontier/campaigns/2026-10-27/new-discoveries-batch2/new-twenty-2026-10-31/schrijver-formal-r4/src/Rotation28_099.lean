import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_099_checked : rotationChunkCheck 3168 17 #[25,24,19,19,19,19,19,19,22,22,25,24,21,21,21,24,23] #[83,9,0,1,2,13,14,25,11,23,86,10,0,1,13,11,0] = true := by decide
end Schrijver
