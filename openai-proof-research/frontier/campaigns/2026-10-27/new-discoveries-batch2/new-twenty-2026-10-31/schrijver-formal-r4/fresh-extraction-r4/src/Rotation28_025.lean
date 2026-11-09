import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_025_checked : rotationChunkCheck 800 32 #[19,19,19,22,19,19,24,24,26,21,21,21,24,21,26,23,23,26,25,4,4,4,4,4,4,4,4,4,4,4,4,4] #[16,27,37,44,105,115,33,111,21,3,15,26,34,104,22,2,14,23,1,0,1,2,3,4,5,6,7,8,9,10,13,14] = true := by decide
end Schrijver
