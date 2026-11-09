import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_068_checked : rotationChunkCheck 2176 32 #[20,23,20,25,22,22,25,24,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3,3] #[26,34,104,22,2,14,23,1,0,1,2,3,4,5,6,7,8,9,10,13,14,15,16,17,18,19,20,21,22,25,26,27] = true := by decide
end Schrijver
