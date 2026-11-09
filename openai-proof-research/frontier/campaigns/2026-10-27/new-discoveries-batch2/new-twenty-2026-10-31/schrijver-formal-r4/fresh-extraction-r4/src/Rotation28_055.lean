import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_055_checked : rotationChunkCheck 1760 32 #[16,16,16,16,16,19,19,19,19,22,16,16,24,16,26,21,21,21,24,21,26,23,23,26,25,18,18,18,18,18,18,18] #[26,27,36,37,46,11,23,34,44,86,104,105,82,115,77,10,22,33,83,111,78,9,21,79,8,0,1,2,3,13,14,15] = true := by decide
end Schrijver
