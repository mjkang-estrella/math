import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_097_checked : rotationChunkCheck 3104 32 #[25,20,20,20,23,20,25,22,22,25,24,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,18,18,18,18,21,15] #[72,9,21,32,79,110,73,8,20,74,7,0,1,2,3,4,13,14,15,16,25,26,27,36,37,46,11,23,34,44,86,104] = true := by decide
end Schrijver
