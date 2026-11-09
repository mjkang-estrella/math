import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_041_checked : rotationChunkCheck 1312 32 #[24,24,26,21,21,21,24,21,26,23,23,26,25,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8,8] #[52,130,42,5,17,28,53,106,43,4,16,44,3,0,1,2,3,4,5,6,7,8,13,14,15,16,17,18,19,20,25,26] = true := by decide
end Schrijver
