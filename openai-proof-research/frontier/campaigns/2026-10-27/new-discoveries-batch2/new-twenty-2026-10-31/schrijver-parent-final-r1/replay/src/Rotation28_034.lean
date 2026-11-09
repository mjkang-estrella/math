import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_034_checked : rotationChunkCheck 1088 32 #[19,22,19,19,24,24,26,21,21,21,24,21,26,23,23,26,25,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6] #[38,53,106,116,43,121,32,4,16,27,44,105,33,3,15,34,2,0,1,2,3,4,5,6,7,8,9,13,14,15,16,17] = true := by decide
end Schrijver
