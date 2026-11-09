import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_050_checked : rotationChunkCheck 1600 32 #[21,21,21,24,21,26,23,23,26,25,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12,12] #[7,19,30,68,108,60,6,18,61,5,0,1,2,3,4,5,6,13,14,15,16,17,18,25,26,27,28,29,36,37,38,39] = true := by decide
end Schrijver
