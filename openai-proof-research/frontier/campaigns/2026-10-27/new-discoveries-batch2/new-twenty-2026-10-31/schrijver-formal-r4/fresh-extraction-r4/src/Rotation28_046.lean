import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_046_checked : rotationChunkCheck 1472 32 #[19,19,22,19,19,24,24,26,21,21,21,24,21,26,23,23,26,25,10,10,10,10,10,10,10,10,10,10,10,10,10,10] #[30,40,68,108,118,60,138,51,6,18,29,61,107,52,5,17,53,4,0,1,2,3,4,5,6,7,13,14,15,16,17,18] = true := by decide
end Schrijver
