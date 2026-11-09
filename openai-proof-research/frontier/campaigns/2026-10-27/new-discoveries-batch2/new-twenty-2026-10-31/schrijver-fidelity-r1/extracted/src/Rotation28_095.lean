import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_095_checked : rotationChunkCheck 3040 32 #[18,18,18,21,18,18,23,23,25,20,20,20,23,20,25,22,22,25,24,13,13,13,13,13,13,13,13,13,13,13,13,13] #[21,32,42,79,110,120,73,151,66,8,20,31,74,109,67,7,19,68,6,0,1,2,3,4,5,13,14,15,16,17,25,26] = true := by decide
end Schrijver
