import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_092_checked : rotationChunkCheck 2944 32 #[16,19,16,16,16,21,21,16,23,23,25,18,18,18,18,21,18,18,23,23,25,20,20,20,23,20,25,22,22,25,24,11] #[51,79,110,120,129,73,151,195,66,144,58,8,20,31,41,74,109,119,67,145,59,7,19,30,68,108,60,6,18,61,5,0] = true := by decide
end Schrijver
