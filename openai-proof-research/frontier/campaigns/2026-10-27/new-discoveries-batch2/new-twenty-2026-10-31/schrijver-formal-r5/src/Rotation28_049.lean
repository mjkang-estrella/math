import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_049_checked : rotationChunkCheck 1568 32 #[10,22,22,10,24,24,26,17,17,17,17,17,20,17,17,17,22,22,17,24,24,26,19,19,19,19,22,19,19,24,24,26] #[193,72,150,201,65,143,57,9,21,32,42,51,79,110,120,129,73,151,195,66,144,58,8,20,31,41,74,109,119,67,145,59] = true := by decide
end Schrijver
