import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_066_checked : rotationChunkCheck 2112 32 #[12,17,17,12,12,26,19,19,19,26,21,21,26,23,23,25,14,14,14,14,14,14,17,14,14,14,14,19,19,14,26,21] #[142,60,138,193,201,143,51,129,195,144,41,119,145,30,108,18,6,18,29,39,48,56,61,107,117,126,134,52,130,192,150,42] = true := by decide
end Schrijver
