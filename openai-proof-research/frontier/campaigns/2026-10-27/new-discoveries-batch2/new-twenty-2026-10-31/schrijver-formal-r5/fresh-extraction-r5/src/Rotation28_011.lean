import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_011_checked : rotationChunkCheck 352 32 #[11,11,25,27,18,18,18,25,27,20,20,25,27,22,22,27,24,27,26,13,13,13,13,13,13,13,16,13,13,13,13,27] #[193,201,143,57,51,129,195,144,58,41,119,145,59,30,108,60,18,61,5,6,18,29,39,48,56,63,61,107,117,126,134,64] = true := by decide
end Schrijver
