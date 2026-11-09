import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_033_checked : rotationChunkCheck 1056 32 #[15,15,15,15,20,20,15,15,22,22,22,24,24,26,17,17,17,17,17,20,17,17,17,22,22,17,24,24,26,19,19,19] #[108,118,127,135,60,138,193,201,51,129,195,41,119,30,6,18,29,39,48,61,107,117,126,52,130,192,42,120,31,5,17,28] = true := by decide
end Schrijver
