import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_020_checked : rotationChunkCheck 640 32 #[18,18,25,27,20,20,20,27,22,22,27,24,24,26,9,9,9,9,9,9,9,9,9,12,9,9,9,9,9,9,27,14] #[135,201,195,119,48,126,192,120,38,116,121,27,105,15,9,21,32,42,51,59,66,72,77,79,110,120,129,137,144,150,125,73] = true := by decide
end Schrijver
