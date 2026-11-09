import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_062_checked : rotationChunkCheck 1984 32 #[11,1,1,1,1,24,26,13,13,1,1,1,24,26,15,15,1,1,24,26,17,17,17,24,26,19,19,19,26,21,21,26] #[156,192,193,194,195,192,116,72,150,201,202,203,193,117,65,143,209,210,194,118,57,135,201,195,119,48,126,192,120,38,116,121] = true := by decide
end Schrijver
