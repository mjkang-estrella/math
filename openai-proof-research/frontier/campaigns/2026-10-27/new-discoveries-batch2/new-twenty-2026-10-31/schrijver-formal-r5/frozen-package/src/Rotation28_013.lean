import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_013_checked : rotationChunkCheck 416 32 #[27,24,27,26,17,17,17,17,17,20,17,17,27,22,22,27,24,27,26,19,19,19,19,22,19,27,24,27,26,21,21,21] #[73,20,74,7,4,16,27,37,46,44,105,115,77,33,111,78,21,79,8,3,15,26,36,34,104,82,22,83,9,2,14,25] = true := by decide
end Schrijver
