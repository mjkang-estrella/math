import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_016_checked : rotationChunkCheck 512 32 #[2,2,2,2,2,2,18,2,2,2,2,20,2,2,2,22,2,2,24,2,26,5,5,5,5,5,5,5,5,5,5,5] #[63,64,65,66,67,68,55,71,72,73,74,46,77,78,79,36,82,83,25,86,13,11,23,34,44,53,61,68,74,79,83,86] = true := by decide
end Schrijver
