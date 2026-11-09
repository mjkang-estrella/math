import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_027_checked : rotationChunkCheck 864 32 #[4,4,4,4,4,4,4,4,4,4,4,20,4,4,4,22,4,4,24,4,26,7,7,7,7,7,7,7,7,7,7,10] #[55,56,57,58,59,60,63,64,65,66,67,55,71,72,73,46,77,78,36,82,25,11,23,34,44,53,61,68,74,79,83,86] = true := by decide
end Schrijver
