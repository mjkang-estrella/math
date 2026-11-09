import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_002_checked : rotationChunkCheck 64 32 #[0,0,0,0,0,27,16,0,0,0,0,27,18,0,0,0,27,20,0,0,27,22,0,27,24,27,26,3,3,3,3,3] #[64,65,66,67,68,6,55,71,72,73,74,7,46,77,78,79,8,36,82,83,9,25,86,10,13,11,0,11,23,34,44,53] = true := by decide
end Schrijver
