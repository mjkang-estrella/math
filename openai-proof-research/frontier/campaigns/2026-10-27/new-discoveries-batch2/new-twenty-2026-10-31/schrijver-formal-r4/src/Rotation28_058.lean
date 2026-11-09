import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_058_checked : rotationChunkCheck 1856 32 #[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,17,1,1,1,1] #[39,40,41,42,43,44,46,47,48,49,50,51,52,53,55,56,57,58,59,60,61,63,64,65,66,67,68,55,71,72,73,74] = true := by decide
end Schrijver
