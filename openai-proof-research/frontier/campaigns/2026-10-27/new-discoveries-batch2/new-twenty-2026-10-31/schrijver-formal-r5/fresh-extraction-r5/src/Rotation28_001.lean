import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_001_checked : rotationChunkCheck 32 32 #[0,0,0,27,0,0,0,0,0,0,0,0,0,27,0,0,0,0,0,0,0,0,27,0,0,0,0,0,0,0,27,0] #[32,33,34,2,36,37,38,39,40,41,42,43,44,3,46,47,48,49,50,51,52,53,4,55,56,57,58,59,60,61,5,63] = true := by decide
end Schrijver
