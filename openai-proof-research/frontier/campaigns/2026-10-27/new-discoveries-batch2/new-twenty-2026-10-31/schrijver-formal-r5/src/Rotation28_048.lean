import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_048_checked : rotationChunkCheck 1536 32 #[10,10,10,18,10,10,10,10,20,10,10,10,22,10,10,24,10,26,15,15,15,15,15,15,18,15,15,15,15,20,20,10] #[106,107,108,82,115,116,117,118,77,125,126,127,71,134,135,64,142,56,10,22,33,43,52,60,83,111,121,130,138,78,156,192] = true := by decide
end Schrijver
