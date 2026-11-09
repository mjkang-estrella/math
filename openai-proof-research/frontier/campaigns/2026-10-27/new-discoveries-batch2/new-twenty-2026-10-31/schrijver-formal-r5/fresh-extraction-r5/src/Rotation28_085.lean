import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_085_checked : rotationChunkCheck 2720 32 #[7,7,7,7,7,7,7,7,7,7,7,7,23,7,25,10,10,10,10,10,10,10,10,13,7,7,7,7,7,7,15,7] #[46,47,48,49,50,55,56,57,58,63,64,65,55,71,46,11,23,34,44,53,61,68,74,86,104,105,106,107,108,109,82,115] = true := by decide
end Schrijver
