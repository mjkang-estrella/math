import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_094_checked : rotationChunkCheck 3008 32 #[14,17,11,11,11,11,19,11,11,11,21,11,11,23,11,25,16,16,16,16,16,19,16,16,16,21,21,11,23,23,25,18] #[61,86,104,105,106,107,82,115,116,117,77,125,126,71,134,64,10,22,33,43,52,83,111,121,130,78,156,192,72,150,65,9] = true := by decide
end Schrijver
