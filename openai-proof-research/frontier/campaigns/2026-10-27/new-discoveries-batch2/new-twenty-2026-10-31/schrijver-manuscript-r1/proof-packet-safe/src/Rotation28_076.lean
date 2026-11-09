import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_076_checked : rotationChunkCheck 2432 32 #[23,23,25,16,16,16,16,16,19,16,16,16,21,21,16,23,23,25,18,18,18,18,21,18,18,23,23,25,20,20,20,23] #[41,119,30,6,18,29,39,48,61,107,117,126,52,130,192,42,120,31,5,17,28,38,53,106,116,43,121,32,4,16,27,44] = true := by decide
end Schrijver
