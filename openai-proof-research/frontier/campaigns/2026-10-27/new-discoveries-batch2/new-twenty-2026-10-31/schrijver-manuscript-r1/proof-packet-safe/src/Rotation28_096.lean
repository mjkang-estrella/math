import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_096_checked : rotationChunkCheck 3072 32 #[13,13,13,13,13,13,13,13,16,16,16,16,16,19,13,13,13,21,13,13,23,13,25,18,18,18,18,21,18,18,23,23] #[27,28,36,37,38,46,47,55,11,23,34,44,53,86,104,105,106,82,115,116,77,125,71,10,22,33,43,83,111,121,78,156] = true := by decide
end Schrijver
