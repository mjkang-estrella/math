import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_070_checked : rotationChunkCheck 2240 32 #[19,3,3,3,21,3,3,23,3,25,6,6,6,6,6,6,6,6,6,6,9,3,3,3,3,3,3,3,3,11,3,3] #[55,71,72,73,46,77,78,36,82,25,11,23,34,44,53,61,68,74,79,83,86,104,105,106,107,108,109,110,111,82,115,116] = true := by decide
end Schrijver
