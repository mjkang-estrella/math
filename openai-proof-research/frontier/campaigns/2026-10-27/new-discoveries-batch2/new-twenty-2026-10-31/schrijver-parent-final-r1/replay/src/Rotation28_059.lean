import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_059_checked : rotationChunkCheck 1888 32 #[19,1,1,1,21,1,1,23,1,25,4,4,4,4,4,4,4,4,4,4,4,7,1,1,1,1,1,1,1,1,26,9] #[46,77,78,79,36,82,83,25,86,13,11,23,34,44,53,61,68,74,79,83,86,86,104,105,106,107,108,109,110,111,104,82] = true := by decide
end Schrijver
