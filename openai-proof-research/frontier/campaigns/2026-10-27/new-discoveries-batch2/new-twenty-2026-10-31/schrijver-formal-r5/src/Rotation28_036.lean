import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_036_checked : rotationChunkCheck 1152 32 #[6,6,22,6,6,24,6,26,9,9,9,9,9,9,9,9,9,12,6,6,6,6,6,6,6,14,6,6,6,6,6,6] #[65,66,55,71,72,46,77,36,11,23,34,44,53,61,68,74,79,86,104,105,106,107,108,109,110,82,115,116,117,118,119,120] = true := by decide
end Schrijver
