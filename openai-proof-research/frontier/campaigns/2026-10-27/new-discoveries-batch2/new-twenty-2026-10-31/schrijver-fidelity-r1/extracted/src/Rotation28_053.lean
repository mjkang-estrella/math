import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_053_checked : rotationChunkCheck 1696 32 #[14,14,14,14,14,14,14,14,14,14,14,14,14,14,14,14,14,14,14,17,17,17,17,17,20,14,14,14,22,14,14,24] #[2,3,4,5,13,14,15,16,17,25,26,27,28,36,37,38,46,47,55,11,23,34,44,53,86,104,105,106,82,115,116,77] = true := by decide
end Schrijver
