import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_090_checked : rotationChunkCheck 2880 32 #[9,9,9,9,9,9,9,9,9,9,25,12,12,12,12,12,12,12,15,9,9,9,9,9,17,9,9,9,9,19,9,9] #[40,46,47,48,49,55,56,57,63,64,55,11,23,34,44,53,61,68,86,104,105,106,107,108,82,115,116,117,118,77,125,126] = true := by decide
end Schrijver
