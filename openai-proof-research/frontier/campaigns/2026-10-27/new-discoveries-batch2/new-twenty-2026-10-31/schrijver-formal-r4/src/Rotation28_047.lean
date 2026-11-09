import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_047_checked : rotationChunkCheck 1504 32 #[10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,10,26,13,13,13,13,13,13,13,16,10,10] #[19,25,26,27,28,29,30,36,37,38,39,40,46,47,48,49,55,56,57,63,64,55,11,23,34,44,53,61,68,86,104,105] = true := by decide
end Schrijver
