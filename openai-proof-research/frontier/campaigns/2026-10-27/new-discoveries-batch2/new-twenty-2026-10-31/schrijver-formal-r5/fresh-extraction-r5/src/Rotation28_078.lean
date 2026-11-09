import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_078_checked : rotationChunkCheck 2496 32 #[5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,21,5,5,23,5,25,8,8,8] #[32,36,37,38,39,40,41,42,46,47,48,49,50,51,55,56,57,58,59,63,64,65,66,55,71,72,46,77,36,11,23,34] = true := by decide
end Schrijver
