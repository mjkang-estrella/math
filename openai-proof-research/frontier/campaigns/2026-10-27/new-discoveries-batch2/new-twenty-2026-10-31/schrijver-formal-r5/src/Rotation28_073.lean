import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_073_checked : rotationChunkCheck 2336 32 #[17,3,3,26,19,19,19,26,21,21,21,23,23,25,10,10,10,10,10,10,10,10,13,10,10,10,10,10,10,15,15,10] #[143,209,210,194,57,135,201,195,48,126,192,38,116,27,9,21,32,42,51,59,66,72,79,110,120,129,137,144,150,73,151,195] = true := by decide
end Schrijver
