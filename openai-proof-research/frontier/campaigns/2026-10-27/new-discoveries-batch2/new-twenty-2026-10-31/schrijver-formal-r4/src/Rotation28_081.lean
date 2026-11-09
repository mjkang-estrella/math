import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_081_checked : rotationChunkCheck 2592 32 #[17,5,5,5,19,19,5,5,21,21,21,23,23,25,12,12,12,12,12,12,12,15,12,12,12,12,12,17,17,12,12,12] #[150,201,202,203,65,143,209,210,57,135,201,48,126,38,9,21,32,42,51,59,66,79,110,120,129,137,144,73,151,195,203,210] = true := by decide
end Schrijver
