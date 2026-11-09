import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_063_checked : rotationChunkCheck 2016 32 #[23,23,25,8,8,8,8,8,8,8,8,8,11,8,8,8,8,8,8,26,13,13,8,8,8,24,26,15,15,15,1,24] #[27,105,15,9,21,32,42,51,59,66,72,77,79,110,120,129,137,144,150,125,73,151,195,203,210,201,126,66,144,210,265,202] = true := by decide
end Schrijver
