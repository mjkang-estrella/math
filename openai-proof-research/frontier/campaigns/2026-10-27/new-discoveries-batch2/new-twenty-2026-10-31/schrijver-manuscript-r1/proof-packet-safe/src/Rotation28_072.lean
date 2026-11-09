import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_072_checked : rotationChunkCheck 2304 32 #[25,8,8,8,8,8,8,8,8,8,11,8,8,8,8,8,8,8,13,13,3,3,3,3,26,15,15,3,3,3,26,17] #[26,10,22,33,43,52,60,67,73,78,83,111,121,130,138,145,151,156,78,156,192,193,194,195,192,72,150,201,202,203,193,65] = true := by decide
end Schrijver
