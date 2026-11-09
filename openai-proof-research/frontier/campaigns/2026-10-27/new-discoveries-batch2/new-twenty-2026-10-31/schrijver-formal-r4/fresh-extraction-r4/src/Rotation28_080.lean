import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_080_checked : rotationChunkCheck 2560 32 #[19,5,5,5,21,21,5,23,23,25,10,10,10,10,10,10,10,10,13,10,10,10,10,10,10,15,15,5,5,5,5,17] #[64,142,143,144,56,134,150,47,125,37,10,22,33,43,52,60,67,73,83,111,121,130,138,145,151,78,156,192,193,194,195,72] = true := by decide
end Schrijver
