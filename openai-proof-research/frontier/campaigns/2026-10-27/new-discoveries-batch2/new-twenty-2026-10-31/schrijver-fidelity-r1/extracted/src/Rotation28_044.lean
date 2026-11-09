import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_044_checked : rotationChunkCheck 1408 32 #[13,13,13,13,13,16,13,13,13,13,13,18,18,8,8,8,20,20,8,8,22,22,8,24,24,26,15,15,15,15,15,15] #[33,43,52,60,67,83,111,121,130,138,145,78,156,192,193,194,72,150,201,202,65,143,209,57,135,48,9,21,32,42,51,59] = true := by decide
end Schrijver
