import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_038_checked : rotationChunkCheck 1216 32 #[11,11,11,11,16,16,6,6,6,6,18,18,6,6,6,20,20,6,6,22,22,22,24,24,26,13,13,13,13,13,13,13] #[130,138,145,151,78,156,192,193,194,195,72,150,201,202,203,65,143,209,210,57,135,201,48,126,38,9,21,32,42,51,59,66] = true := by decide
end Schrijver
