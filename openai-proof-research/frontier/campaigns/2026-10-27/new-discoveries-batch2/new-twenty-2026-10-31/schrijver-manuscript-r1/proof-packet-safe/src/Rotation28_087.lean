import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_087_checked : rotationChunkCheck 2784 32 #[17,17,7,7,7,19,19,7,7,21,21,7,23,23,25,14,14,14,14,14,14,17,14,14,14,14,19,19,14,14,21,21] #[78,156,192,193,194,72,150,201,202,65,143,209,57,135,48,9,21,32,42,51,59,79,110,120,129,137,73,151,195,203,66,144] = true := by decide
end Schrijver
