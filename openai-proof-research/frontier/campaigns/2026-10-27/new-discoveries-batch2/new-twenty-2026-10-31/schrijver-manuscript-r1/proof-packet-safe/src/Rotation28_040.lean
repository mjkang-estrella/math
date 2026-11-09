import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_040_checked : rotationChunkCheck 1280 32 #[20,20,15,15,22,22,22,24,24,26,17,17,17,17,17,20,17,17,17,22,22,17,24,24,26,19,19,19,19,22,19,19] #[67,145,194,202,59,137,203,50,128,40,7,19,30,40,49,68,108,118,127,60,138,193,51,129,41,6,18,29,39,61,107,117] = true := by decide
end Schrijver
