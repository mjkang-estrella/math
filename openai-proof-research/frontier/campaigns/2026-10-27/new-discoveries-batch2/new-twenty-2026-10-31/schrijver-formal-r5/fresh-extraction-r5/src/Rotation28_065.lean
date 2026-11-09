import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_065_checked : rotationChunkCheck 2080 32 #[15,10,10,10,26,17,17,17,24,26,19,19,19,26,21,21,26,23,23,25,12,12,12,12,12,12,12,15,12,12,12,12] #[145,194,202,209,135,59,137,203,210,136,50,128,194,137,40,118,138,29,107,17,7,19,30,40,49,57,64,68,108,118,127,135] = true := by decide
end Schrijver
