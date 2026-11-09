import RotationCheck
namespace Schrijver
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
set_option exponentiation.threshold 100000
theorem Rotation28_083_checked : rotationChunkCheck 2656 32 #[16,16,16,16,19,16,16,16,21,21,16,23,23,25,18,18,18,18,21,18,18,23,23,25,20,20,20,23,20,25,22,22] #[19,30,40,49,68,108,118,127,60,138,193,51,129,41,6,18,29,39,61,107,117,52,130,42,5,17,28,53,106,43,4,16] = true := by decide
end Schrijver
