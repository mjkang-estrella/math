import FiniteCheck

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Davis

theorem certificate_11 : certificateCheck 11 = true := by decide +kernel

theorem certificate_12 : certificateCheck 12 = true := by decide +kernel

theorem certificate_13 : certificateCheck 13 = true := by decide +kernel

theorem certificate_14 : certificateCheck 14 = true := by decide +kernel

theorem certificate_15 : certificateCheck 15 = true := by decide +kernel

theorem certificate_16 : certificateCheck 16 = true := by decide +kernel

end Davis
