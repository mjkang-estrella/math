import FiniteCheck

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Davis

theorem certificate_5 : certificateCheck 5 = true := by decide +kernel

theorem certificate_6 : certificateCheck 6 = true := by decide +kernel

theorem certificate_7 : certificateCheck 7 = true := by decide +kernel

theorem certificate_8 : certificateCheck 8 = true := by decide +kernel

theorem certificate_9 : certificateCheck 9 = true := by decide +kernel

theorem certificate_10 : certificateCheck 10 = true := by decide +kernel

end Davis
