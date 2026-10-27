import FiniteCheck

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Davis

theorem certificate_41 : certificateCheck 41 = true := by decide +kernel

theorem certificate_42 : certificateCheck 42 = true := by decide +kernel

end Davis
