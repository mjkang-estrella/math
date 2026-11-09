import BindHQ00
import BindHQ01
import BindHQ02
import BindHQ03
import BindHQ04
import BindHQ05
import BindHQ06
import BindHQ07
import BindHP00
import BindHP01
import BindHP02
import BindHP03
import BindHP04
import BindHP05
import BindHP06
import BindHP07
import BindHP08
import BindHP09
import BindHP10
import BindHP11
import BindHP12
import BindHP13
import BindHP14
namespace TripleCertificates
open FullereneGeometry
theorem DposH : (0:ℝ) < DH := by norm_num [DH]
theorem qbindH (i : Fin 32) : rv (AH i) = (DH:ℝ) • qH i := by
 fin_cases i
 · exact qbH00
 · exact qbH01
 · exact qbH02
 · exact qbH03
 · exact qbH04
 · exact qbH05
 · exact qbH06
 · exact qbH07
 · exact qbH08
 · exact qbH09
 · exact qbH10
 · exact qbH11
 · exact qbH12
 · exact qbH13
 · exact qbH14
 · exact qbH15
 · exact qbH16
 · exact qbH17
 · exact qbH18
 · exact qbH19
 · exact qbH20
 · exact qbH21
 · exact qbH22
 · exact qbH23
 · exact qbH24
 · exact qbH25
 · exact qbH26
 · exact qbH27
 · exact qbH28
 · exact qbH29
 · exact qbH30
 · exact qbH31
theorem pbindH (v : Fin 60) : rp (PH v) = pH v := by
 fin_cases v
 · exact pbH00
 · exact pbH01
 · exact pbH02
 · exact pbH03
 · exact pbH04
 · exact pbH05
 · exact pbH06
 · exact pbH07
 · exact pbH08
 · exact pbH09
 · exact pbH10
 · exact pbH11
 · exact pbH12
 · exact pbH13
 · exact pbH14
 · exact pbH15
 · exact pbH16
 · exact pbH17
 · exact pbH18
 · exact pbH19
 · exact pbH20
 · exact pbH21
 · exact pbH22
 · exact pbH23
 · exact pbH24
 · exact pbH25
 · exact pbH26
 · exact pbH27
 · exact pbH28
 · exact pbH29
 · exact pbH30
 · exact pbH31
 · exact pbH32
 · exact pbH33
 · exact pbH34
 · exact pbH35
 · exact pbH36
 · exact pbH37
 · exact pbH38
 · exact pbH39
 · exact pbH40
 · exact pbH41
 · exact pbH42
 · exact pbH43
 · exact pbH44
 · exact pbH45
 · exact pbH46
 · exact pbH47
 · exact pbH48
 · exact pbH49
 · exact pbH50
 · exact pbH51
 · exact pbH52
 · exact pbH53
 · exact pbH54
 · exact pbH55
 · exact pbH56
 · exact pbH57
 · exact pbH58
 · exact pbH59
end TripleCertificates
