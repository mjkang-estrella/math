import SmallCertificatesA
import SmallCertificatesB
import SmallCertificatesC
import SmallCertificatesD
import SmallCertificatesE
import SmallCertificatesF
import SmallCertificatesG
import SourceTail
import FiniteBridge

namespace Davis

theorem small_certificates {d : ℕ} (hlo : 5 ≤ d) (hhi : d ≤ 42) :
    certificateCheck d = true := by
  interval_cases d
  · exact certificate_5
  · exact certificate_6
  · exact certificate_7
  · exact certificate_8
  · exact certificate_9
  · exact certificate_10
  · exact certificate_11
  · exact certificate_12
  · exact certificate_13
  · exact certificate_14
  · exact certificate_15
  · exact certificate_16
  · exact certificate_17
  · exact certificate_18
  · exact certificate_19
  · exact certificate_20
  · exact certificate_21
  · exact certificate_22
  · exact certificate_23
  · exact certificate_24
  · exact certificate_25
  · exact certificate_26
  · exact certificate_27
  · exact certificate_28
  · exact certificate_29
  · exact certificate_30
  · exact certificate_31
  · exact certificate_32
  · exact certificate_33
  · exact certificate_34
  · exact certificate_35
  · exact certificate_36
  · exact certificate_37
  · exact certificate_38
  · exact certificate_39
  · exact certificate_40
  · exact certificate_41
  · exact certificate_42


theorem source_strict_bound {d : ℕ} {x : ℝ} (hd : 5 ≤ d)
    (hx : ((d : ℝ) + Real.sqrt (d + 2)) / 2 ≤ x) :
    (199 / 200 : ℝ) * (d - 2) / (2 * x + d - 2) < -remainder d x / P d x := by
  by_cases htail : 43 ≤ d
  · exact source_tail htail hx
  · exact source_bound_of_certificate hd hx (small_certificates hd (by omega))

theorem source_conjecture_319187 : SourceConjecture319187 := by
  intro d x hd hx
  exact (source_strict_bound hd hx).le

end Davis
