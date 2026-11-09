import BindGQ00
import BindGQ01
import BindGQ02
import BindGQ03
import BindGQ04
import BindGQ05
import BindGQ06
import BindGQ07
import BindGP00
import BindGP01
import BindGP02
import BindGP03
import BindGP04
import BindGP05
import BindGP06
import BindGP07
import BindGP08
import BindGP09
import BindGP10
import BindGP11
import BindGP12
import BindGP13
import BindGP14
namespace TripleCertificates
open FullereneGeometry
theorem DposG : (0:ℝ) < DG := by norm_num [DG]
theorem qbindG (i : Fin 32) : rv (AG i) = (DG:ℝ) • qG i := by
 fin_cases i
 · exact qbG00
 · exact qbG01
 · exact qbG02
 · exact qbG03
 · exact qbG04
 · exact qbG05
 · exact qbG06
 · exact qbG07
 · exact qbG08
 · exact qbG09
 · exact qbG10
 · exact qbG11
 · exact qbG12
 · exact qbG13
 · exact qbG14
 · exact qbG15
 · exact qbG16
 · exact qbG17
 · exact qbG18
 · exact qbG19
 · exact qbG20
 · exact qbG21
 · exact qbG22
 · exact qbG23
 · exact qbG24
 · exact qbG25
 · exact qbG26
 · exact qbG27
 · exact qbG28
 · exact qbG29
 · exact qbG30
 · exact qbG31
theorem pbindG (v : Fin 60) : rp (PG v) = pG v := by
 fin_cases v
 · exact pbG00
 · exact pbG01
 · exact pbG02
 · exact pbG03
 · exact pbG04
 · exact pbG05
 · exact pbG06
 · exact pbG07
 · exact pbG08
 · exact pbG09
 · exact pbG10
 · exact pbG11
 · exact pbG12
 · exact pbG13
 · exact pbG14
 · exact pbG15
 · exact pbG16
 · exact pbG17
 · exact pbG18
 · exact pbG19
 · exact pbG20
 · exact pbG21
 · exact pbG22
 · exact pbG23
 · exact pbG24
 · exact pbG25
 · exact pbG26
 · exact pbG27
 · exact pbG28
 · exact pbG29
 · exact pbG30
 · exact pbG31
 · exact pbG32
 · exact pbG33
 · exact pbG34
 · exact pbG35
 · exact pbG36
 · exact pbG37
 · exact pbG38
 · exact pbG39
 · exact pbG40
 · exact pbG41
 · exact pbG42
 · exact pbG43
 · exact pbG44
 · exact pbG45
 · exact pbG46
 · exact pbG47
 · exact pbG48
 · exact pbG49
 · exact pbG50
 · exact pbG51
 · exact pbG52
 · exact pbG53
 · exact pbG54
 · exact pbG55
 · exact pbG56
 · exact pbG57
 · exact pbG58
 · exact pbG59
end TripleCertificates
