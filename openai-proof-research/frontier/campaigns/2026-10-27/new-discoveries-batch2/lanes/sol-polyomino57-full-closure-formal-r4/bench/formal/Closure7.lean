import Closure7C000
import Closure7C001
import Closure7C002
import Closure7C003
import Closure7C004
import Closure7C005
import Closure7C006
import Closure7C007
import Closure7C008
import Closure7C009
import Closure7C010
import Closure7C011
import Closure7C012
import Closure7C013
import Closure7C014
import Closure7C015
import Closure7C016
import Closure7C017
import Closure7C018
import Closure7C019
import Closure7C020
import Closure7C021
import Closure7C022
import Closure7C023
import Closure7C024
import Closure7C025
import Closure7C026
import Closure7C027
import Closure7C028
import Closure7C029
import Closure7C030
import Closure7C031
import Closure7C032
import Closure7C033
import Closure7C034
import Closure7C035
import Closure7C036
import Closure7C037
import Closure7C038
import Closure7C039
import Closure7C040
import Closure7C041
import Closure7C042
import Closure7C043
import Closure7C044
import Closure7C045
import Closure7C046
import Closure7C047
import Closure7C048
import Closure7C049
import Closure7C050
import Closure7C051
import Closure7C052
import Closure7C053
import Closure7C054
import Closure7C055
import Closure7C056
import Closure7C057
import Closure7C058
import Closure7C059
import Closure7C060
import Closure7C061
import Closure7C062
import Closure7C063
import Closure7C064
import Closure7C065
import Closure7C066
import Closure7C067
import Closure7C068
import Closure7C069
import Closure7C070
import Closure7C071
import Closure7C072
import Closure7C073
import Closure7C074
import Closure7C075
import Closure7C076
import Closure7C077
import Closure7C078
import Closure7C079
import Closure7C080
import Closure7C081
import Closure7C082
import Closure7C083
import Closure7C084
import Closure7C085
import Closure7C086
import Closure7C087
import Closure7C088
import Closure7C089
import Closure7C090
import Closure7C091
import Closure7C092
import Closure7C093
import Closure7C094
set_option autoImplicit false
namespace Polyomino57
def closedLayer7 : Array (List GridPoint) := (Closure7C000rows ++ (Closure7C001rows ++ (Closure7C002rows ++ (Closure7C003rows ++ (Closure7C004rows ++ (Closure7C005rows ++ (Closure7C006rows ++ (Closure7C007rows ++ (Closure7C008rows ++ (Closure7C009rows ++ (Closure7C010rows ++ (Closure7C011rows ++ (Closure7C012rows ++ (Closure7C013rows ++ (Closure7C014rows ++ (Closure7C015rows ++ (Closure7C016rows ++ (Closure7C017rows ++ (Closure7C018rows ++ (Closure7C019rows ++ (Closure7C020rows ++ (Closure7C021rows ++ (Closure7C022rows ++ (Closure7C023rows ++ (Closure7C024rows ++ (Closure7C025rows ++ (Closure7C026rows ++ (Closure7C027rows ++ (Closure7C028rows ++ (Closure7C029rows ++ (Closure7C030rows ++ (Closure7C031rows ++ (Closure7C032rows ++ (Closure7C033rows ++ (Closure7C034rows ++ (Closure7C035rows ++ (Closure7C036rows ++ (Closure7C037rows ++ (Closure7C038rows ++ (Closure7C039rows ++ (Closure7C040rows ++ (Closure7C041rows ++ (Closure7C042rows ++ (Closure7C043rows ++ (Closure7C044rows ++ (Closure7C045rows ++ (Closure7C046rows ++ (Closure7C047rows ++ (Closure7C048rows ++ (Closure7C049rows ++ (Closure7C050rows ++ (Closure7C051rows ++ (Closure7C052rows ++ (Closure7C053rows ++ (Closure7C054rows ++ (Closure7C055rows ++ (Closure7C056rows ++ (Closure7C057rows ++ (Closure7C058rows ++ (Closure7C059rows ++ (Closure7C060rows ++ (Closure7C061rows ++ (Closure7C062rows ++ (Closure7C063rows ++ (Closure7C064rows ++ (Closure7C065rows ++ (Closure7C066rows ++ (Closure7C067rows ++ (Closure7C068rows ++ (Closure7C069rows ++ (Closure7C070rows ++ (Closure7C071rows ++ (Closure7C072rows ++ (Closure7C073rows ++ (Closure7C074rows ++ (Closure7C075rows ++ (Closure7C076rows ++ (Closure7C077rows ++ (Closure7C078rows ++ (Closure7C079rows ++ (Closure7C080rows ++ (Closure7C081rows ++ (Closure7C082rows ++ (Closure7C083rows ++ (Closure7C084rows ++ (Closure7C085rows ++ (Closure7C086rows ++ (Closure7C087rows ++ (Closure7C088rows ++ (Closure7C089rows ++ (Closure7C090rows ++ (Closure7C091rows ++ (Closure7C092rows ++ (Closure7C093rows ++ (Closure7C094rows))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).toArray
theorem closure7_local : LocallyClosed closedLayer7 layer8 := by
  intro row hr
  simp only [closedLayer7,List.toList_toArray,List.mem_append] at hr
  rcases hr with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63 | h64 | h65 | h66 | h67 | h68 | h69 | h70 | h71 | h72 | h73 | h74 | h75 | h76 | h77 | h78 | h79 | h80 | h81 | h82 | h83 | h84 | h85 | h86 | h87 | h88 | h89 | h90 | h91 | h92 | h93 | h94
  · exact Closure7C000_closed row h0
  · exact Closure7C001_closed row h1
  · exact Closure7C002_closed row h2
  · exact Closure7C003_closed row h3
  · exact Closure7C004_closed row h4
  · exact Closure7C005_closed row h5
  · exact Closure7C006_closed row h6
  · exact Closure7C007_closed row h7
  · exact Closure7C008_closed row h8
  · exact Closure7C009_closed row h9
  · exact Closure7C010_closed row h10
  · exact Closure7C011_closed row h11
  · exact Closure7C012_closed row h12
  · exact Closure7C013_closed row h13
  · exact Closure7C014_closed row h14
  · exact Closure7C015_closed row h15
  · exact Closure7C016_closed row h16
  · exact Closure7C017_closed row h17
  · exact Closure7C018_closed row h18
  · exact Closure7C019_closed row h19
  · exact Closure7C020_closed row h20
  · exact Closure7C021_closed row h21
  · exact Closure7C022_closed row h22
  · exact Closure7C023_closed row h23
  · exact Closure7C024_closed row h24
  · exact Closure7C025_closed row h25
  · exact Closure7C026_closed row h26
  · exact Closure7C027_closed row h27
  · exact Closure7C028_closed row h28
  · exact Closure7C029_closed row h29
  · exact Closure7C030_closed row h30
  · exact Closure7C031_closed row h31
  · exact Closure7C032_closed row h32
  · exact Closure7C033_closed row h33
  · exact Closure7C034_closed row h34
  · exact Closure7C035_closed row h35
  · exact Closure7C036_closed row h36
  · exact Closure7C037_closed row h37
  · exact Closure7C038_closed row h38
  · exact Closure7C039_closed row h39
  · exact Closure7C040_closed row h40
  · exact Closure7C041_closed row h41
  · exact Closure7C042_closed row h42
  · exact Closure7C043_closed row h43
  · exact Closure7C044_closed row h44
  · exact Closure7C045_closed row h45
  · exact Closure7C046_closed row h46
  · exact Closure7C047_closed row h47
  · exact Closure7C048_closed row h48
  · exact Closure7C049_closed row h49
  · exact Closure7C050_closed row h50
  · exact Closure7C051_closed row h51
  · exact Closure7C052_closed row h52
  · exact Closure7C053_closed row h53
  · exact Closure7C054_closed row h54
  · exact Closure7C055_closed row h55
  · exact Closure7C056_closed row h56
  · exact Closure7C057_closed row h57
  · exact Closure7C058_closed row h58
  · exact Closure7C059_closed row h59
  · exact Closure7C060_closed row h60
  · exact Closure7C061_closed row h61
  · exact Closure7C062_closed row h62
  · exact Closure7C063_closed row h63
  · exact Closure7C064_closed row h64
  · exact Closure7C065_closed row h65
  · exact Closure7C066_closed row h66
  · exact Closure7C067_closed row h67
  · exact Closure7C068_closed row h68
  · exact Closure7C069_closed row h69
  · exact Closure7C070_closed row h70
  · exact Closure7C071_closed row h71
  · exact Closure7C072_closed row h72
  · exact Closure7C073_closed row h73
  · exact Closure7C074_closed row h74
  · exact Closure7C075_closed row h75
  · exact Closure7C076_closed row h76
  · exact Closure7C077_closed row h77
  · exact Closure7C078_closed row h78
  · exact Closure7C079_closed row h79
  · exact Closure7C080_closed row h80
  · exact Closure7C081_closed row h81
  · exact Closure7C082_closed row h82
  · exact Closure7C083_closed row h83
  · exact Closure7C084_closed row h84
  · exact Closure7C085_closed row h85
  · exact Closure7C086_closed row h86
  · exact Closure7C087_closed row h87
  · exact Closure7C088_closed row h88
  · exact Closure7C089_closed row h89
  · exact Closure7C090_closed row h90
  · exact Closure7C091_closed row h91
  · exact Closure7C092_closed row h92
  · exact Closure7C093_closed row h93
  · exact Closure7C094_closed row h94
theorem closure7 : ∃ choices, arrayClosureCheck closedLayer7 layer8 choices = true :=
  locallyClosed_array closure7_local
end Polyomino57
