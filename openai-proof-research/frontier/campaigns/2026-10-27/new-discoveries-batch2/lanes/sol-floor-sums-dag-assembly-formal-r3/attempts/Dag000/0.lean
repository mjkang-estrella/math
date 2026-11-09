import Query
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n25 (_v : Vars) (_q : Query _v)  : (e24 _v) := by
  simp only [e18, e20, e22, e23, e24] at *
  omega
theorem n55 (_v : Vars) (_q : Query _v)  : (e54 _v) := by
  simp only [e12, e50, e51, e52, e53, e54] at *
  omega
theorem n67 (_v : Vars) (_q : Query _v)  : (e66 _v) := by
  simp only [e62, e63, e64, e65, e66] at *
  omega
theorem n86 (_v : Vars) (_q : Query _v)  : (e85 _v) := by
  simp only [e81, e82, e83, e84, e85] at *
  omega
theorem n117 (_v : Vars) (_q : Query _v)  : (e116 _v) := by
  simp only [e12, e102, e104, e114, e115, e116] at *
  omega
theorem n125 (_v : Vars) (_q : Query _v)  : (e124 _v) := by
  simp only [e120, e121, e122, e123, e124] at *
  omega
theorem n138 (_v : Vars) (_q : Query _v)  : (e137 _v) := by
  exact (_q).1
theorem n140 (_v : Vars) (_q : Query _v)  : (e139 _v) := by
  simp only [e137, e139] at *
  omega
theorem n141 (_v : Vars) (_q : Query _v)  : (e137 _v) := by
  have p138 := n138 _v _q 
  have p140 := n140 _v _q 
  simp only [e137, e139] at *
  tauto
theorem n147 (_v : Vars) (_q : Query _v)  : (e146 _v) := by
  simp only [e5, e6, e36, e142, e145, e146] at *
  omega
theorem n159 (_v : Vars) (_q : Query _v)  : (e158 _v) := by
  simp only [e155, e156, e157, e158] at *
  omega
theorem n161 (_v : Vars) (_q : Query _v)  : (e160 _v) := by
  simp only [e156, e157, e160] at *
  omega
theorem n170 (_v : Vars) (_q : Query _v)  : (e169 _v) := by
  simp only [e166, e167, e168, e169] at *
  omega
theorem n172 (_v : Vars) (_q : Query _v)  : (e171 _v) := by
  simp only [e167, e168, e171] at *
  omega
theorem n181 (_v : Vars) (_q : Query _v)  : (e180 _v) := by
  simp only [e177, e178, e179, e180] at *
  omega
theorem n183 (_v : Vars) (_q : Query _v)  : (e182 _v) := by
  simp only [e178, e179, e182] at *
  omega
theorem n204 (_v : Vars) (_q : Query _v)  : (e203 _v) := by
  simp only [e199, e200, e201, e202, e203] at *
  omega
theorem n222 (_v : Vars) (_q : Query _v)  : (e221 _v) := by
  simp only [e217, e218, e219, e220, e221] at *
  omega
theorem n235 (_v : Vars) (_q : Query _v)  : (e234 _v) := by
  exact ((_q).2).1
theorem n237 (_v : Vars) (_q : Query _v)  : (e236 _v) := by
  simp only [e234, e236] at *
  omega
theorem n238 (_v : Vars) (_q : Query _v)  : (e234 _v) := by
  have p235 := n235 _v _q 
  have p237 := n237 _v _q 
  simp only [e234, e236] at *
  tauto
theorem n243 (_v : Vars) (_q : Query _v)  : (e242 _v) := by
  exact (((_q).2).2).1
theorem n245 (_v : Vars) (_q : Query _v)  : (e244 _v) := by
  simp only [e242, e244] at *
  omega
theorem n246 (_v : Vars) (_q : Query _v)  : (e242 _v) := by
  have p243 := n243 _v _q 
  have p245 := n245 _v _q 
  simp only [e242, e244] at *
  tauto
theorem n253 (_v : Vars) (_q : Query _v) (h191 : (e191 _v)) : (e191 _v) := by
  exact h191
theorem n255 (_v : Vars) (_q : Query _v)  : (e254 _v) := by
  exact ((((_q).2).2).2).1
theorem n257 (_v : Vars) (_q : Query _v)  : (e256 _v) := by
  simp only [e5, e254, e256] at *
  omega
theorem n258 (_v : Vars) (_q : Query _v)  : (e254 _v) := by
  have p255 := n255 _v _q 
  have p257 := n257 _v _q 
  simp only [e254, e256] at *
  tauto
theorem n273 (_v : Vars) (_q : Query _v)  : (e272 _v) := by
  simp only [e12, e260, e262, e270, e271, e272] at *
  omega
theorem n281 (_v : Vars) (_q : Query _v)  : (e280 _v) := by
  simp only [e276, e277, e278, e279, e280] at *
  omega
theorem n293 (_v : Vars) (_q : Query _v)  : (e292 _v) := by
  exact (((((_q).2).2).2).2).1
theorem n295 (_v : Vars) (_q : Query _v)  : (e294 _v) := by
  simp only [e12, e292, e294] at *
  omega
theorem n296 (_v : Vars) (_q : Query _v)  : (e292 _v) := by
  have p293 := n293 _v _q 
  have p295 := n295 _v _q 
  simp only [e292, e294] at *
  tauto
theorem n309 (_v : Vars) (_q : Query _v)  : (e308 _v) := by
  simp only [e12, e298, e300, e306, e307, e308] at *
  omega
theorem n317 (_v : Vars) (_q : Query _v)  : (e316 _v) := by
  simp only [e312, e313, e314, e315, e316] at *
  omega
theorem n328 (_v : Vars) (_q : Query _v)  : (e327 _v) := by
  exact ((((((_q).2).2).2).2).2).1
theorem n330 (_v : Vars) (_q : Query _v)  : (e329 _v) := by
  simp only [e5, e327, e329] at *
  omega
theorem n331 (_v : Vars) (_q : Query _v)  : (e327 _v) := by
  have p328 := n328 _v _q 
  have p330 := n330 _v _q 
  simp only [e327, e329] at *
  tauto
theorem n344 (_v : Vars) (_q : Query _v)  : (e343 _v) := by
  simp only [e12, e333, e335, e341, e342, e343] at *
  omega
theorem n352 (_v : Vars) (_q : Query _v)  : (e351 _v) := by
  simp only [e347, e348, e349, e350, e351] at *
  omega
theorem n374 (_v : Vars) (_q : Query _v)  : (e373 _v) := by
  simp only [e12, e363, e365, e371, e372, e373] at *
  omega
theorem n382 (_v : Vars) (_q : Query _v)  : (e381 _v) := by
  simp only [e377, e378, e379, e380, e381] at *
  omega
theorem n396 (_v : Vars) (_q : Query _v)  : (e395 _v) := by
  simp only [e392, e393, e394, e395] at *
  omega
theorem n398 (_v : Vars) (_q : Query _v)  : (e397 _v) := by
  simp only [e393, e394, e397] at *
  omega
theorem n419 (_v : Vars) (_q : Query _v)  : (e418 _v) := by
  simp only [e12, e404, e406, e416, e417, e418] at *
  omega
end
end Assembly
