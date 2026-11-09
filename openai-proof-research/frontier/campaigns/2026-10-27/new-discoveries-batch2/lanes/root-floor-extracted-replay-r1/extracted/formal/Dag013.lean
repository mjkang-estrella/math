import Dag012
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n4999 (_v : Vars) (_q : Query _v) (h91 : (e91 _v)) : (e91 _v) := by
  exact h91
theorem n5000 (_v : Vars) (_q : Query _v) (h30 : (e30 _v)) : (e30 _v) := by
  exact h30
theorem n5001 (_v : Vars) (_q : Query _v) (h4096 : (e4096 _v)) : (e4096 _v) := by
  exact h4096
theorem n5002 (_v : Vars) (_q : Query _v) (h3971 : (e3971 _v)) : (e3971 _v) := by
  exact h3971
theorem n5003 (_v : Vars) (_q : Query _v) (h4199 : (e4199 _v)) : (e4199 _v) := by
  exact h4199
theorem n5004 (_v : Vars) (_q : Query _v) (h4220 : (e4220 _v)) : (e4220 _v) := by
  exact h4220
theorem n5005 (_v : Vars) (_q : Query _v) (h3169 : (e3169 _v)) : (e3169 _v) := by
  exact h3169
theorem n5006 (_v : Vars) (_q : Query _v) (h4675 : (e4675 _v)) : (e4675 _v) := by
  exact h4675
theorem n5007 (_v : Vars) (_q : Query _v) (h225 : (e225 _v)) : (e225 _v) := by
  exact h225
theorem n5008 (_v : Vars) (_q : Query _v) (h4787 : (e4787 _v)) : (e4787 _v) := by
  exact h4787
theorem n5009 (_v : Vars) (_q : Query _v) (h4181 : (e4181 _v)) : (e4181 _v) := by
  exact h4181
theorem n5010 (_v : Vars) (_q : Query _v) (h70 : (e70 _v)) : (e70 _v) := by
  exact h70
theorem n5011 (_v : Vars) (_q : Query _v) (h4486 : (e4486 _v)) : (e4486 _v) := by
  exact h4486
theorem n5012 (_v : Vars) (_q : Query _v) (h4054 : (e4054 _v)) : (e4054 _v) := by
  exact h4054
theorem n5013 (_v : Vars) (_q : Query _v) (h3851 : (e3851 _v)) : (e3851 _v) := by
  exact h3851
theorem n5014 (_v : Vars) (_q : Query _v) (h4720 : (e4720 _v)) : (e4720 _v) := by
  exact h4720
theorem n5019 (_v : Vars) (_q : Query _v) (h5018 : (e5018 _v)) : (e5018 _v) := by
  exact h5018
theorem n5022 (_v : Vars) (_q : Query _v) (h3849 : (e3849 _v)) : (e3849 _v) := by
  exact h3849
theorem n5024 (_v : Vars) (_q : Query _v) (h4897 : (e4897 _v)) : (e4897 _v) := by
  exact h4897
theorem n5026 (_v : Vars) (_q : Query _v) (h4201 : (e4201 _v)) : (e4201 _v) := by
  exact h4201
theorem n5027 (_v : Vars) (_q : Query _v) (h4158 : (e4158 _v)) : (e4158 _v) := by
  exact h4158
theorem n5085 (_v : Vars) (_q : Query _v)  : (e29 _v) := by
  simp only [e5, e6, e12, e20, e26, e27, e28, e29] at *
  omega
theorem n5086 (_v : Vars) (_q : Query _v)  : (e31 _v) := by
  simp only [e5, e6, e12, e22, e26, e27, e30, e31] at *
  omega
theorem n5088 (_v : Vars) (_q : Query _v)  : (e5087 _v) := by
  have p5085 := n5085 _v _q 
  have p5086 := n5086 _v _q 
  change ((e20 _v) ↔ (e28 _v)) at p5085
  change ((e22 _v) ↔ (e30 _v)) at p5086
  change ((e20 _v) ↔ (e28 _v)) at p5085
  change ((e22 _v) ↔ (e30 _v)) at p5086
  simp only [e5087, e23, e32, p5085, p5086]
theorem n5092 (_v : Vars) (_q : Query _v)  : (e5091 _v) := by
  simp only [e5, e6, e12, e26, e27, e28, e30, e32, e34, e35, e5089, e5090, e5091] at *
  omega
theorem n5113 (_v : Vars) (_q : Query _v)  : (e5112 _v) := by
  simp only [e12, e51, e52, e53, e57, e58, e59, e60, e5112] at *
  omega
theorem n5114 (_v : Vars) (_q : Query _v)  : (e71 _v) := by
  simp only [e5, e6, e12, e63, e68, e69, e70, e71] at *
  omega
theorem n5115 (_v : Vars) (_q : Query _v)  : (e73 _v) := by
  simp only [e5, e6, e12, e64, e68, e69, e72, e73] at *
  omega
theorem n5117 (_v : Vars) (_q : Query _v)  : (e5116 _v) := by
  have p5114 := n5114 _v _q 
  have p5115 := n5115 _v _q 
  change ((e63 _v) ↔ (e70 _v)) at p5114
  change ((e64 _v) ↔ (e72 _v)) at p5115
  change ((e63 _v) ↔ (e70 _v)) at p5114
  change ((e64 _v) ↔ (e72 _v)) at p5115
  simp only [e5116, e65, e74, p5114, p5115]
theorem n5121 (_v : Vars) (_q : Query _v)  : (e5120 _v) := by
  simp only [e5, e6, e12, e68, e69, e70, e72, e74, e75, e76, e5118, e5119, e5120] at *
  omega
theorem n5130 (_v : Vars) (_q : Query _v)  : (e90 _v) := by
  simp only [e5, e6, e12, e82, e87, e88, e89, e90] at *
  omega
theorem n5131 (_v : Vars) (_q : Query _v)  : (e92 _v) := by
  simp only [e5, e6, e12, e83, e87, e88, e91, e92] at *
  omega
theorem n5133 (_v : Vars) (_q : Query _v)  : (e5132 _v) := by
  have p5130 := n5130 _v _q 
  have p5131 := n5131 _v _q 
  change ((e82 _v) ↔ (e89 _v)) at p5130
  change ((e83 _v) ↔ (e91 _v)) at p5131
  change ((e82 _v) ↔ (e89 _v)) at p5130
  change ((e83 _v) ↔ (e91 _v)) at p5131
  simp only [e5132, e84, e93, p5130, p5131]
theorem n5137 (_v : Vars) (_q : Query _v)  : (e5136 _v) := by
  simp only [e5, e6, e12, e87, e88, e89, e91, e93, e94, e95, e5134, e5135, e5136] at *
  omega
theorem n5158 (_v : Vars) (_q : Query _v)  : (e5157 _v) := by
  simp only [e12, e102, e103, e104, e105, e106, e115, e118, e5157] at *
  omega
theorem n5159 (_v : Vars) (_q : Query _v)  : (e129 _v) := by
  simp only [e5, e6, e12, e121, e126, e127, e128, e129] at *
  omega
theorem n5160 (_v : Vars) (_q : Query _v)  : (e131 _v) := by
  simp only [e5, e6, e12, e122, e126, e127, e130, e131] at *
  omega
theorem n5162 (_v : Vars) (_q : Query _v)  : (e5161 _v) := by
  have p5159 := n5159 _v _q 
  have p5160 := n5160 _v _q 
  change ((e121 _v) ↔ (e128 _v)) at p5159
  change ((e122 _v) ↔ (e130 _v)) at p5160
  change ((e121 _v) ↔ (e128 _v)) at p5159
  change ((e122 _v) ↔ (e130 _v)) at p5160
  simp only [e5161, e123, e132, p5159, p5160]
theorem n5166 (_v : Vars) (_q : Query _v)  : (e5165 _v) := by
  simp only [e5, e6, e12, e126, e127, e128, e130, e132, e133, e134, e5163, e5164, e5165] at *
  omega
theorem n5173 (_v : Vars) (_q : Query _v)  : (e144 _v) := by
  simp only [e5, e6, e12, e36, e137, e142, e143, e144] at *
  omega
theorem n5174 (_v : Vars) (_q : Query _v)  : (e143 _v) := by
  have p141 := n141 _v _q 
  have p5173 := n5173 _v _q 
  simp only [e137, e143, e144] at *
  tauto
theorem n5175 (_v : Vars) (_q : Query _v)  : (e155 _v) := by
  exact (((((((((((((_q).2).2).2).2).2).2).2).2).2).2).2).2).1
theorem n5176 (_v : Vars) (_q : Query _v)  : (e157 _v) := by
  have p5175 := n5175 _v _q 
  have p159 := n159 _v _q 
  simp only [e155, e156, e157, e158] at *
  tauto
theorem n5177 (_v : Vars) (_q : Query _v)  : (e157 _v) := by
  have p5176 := n5176 _v _q 
  have p161 := n161 _v _q 
  simp only [e156, e157, e160] at *
  tauto
theorem n5178 (_v : Vars) (_q : Query _v)  : (e164 _v) := by
  simp only [e5, e6, e8, e12, e156, e162, e163, e164] at *
  omega
end
end Assembly
