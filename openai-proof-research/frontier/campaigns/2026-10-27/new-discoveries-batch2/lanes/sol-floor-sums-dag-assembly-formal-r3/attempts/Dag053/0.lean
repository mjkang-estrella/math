import Dag052
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000
namespace Assembly
noncomputable section
open Classical
theorem n10075 (_v : Vars) (_q : Query _v)  : (e6413 _v) := by
  simp only [e413, e749, e2823, e2824, e6401, e6411, e6412, e6413] at *
  by_cases hc : ((e2 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10077 (_v : Vars) (_q : Query _v)  : (e10076 _v) := by
  have p10075 := n10075 _v _q 
  simp only [e413, e749, e1978, e2823, e2824, e6401, e6411, e6412, e6413, e10076] at *
  tauto
theorem n10079 (_v : Vars) (_q : Query _v)  : (e10078 _v) := by
  have p10077 := n10077 _v _q 
  change ((e1978 _v) = (e413 _v)) at p10077
  simp only [e10078, e6195, e2825, p10077]
theorem n10081 (_v : Vars) (_q : Query _v)  : (e10080 _v) := by
  have p5348 := n5348 _v _q 
  simp only [e403, e411, e412, e413, e414, e415, e416, e2825, e5346, e5347, e10080] at *
  tauto
theorem n10083 (_v : Vars) (_q : Query _v)  : (e10082 _v) := by
  have p10079 := n10079 _v _q 
  have p10081 := n10081 _v _q 
  exact (Eq.trans p10079 p10081)
theorem n10084 (_v : Vars) (_q : Query _v)  : (e6416 _v) := by
  simp only [e749, e2826, e2827, e2828, e6401, e6414, e6415, e6416] at *
  by_cases hc : ((e2 _v) ≤ (e12 _v)) <;> simp [hc]
theorem n10086 (_v : Vars) (_q : Query _v)  : (e10085 _v) := by
  have p10084 := n10084 _v _q 
  simp only [e749, e1988, e2826, e2827, e2828, e6401, e6414, e6415, e6416, e10085] at *
  tauto
theorem n10088 (_v : Vars) (_q : Query _v)  : (e10087 _v) := by
  have p10086 := n10086 _v _q 
  change ((e1988 _v) = (e2826 _v)) at p10086
  simp only [e10087, e6196, e2829, p10086]
theorem n10090 (_v : Vars) (_q : Query _v)  : (e10089 _v) := by
  have p6419 := n6419 _v _q 
  simp only [e1985, e2826, e2829, e2830, e2831, e2832, e2833, e3393, e6417, e6418, e10089] at *
  tauto
theorem n10092 (_v : Vars) (_q : Query _v)  : (e10091 _v) := by
  have p10088 := n10088 _v _q 
  have p10090 := n10090 _v _q 
  exact (Eq.trans p10088 p10090)
theorem n10094 (_v : Vars) (_q : Query _v)  : (e10093 _v) := by
  have p6422 := n6422 _v _q 
  simp only [e163, e165, e2003, e2834, e2835, e2836, e4238, e6420, e6421, e10093] at *
  tauto
theorem n10097 (_v : Vars) (_q : Query _v)  : (e10096 _v) := by
  have p10094 := n10094 _v _q 
  change ((e2003 _v) = (e2834 _v)) at p10094
  simp only [e10096, e9330, e10095, p10094]
theorem n10098 (_v : Vars) (_q : Query _v)  : (e6426 _v) := by
  simp only [e1995, e2834, e2918, e4566, e4576, e6423, e6424, e6425, e6426] at *
  by_cases hc : ((e1994 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10100 (_v : Vars) (_q : Query _v)  : (e10099 _v) := by
  have p10098 := n10098 _v _q 
  simp only [e1995, e2834, e2918, e4566, e4576, e6423, e6424, e6425, e6426, e10095, e10099] at *
  tauto
theorem n10102 (_v : Vars) (_q : Query _v)  : (e10101 _v) := by
  have p10097 := n10097 _v _q 
  have p10100 := n10100 _v _q 
  exact (Eq.trans p10097 p10100)
theorem n10104 (_v : Vars) (_q : Query _v)  : (e10103 _v) := by
  have p6430 := n6430 _v _q 
  simp only [e2017, e2020, e2837, e2838, e2839, e2840, e6427, e6428, e6429, e10103] at *
  tauto
theorem n10107 (_v : Vars) (_q : Query _v)  : (e10106 _v) := by
  have p10104 := n10104 _v _q 
  change ((e2020 _v) = (e2838 _v)) at p10104
  simp only [e10106, e9341, e10105, p10104]
theorem n10108 (_v : Vars) (_q : Query _v)  : (e6434 _v) := by
  simp only [e2010, e2838, e2920, e3314, e3319, e6431, e6432, e6433, e6434] at *
  by_cases hc : ((e2009 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10110 (_v : Vars) (_q : Query _v)  : (e10109 _v) := by
  have p10108 := n10108 _v _q 
  simp only [e2010, e2838, e2920, e3314, e3319, e6431, e6432, e6433, e6434, e10105, e10109] at *
  tauto
theorem n10112 (_v : Vars) (_q : Query _v)  : (e10111 _v) := by
  have p10107 := n10107 _v _q 
  have p10110 := n10110 _v _q 
  exact (Eq.trans p10107 p10110)
theorem n10114 (_v : Vars) (_q : Query _v)  : (e10113 _v) := by
  have p6438 := n6438 _v _q 
  simp only [e2034, e2037, e2841, e2842, e2843, e2844, e6435, e6436, e6437, e10113] at *
  tauto
theorem n10117 (_v : Vars) (_q : Query _v)  : (e10116 _v) := by
  have p10114 := n10114 _v _q 
  change ((e2037 _v) = (e2842 _v)) at p10114
  simp only [e10116, e9352, e10115, p10114]
theorem n10118 (_v : Vars) (_q : Query _v)  : (e6442 _v) := by
  simp only [e2027, e2842, e2922, e3082, e3087, e6439, e6440, e6441, e6442] at *
  by_cases hc : ((e2026 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10120 (_v : Vars) (_q : Query _v)  : (e10119 _v) := by
  have p10118 := n10118 _v _q 
  simp only [e2027, e2842, e2922, e3082, e3087, e6439, e6440, e6441, e6442, e10115, e10119] at *
  tauto
theorem n10122 (_v : Vars) (_q : Query _v)  : (e10121 _v) := by
  have p10117 := n10117 _v _q 
  have p10120 := n10120 _v _q 
  exact (Eq.trans p10117 p10120)
theorem n10124 (_v : Vars) (_q : Query _v)  : (e10123 _v) := by
  have p6446 := n6446 _v _q 
  simp only [e2051, e2054, e2845, e2846, e2847, e2848, e6443, e6444, e6445, e10123] at *
  tauto
theorem n10127 (_v : Vars) (_q : Query _v)  : (e10126 _v) := by
  have p10124 := n10124 _v _q 
  change ((e2054 _v) = (e2846 _v)) at p10124
  simp only [e10126, e9363, e10125, p10124]
theorem n10128 (_v : Vars) (_q : Query _v)  : (e6450 _v) := by
  simp only [e2044, e2846, e2924, e3641, e3646, e6447, e6448, e6449, e6450] at *
  by_cases hc : ((e2043 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10130 (_v : Vars) (_q : Query _v)  : (e10129 _v) := by
  have p10128 := n10128 _v _q 
  simp only [e2044, e2846, e2924, e3641, e3646, e6447, e6448, e6449, e6450, e10125, e10129] at *
  tauto
theorem n10132 (_v : Vars) (_q : Query _v)  : (e10131 _v) := by
  have p10127 := n10127 _v _q 
  have p10130 := n10130 _v _q 
  exact (Eq.trans p10127 p10130)
theorem n10134 (_v : Vars) (_q : Query _v)  : (e10133 _v) := by
  have p6453 := n6453 _v _q 
  simp only [e174, e176, e2069, e2849, e2850, e2851, e4629, e6451, e6452, e10133] at *
  tauto
theorem n10137 (_v : Vars) (_q : Query _v)  : (e10136 _v) := by
  have p10134 := n10134 _v _q 
  change ((e2069 _v) = (e2849 _v)) at p10134
  simp only [e10136, e9374, e10135, p10134]
theorem n10138 (_v : Vars) (_q : Query _v)  : (e6457 _v) := by
  simp only [e2061, e2849, e2926, e4438, e4448, e6454, e6455, e6456, e6457] at *
  by_cases hc : ((e2060 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10140 (_v : Vars) (_q : Query _v)  : (e10139 _v) := by
  have p10138 := n10138 _v _q 
  simp only [e2061, e2849, e2926, e4438, e4448, e6454, e6455, e6456, e6457, e10135, e10139] at *
  tauto
theorem n10142 (_v : Vars) (_q : Query _v)  : (e10141 _v) := by
  have p10137 := n10137 _v _q 
  have p10140 := n10140 _v _q 
  exact (Eq.trans p10137 p10140)
theorem n10144 (_v : Vars) (_q : Query _v)  : (e10143 _v) := by
  have p6461 := n6461 _v _q 
  simp only [e2083, e2086, e2852, e2853, e2854, e2855, e6458, e6459, e6460, e10143] at *
  tauto
theorem n10147 (_v : Vars) (_q : Query _v)  : (e10146 _v) := by
  have p10144 := n10144 _v _q 
  change ((e2086 _v) = (e2853 _v)) at p10144
  simp only [e10146, e9385, e10145, p10144]
theorem n10148 (_v : Vars) (_q : Query _v)  : (e6465 _v) := by
  simp only [e2076, e2853, e2928, e3545, e3550, e6462, e6463, e6464, e6465] at *
  by_cases hc : ((e2075 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10150 (_v : Vars) (_q : Query _v)  : (e10149 _v) := by
  have p10148 := n10148 _v _q 
  simp only [e2076, e2853, e2928, e3545, e3550, e6462, e6463, e6464, e6465, e10145, e10149] at *
  tauto
theorem n10152 (_v : Vars) (_q : Query _v)  : (e10151 _v) := by
  have p10147 := n10147 _v _q 
  have p10150 := n10150 _v _q 
  exact (Eq.trans p10147 p10150)
theorem n10154 (_v : Vars) (_q : Query _v)  : (e10153 _v) := by
  have p6469 := n6469 _v _q 
  simp only [e346, e2098, e2101, e2856, e2857, e2858, e6466, e6467, e6468, e10153] at *
  tauto
theorem n10157 (_v : Vars) (_q : Query _v)  : (e10156 _v) := by
  have p10154 := n10154 _v _q 
  change ((e2101 _v) = (e346 _v)) at p10154
  simp only [e10156, e9396, e10155, p10154]
theorem n10158 (_v : Vars) (_q : Query _v)  : (e5302 _v) := by
  simp only [e332, e340, e341, e346, e347, e5299, e5300, e5301, e5302] at *
  by_cases hc : ((e339 _v) ≥ (e12 _v)) <;> simp [hc]
theorem n10160 (_v : Vars) (_q : Query _v)  : (e10159 _v) := by
  have p10158 := n10158 _v _q 
  simp only [e332, e340, e341, e346, e347, e5299, e5300, e5301, e5302, e10155, e10159] at *
  tauto
theorem n10162 (_v : Vars) (_q : Query _v)  : (e10161 _v) := by
  have p10157 := n10157 _v _q 
  have p10160 := n10160 _v _q 
  exact (Eq.trans p10157 p10160)
end
end Assembly
