import TreeBlock035
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B035L0 : RowFamilyTree := TreeBlock035L0
abbrev F11B035L1 : RowFamilyTree := TreeBlock035L1
abbrev F11B035L2 : RowFamilyTree := TreeBlock035L2
abbrev F11B035L3 : RowFamilyTree := TreeBlock035L3
abbrev F11B035L4 : RowFamilyTree := TreeBlock035L4
abbrev F11B035L5 : RowFamilyTree := TreeBlock035L5
abbrev F11B035L6 : RowFamilyTree := TreeBlock035L6
abbrev F11B035L7 : RowFamilyTree := TreeBlock035L7
abbrev F11B035L8 : RowFamilyTree := TreeBlock035L8
abbrev F11B035L9 : RowFamilyTree := TreeBlock035L9
abbrev F11B035L10 : RowFamilyTree := TreeBlock035L10
abbrev F11B035L11 : RowFamilyTree := TreeBlock035L11
abbrev F11B035L12 : RowFamilyTree := TreeBlock035L12
abbrev F11B035L13 : RowFamilyTree := TreeBlock035L13
abbrev F11B035L14 : RowFamilyTree := TreeBlock035L14
abbrev F11B035L15 : RowFamilyTree := TreeBlock035L15
abbrev F11B035L16 : RowFamilyTree := TreeBlock035L16
abbrev F11B035L17 : RowFamilyTree := TreeBlock035L17
abbrev F11B035L18 : RowFamilyTree := TreeBlock035L18
abbrev F11B035L19 : RowFamilyTree := TreeBlock035L19
abbrev F11B035L20 : RowFamilyTree := TreeBlock035L20
abbrev F11B035L21 : RowFamilyTree := TreeBlock035L21
abbrev F11B035L22 : RowFamilyTree := TreeBlock035L22
abbrev F11B035L23 : RowFamilyTree := TreeBlock035L23
abbrev F11B035L24 : RowFamilyTree := TreeBlock035L24
abbrev F11B035L25 : RowFamilyTree := TreeBlock035L25
abbrev F11B035L26 : RowFamilyTree := TreeBlock035L26
abbrev F11B035L27 : RowFamilyTree := TreeBlock035L27
abbrev F11B035L28 : RowFamilyTree := TreeBlock035L28
abbrev F11B035L29 : RowFamilyTree := TreeBlock035L29
abbrev F11B035L30 : RowFamilyTree := TreeBlock035L30
abbrev F11B035L31 : RowFamilyTree := TreeBlock035L31
abbrev F11B035L32 : RowFamilyTree := TreeBlock035L32
abbrev F11B035L33 : RowFamilyTree := TreeBlock035L33
abbrev F11B035L34 : RowFamilyTree := TreeBlock035L34
abbrev F11B035L35 : RowFamilyTree := TreeBlock035L35
abbrev F11B035L36 : RowFamilyTree := TreeBlock035L36
abbrev F11B035L37 : RowFamilyTree := TreeBlock035L37
abbrev F11B035L38 : RowFamilyTree := TreeBlock035L38
abbrev F11B035L39 : RowFamilyTree := TreeBlock035L39
abbrev F11B035L40 : RowFamilyTree := TreeBlock035L40
abbrev F11B035L41 : RowFamilyTree := TreeBlock035L41
abbrev F11B035L42 : RowFamilyTree := TreeBlock035L42
abbrev F11B035L43 : RowFamilyTree := TreeBlock035L43
abbrev F11B035L44 : RowFamilyTree := TreeBlock035L44
abbrev F11B035L45 : RowFamilyTree := TreeBlock035L45
abbrev F11B035L46 : RowFamilyTree := TreeBlock035L46
abbrev F11B035L47 : RowFamilyTree := TreeBlock035L47
abbrev F11B035L48 : RowFamilyTree := TreeBlock035L48
abbrev F11B035L49 : RowFamilyTree := TreeBlock035L49
abbrev F11B035L50 : RowFamilyTree := TreeBlock035L50
abbrev F11B035L51 : RowFamilyTree := TreeBlock035L51
abbrev F11B035L52 : RowFamilyTree := TreeBlock035L52
abbrev F11B035L53 : RowFamilyTree := TreeBlock035L53
abbrev F11B035L54 : RowFamilyTree := TreeBlock035L54
abbrev F11B035L55 : RowFamilyTree := TreeBlock035L55
abbrev F11B035L56 : RowFamilyTree := TreeBlock035L56
abbrev F11B035L57 : RowFamilyTree := TreeBlock035L57
abbrev F11B035L58 : RowFamilyTree := TreeBlock035L58
abbrev F11B035L59 : RowFamilyTree := TreeBlock035L59
abbrev F11B035L60 : RowFamilyTree := TreeBlock035L60
abbrev F11B035L61 : RowFamilyTree := TreeBlock035L61
abbrev F11B035L62 : RowFamilyTree := TreeBlock035L62
abbrev F11B035L63 : RowFamilyTree := TreeBlock035L63
abbrev F11B035 : RowFamilyTree := TreeBlock035
theorem F11B035L0_lift (row : List GridPoint) (h : FamilyMember row F11B035L0) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B035L1_lift (row : List GridPoint) (h : FamilyMember row F11B035L1) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B035L2_lift (row : List GridPoint) (h : FamilyMember row F11B035L2) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B035L3_lift (row : List GridPoint) (h : FamilyMember row F11B035L3) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B035L4_lift (row : List GridPoint) (h : FamilyMember row F11B035L4) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B035L5_lift (row : List GridPoint) (h : FamilyMember row F11B035L5) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B035L6_lift (row : List GridPoint) (h : FamilyMember row F11B035L6) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B035L7_lift (row : List GridPoint) (h : FamilyMember row F11B035L7) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B035L8_lift (row : List GridPoint) (h : FamilyMember row F11B035L8) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B035L9_lift (row : List GridPoint) (h : FamilyMember row F11B035L9) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B035L10_lift (row : List GridPoint) (h : FamilyMember row F11B035L10) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B035L11_lift (row : List GridPoint) (h : FamilyMember row F11B035L11) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B035L12_lift (row : List GridPoint) (h : FamilyMember row F11B035L12) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B035L13_lift (row : List GridPoint) (h : FamilyMember row F11B035L13) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B035L14_lift (row : List GridPoint) (h : FamilyMember row F11B035L14) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B035L15_lift (row : List GridPoint) (h : FamilyMember row F11B035L15) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B035L16_lift (row : List GridPoint) (h : FamilyMember row F11B035L16) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B035L17_lift (row : List GridPoint) (h : FamilyMember row F11B035L17) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B035L18_lift (row : List GridPoint) (h : FamilyMember row F11B035L18) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B035L19_lift (row : List GridPoint) (h : FamilyMember row F11B035L19) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B035L20_lift (row : List GridPoint) (h : FamilyMember row F11B035L20) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B035L21_lift (row : List GridPoint) (h : FamilyMember row F11B035L21) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B035L22_lift (row : List GridPoint) (h : FamilyMember row F11B035L22) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B035L23_lift (row : List GridPoint) (h : FamilyMember row F11B035L23) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B035L24_lift (row : List GridPoint) (h : FamilyMember row F11B035L24) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B035L25_lift (row : List GridPoint) (h : FamilyMember row F11B035L25) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B035L26_lift (row : List GridPoint) (h : FamilyMember row F11B035L26) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B035L27_lift (row : List GridPoint) (h : FamilyMember row F11B035L27) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B035L28_lift (row : List GridPoint) (h : FamilyMember row F11B035L28) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B035L29_lift (row : List GridPoint) (h : FamilyMember row F11B035L29) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B035L30_lift (row : List GridPoint) (h : FamilyMember row F11B035L30) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B035L31_lift (row : List GridPoint) (h : FamilyMember row F11B035L31) : FamilyMember row F11B035 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B035L32_lift (row : List GridPoint) (h : FamilyMember row F11B035L32) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B035L33_lift (row : List GridPoint) (h : FamilyMember row F11B035L33) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B035L34_lift (row : List GridPoint) (h : FamilyMember row F11B035L34) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B035L35_lift (row : List GridPoint) (h : FamilyMember row F11B035L35) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B035L36_lift (row : List GridPoint) (h : FamilyMember row F11B035L36) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B035L37_lift (row : List GridPoint) (h : FamilyMember row F11B035L37) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B035L38_lift (row : List GridPoint) (h : FamilyMember row F11B035L38) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B035L39_lift (row : List GridPoint) (h : FamilyMember row F11B035L39) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B035L40_lift (row : List GridPoint) (h : FamilyMember row F11B035L40) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B035L41_lift (row : List GridPoint) (h : FamilyMember row F11B035L41) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B035L42_lift (row : List GridPoint) (h : FamilyMember row F11B035L42) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B035L43_lift (row : List GridPoint) (h : FamilyMember row F11B035L43) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B035L44_lift (row : List GridPoint) (h : FamilyMember row F11B035L44) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B035L45_lift (row : List GridPoint) (h : FamilyMember row F11B035L45) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B035L46_lift (row : List GridPoint) (h : FamilyMember row F11B035L46) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B035L47_lift (row : List GridPoint) (h : FamilyMember row F11B035L47) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B035L48_lift (row : List GridPoint) (h : FamilyMember row F11B035L48) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B035L49_lift (row : List GridPoint) (h : FamilyMember row F11B035L49) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B035L50_lift (row : List GridPoint) (h : FamilyMember row F11B035L50) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B035L51_lift (row : List GridPoint) (h : FamilyMember row F11B035L51) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B035L52_lift (row : List GridPoint) (h : FamilyMember row F11B035L52) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B035L53_lift (row : List GridPoint) (h : FamilyMember row F11B035L53) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B035L54_lift (row : List GridPoint) (h : FamilyMember row F11B035L54) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B035L55_lift (row : List GridPoint) (h : FamilyMember row F11B035L55) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B035L56_lift (row : List GridPoint) (h : FamilyMember row F11B035L56) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B035L57_lift (row : List GridPoint) (h : FamilyMember row F11B035L57) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B035L58_lift (row : List GridPoint) (h : FamilyMember row F11B035L58) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B035L59_lift (row : List GridPoint) (h : FamilyMember row F11B035L59) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B035L60_lift (row : List GridPoint) (h : FamilyMember row F11B035L60) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B035L61_lift (row : List GridPoint) (h : FamilyMember row F11B035L61) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B035L62_lift (row : List GridPoint) (h : FamilyMember row F11B035L62) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B035L63_lift (row : List GridPoint) (h : FamilyMember row F11B035L63) : FamilyMember row F11B035 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
