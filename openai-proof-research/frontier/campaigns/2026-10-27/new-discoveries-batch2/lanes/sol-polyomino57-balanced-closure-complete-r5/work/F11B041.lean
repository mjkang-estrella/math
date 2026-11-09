import TreeBlock041
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B041L0 : RowFamilyTree := TreeBlock041L0
abbrev F11B041L1 : RowFamilyTree := TreeBlock041L1
abbrev F11B041L2 : RowFamilyTree := TreeBlock041L2
abbrev F11B041L3 : RowFamilyTree := TreeBlock041L3
abbrev F11B041L4 : RowFamilyTree := TreeBlock041L4
abbrev F11B041L5 : RowFamilyTree := TreeBlock041L5
abbrev F11B041L6 : RowFamilyTree := TreeBlock041L6
abbrev F11B041L7 : RowFamilyTree := TreeBlock041L7
abbrev F11B041L8 : RowFamilyTree := TreeBlock041L8
abbrev F11B041L9 : RowFamilyTree := TreeBlock041L9
abbrev F11B041L10 : RowFamilyTree := TreeBlock041L10
abbrev F11B041L11 : RowFamilyTree := TreeBlock041L11
abbrev F11B041L12 : RowFamilyTree := TreeBlock041L12
abbrev F11B041L13 : RowFamilyTree := TreeBlock041L13
abbrev F11B041L14 : RowFamilyTree := TreeBlock041L14
abbrev F11B041L15 : RowFamilyTree := TreeBlock041L15
abbrev F11B041L16 : RowFamilyTree := TreeBlock041L16
abbrev F11B041L17 : RowFamilyTree := TreeBlock041L17
abbrev F11B041L18 : RowFamilyTree := TreeBlock041L18
abbrev F11B041L19 : RowFamilyTree := TreeBlock041L19
abbrev F11B041L20 : RowFamilyTree := TreeBlock041L20
abbrev F11B041L21 : RowFamilyTree := TreeBlock041L21
abbrev F11B041L22 : RowFamilyTree := TreeBlock041L22
abbrev F11B041L23 : RowFamilyTree := TreeBlock041L23
abbrev F11B041L24 : RowFamilyTree := TreeBlock041L24
abbrev F11B041L25 : RowFamilyTree := TreeBlock041L25
abbrev F11B041L26 : RowFamilyTree := TreeBlock041L26
abbrev F11B041L27 : RowFamilyTree := TreeBlock041L27
abbrev F11B041L28 : RowFamilyTree := TreeBlock041L28
abbrev F11B041L29 : RowFamilyTree := TreeBlock041L29
abbrev F11B041L30 : RowFamilyTree := TreeBlock041L30
abbrev F11B041L31 : RowFamilyTree := TreeBlock041L31
abbrev F11B041L32 : RowFamilyTree := TreeBlock041L32
abbrev F11B041L33 : RowFamilyTree := TreeBlock041L33
abbrev F11B041L34 : RowFamilyTree := TreeBlock041L34
abbrev F11B041L35 : RowFamilyTree := TreeBlock041L35
abbrev F11B041L36 : RowFamilyTree := TreeBlock041L36
abbrev F11B041L37 : RowFamilyTree := TreeBlock041L37
abbrev F11B041L38 : RowFamilyTree := TreeBlock041L38
abbrev F11B041L39 : RowFamilyTree := TreeBlock041L39
abbrev F11B041L40 : RowFamilyTree := TreeBlock041L40
abbrev F11B041L41 : RowFamilyTree := TreeBlock041L41
abbrev F11B041L42 : RowFamilyTree := TreeBlock041L42
abbrev F11B041L43 : RowFamilyTree := TreeBlock041L43
abbrev F11B041L44 : RowFamilyTree := TreeBlock041L44
abbrev F11B041L45 : RowFamilyTree := TreeBlock041L45
abbrev F11B041L46 : RowFamilyTree := TreeBlock041L46
abbrev F11B041L47 : RowFamilyTree := TreeBlock041L47
abbrev F11B041L48 : RowFamilyTree := TreeBlock041L48
abbrev F11B041L49 : RowFamilyTree := TreeBlock041L49
abbrev F11B041L50 : RowFamilyTree := TreeBlock041L50
abbrev F11B041L51 : RowFamilyTree := TreeBlock041L51
abbrev F11B041L52 : RowFamilyTree := TreeBlock041L52
abbrev F11B041L53 : RowFamilyTree := TreeBlock041L53
abbrev F11B041L54 : RowFamilyTree := TreeBlock041L54
abbrev F11B041L55 : RowFamilyTree := TreeBlock041L55
abbrev F11B041L56 : RowFamilyTree := TreeBlock041L56
abbrev F11B041L57 : RowFamilyTree := TreeBlock041L57
abbrev F11B041L58 : RowFamilyTree := TreeBlock041L58
abbrev F11B041L59 : RowFamilyTree := TreeBlock041L59
abbrev F11B041L60 : RowFamilyTree := TreeBlock041L60
abbrev F11B041L61 : RowFamilyTree := TreeBlock041L61
abbrev F11B041L62 : RowFamilyTree := TreeBlock041L62
abbrev F11B041L63 : RowFamilyTree := TreeBlock041L63
abbrev F11B041 : RowFamilyTree := TreeBlock041
theorem F11B041L0_lift (row : List GridPoint) (h : FamilyMember row F11B041L0) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B041L1_lift (row : List GridPoint) (h : FamilyMember row F11B041L1) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B041L2_lift (row : List GridPoint) (h : FamilyMember row F11B041L2) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B041L3_lift (row : List GridPoint) (h : FamilyMember row F11B041L3) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B041L4_lift (row : List GridPoint) (h : FamilyMember row F11B041L4) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B041L5_lift (row : List GridPoint) (h : FamilyMember row F11B041L5) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B041L6_lift (row : List GridPoint) (h : FamilyMember row F11B041L6) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B041L7_lift (row : List GridPoint) (h : FamilyMember row F11B041L7) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B041L8_lift (row : List GridPoint) (h : FamilyMember row F11B041L8) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B041L9_lift (row : List GridPoint) (h : FamilyMember row F11B041L9) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B041L10_lift (row : List GridPoint) (h : FamilyMember row F11B041L10) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B041L11_lift (row : List GridPoint) (h : FamilyMember row F11B041L11) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B041L12_lift (row : List GridPoint) (h : FamilyMember row F11B041L12) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B041L13_lift (row : List GridPoint) (h : FamilyMember row F11B041L13) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B041L14_lift (row : List GridPoint) (h : FamilyMember row F11B041L14) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B041L15_lift (row : List GridPoint) (h : FamilyMember row F11B041L15) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B041L16_lift (row : List GridPoint) (h : FamilyMember row F11B041L16) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B041L17_lift (row : List GridPoint) (h : FamilyMember row F11B041L17) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B041L18_lift (row : List GridPoint) (h : FamilyMember row F11B041L18) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B041L19_lift (row : List GridPoint) (h : FamilyMember row F11B041L19) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B041L20_lift (row : List GridPoint) (h : FamilyMember row F11B041L20) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B041L21_lift (row : List GridPoint) (h : FamilyMember row F11B041L21) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B041L22_lift (row : List GridPoint) (h : FamilyMember row F11B041L22) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B041L23_lift (row : List GridPoint) (h : FamilyMember row F11B041L23) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B041L24_lift (row : List GridPoint) (h : FamilyMember row F11B041L24) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B041L25_lift (row : List GridPoint) (h : FamilyMember row F11B041L25) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B041L26_lift (row : List GridPoint) (h : FamilyMember row F11B041L26) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B041L27_lift (row : List GridPoint) (h : FamilyMember row F11B041L27) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B041L28_lift (row : List GridPoint) (h : FamilyMember row F11B041L28) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B041L29_lift (row : List GridPoint) (h : FamilyMember row F11B041L29) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B041L30_lift (row : List GridPoint) (h : FamilyMember row F11B041L30) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B041L31_lift (row : List GridPoint) (h : FamilyMember row F11B041L31) : FamilyMember row F11B041 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B041L32_lift (row : List GridPoint) (h : FamilyMember row F11B041L32) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B041L33_lift (row : List GridPoint) (h : FamilyMember row F11B041L33) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B041L34_lift (row : List GridPoint) (h : FamilyMember row F11B041L34) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B041L35_lift (row : List GridPoint) (h : FamilyMember row F11B041L35) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B041L36_lift (row : List GridPoint) (h : FamilyMember row F11B041L36) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B041L37_lift (row : List GridPoint) (h : FamilyMember row F11B041L37) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B041L38_lift (row : List GridPoint) (h : FamilyMember row F11B041L38) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B041L39_lift (row : List GridPoint) (h : FamilyMember row F11B041L39) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B041L40_lift (row : List GridPoint) (h : FamilyMember row F11B041L40) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B041L41_lift (row : List GridPoint) (h : FamilyMember row F11B041L41) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B041L42_lift (row : List GridPoint) (h : FamilyMember row F11B041L42) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B041L43_lift (row : List GridPoint) (h : FamilyMember row F11B041L43) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B041L44_lift (row : List GridPoint) (h : FamilyMember row F11B041L44) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B041L45_lift (row : List GridPoint) (h : FamilyMember row F11B041L45) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B041L46_lift (row : List GridPoint) (h : FamilyMember row F11B041L46) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B041L47_lift (row : List GridPoint) (h : FamilyMember row F11B041L47) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B041L48_lift (row : List GridPoint) (h : FamilyMember row F11B041L48) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B041L49_lift (row : List GridPoint) (h : FamilyMember row F11B041L49) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B041L50_lift (row : List GridPoint) (h : FamilyMember row F11B041L50) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B041L51_lift (row : List GridPoint) (h : FamilyMember row F11B041L51) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B041L52_lift (row : List GridPoint) (h : FamilyMember row F11B041L52) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B041L53_lift (row : List GridPoint) (h : FamilyMember row F11B041L53) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B041L54_lift (row : List GridPoint) (h : FamilyMember row F11B041L54) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B041L55_lift (row : List GridPoint) (h : FamilyMember row F11B041L55) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B041L56_lift (row : List GridPoint) (h : FamilyMember row F11B041L56) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B041L57_lift (row : List GridPoint) (h : FamilyMember row F11B041L57) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B041L58_lift (row : List GridPoint) (h : FamilyMember row F11B041L58) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B041L59_lift (row : List GridPoint) (h : FamilyMember row F11B041L59) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B041L60_lift (row : List GridPoint) (h : FamilyMember row F11B041L60) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B041L61_lift (row : List GridPoint) (h : FamilyMember row F11B041L61) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B041L62_lift (row : List GridPoint) (h : FamilyMember row F11B041L62) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B041L63_lift (row : List GridPoint) (h : FamilyMember row F11B041L63) : FamilyMember row F11B041 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
