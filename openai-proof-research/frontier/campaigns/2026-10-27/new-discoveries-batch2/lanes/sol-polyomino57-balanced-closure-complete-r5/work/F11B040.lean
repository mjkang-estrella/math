import TreeBlock040
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B040L0 : RowFamilyTree := TreeBlock040L0
abbrev F11B040L1 : RowFamilyTree := TreeBlock040L1
abbrev F11B040L2 : RowFamilyTree := TreeBlock040L2
abbrev F11B040L3 : RowFamilyTree := TreeBlock040L3
abbrev F11B040L4 : RowFamilyTree := TreeBlock040L4
abbrev F11B040L5 : RowFamilyTree := TreeBlock040L5
abbrev F11B040L6 : RowFamilyTree := TreeBlock040L6
abbrev F11B040L7 : RowFamilyTree := TreeBlock040L7
abbrev F11B040L8 : RowFamilyTree := TreeBlock040L8
abbrev F11B040L9 : RowFamilyTree := TreeBlock040L9
abbrev F11B040L10 : RowFamilyTree := TreeBlock040L10
abbrev F11B040L11 : RowFamilyTree := TreeBlock040L11
abbrev F11B040L12 : RowFamilyTree := TreeBlock040L12
abbrev F11B040L13 : RowFamilyTree := TreeBlock040L13
abbrev F11B040L14 : RowFamilyTree := TreeBlock040L14
abbrev F11B040L15 : RowFamilyTree := TreeBlock040L15
abbrev F11B040L16 : RowFamilyTree := TreeBlock040L16
abbrev F11B040L17 : RowFamilyTree := TreeBlock040L17
abbrev F11B040L18 : RowFamilyTree := TreeBlock040L18
abbrev F11B040L19 : RowFamilyTree := TreeBlock040L19
abbrev F11B040L20 : RowFamilyTree := TreeBlock040L20
abbrev F11B040L21 : RowFamilyTree := TreeBlock040L21
abbrev F11B040L22 : RowFamilyTree := TreeBlock040L22
abbrev F11B040L23 : RowFamilyTree := TreeBlock040L23
abbrev F11B040L24 : RowFamilyTree := TreeBlock040L24
abbrev F11B040L25 : RowFamilyTree := TreeBlock040L25
abbrev F11B040L26 : RowFamilyTree := TreeBlock040L26
abbrev F11B040L27 : RowFamilyTree := TreeBlock040L27
abbrev F11B040L28 : RowFamilyTree := TreeBlock040L28
abbrev F11B040L29 : RowFamilyTree := TreeBlock040L29
abbrev F11B040L30 : RowFamilyTree := TreeBlock040L30
abbrev F11B040L31 : RowFamilyTree := TreeBlock040L31
abbrev F11B040L32 : RowFamilyTree := TreeBlock040L32
abbrev F11B040L33 : RowFamilyTree := TreeBlock040L33
abbrev F11B040L34 : RowFamilyTree := TreeBlock040L34
abbrev F11B040L35 : RowFamilyTree := TreeBlock040L35
abbrev F11B040L36 : RowFamilyTree := TreeBlock040L36
abbrev F11B040L37 : RowFamilyTree := TreeBlock040L37
abbrev F11B040L38 : RowFamilyTree := TreeBlock040L38
abbrev F11B040L39 : RowFamilyTree := TreeBlock040L39
abbrev F11B040L40 : RowFamilyTree := TreeBlock040L40
abbrev F11B040L41 : RowFamilyTree := TreeBlock040L41
abbrev F11B040L42 : RowFamilyTree := TreeBlock040L42
abbrev F11B040L43 : RowFamilyTree := TreeBlock040L43
abbrev F11B040L44 : RowFamilyTree := TreeBlock040L44
abbrev F11B040L45 : RowFamilyTree := TreeBlock040L45
abbrev F11B040L46 : RowFamilyTree := TreeBlock040L46
abbrev F11B040L47 : RowFamilyTree := TreeBlock040L47
abbrev F11B040L48 : RowFamilyTree := TreeBlock040L48
abbrev F11B040L49 : RowFamilyTree := TreeBlock040L49
abbrev F11B040L50 : RowFamilyTree := TreeBlock040L50
abbrev F11B040L51 : RowFamilyTree := TreeBlock040L51
abbrev F11B040L52 : RowFamilyTree := TreeBlock040L52
abbrev F11B040L53 : RowFamilyTree := TreeBlock040L53
abbrev F11B040L54 : RowFamilyTree := TreeBlock040L54
abbrev F11B040L55 : RowFamilyTree := TreeBlock040L55
abbrev F11B040L56 : RowFamilyTree := TreeBlock040L56
abbrev F11B040L57 : RowFamilyTree := TreeBlock040L57
abbrev F11B040L58 : RowFamilyTree := TreeBlock040L58
abbrev F11B040L59 : RowFamilyTree := TreeBlock040L59
abbrev F11B040L60 : RowFamilyTree := TreeBlock040L60
abbrev F11B040L61 : RowFamilyTree := TreeBlock040L61
abbrev F11B040L62 : RowFamilyTree := TreeBlock040L62
abbrev F11B040L63 : RowFamilyTree := TreeBlock040L63
abbrev F11B040 : RowFamilyTree := TreeBlock040
theorem F11B040L0_lift (row : List GridPoint) (h : FamilyMember row F11B040L0) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B040L1_lift (row : List GridPoint) (h : FamilyMember row F11B040L1) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B040L2_lift (row : List GridPoint) (h : FamilyMember row F11B040L2) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B040L3_lift (row : List GridPoint) (h : FamilyMember row F11B040L3) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B040L4_lift (row : List GridPoint) (h : FamilyMember row F11B040L4) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B040L5_lift (row : List GridPoint) (h : FamilyMember row F11B040L5) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B040L6_lift (row : List GridPoint) (h : FamilyMember row F11B040L6) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B040L7_lift (row : List GridPoint) (h : FamilyMember row F11B040L7) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B040L8_lift (row : List GridPoint) (h : FamilyMember row F11B040L8) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B040L9_lift (row : List GridPoint) (h : FamilyMember row F11B040L9) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B040L10_lift (row : List GridPoint) (h : FamilyMember row F11B040L10) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B040L11_lift (row : List GridPoint) (h : FamilyMember row F11B040L11) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B040L12_lift (row : List GridPoint) (h : FamilyMember row F11B040L12) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B040L13_lift (row : List GridPoint) (h : FamilyMember row F11B040L13) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B040L14_lift (row : List GridPoint) (h : FamilyMember row F11B040L14) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B040L15_lift (row : List GridPoint) (h : FamilyMember row F11B040L15) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B040L16_lift (row : List GridPoint) (h : FamilyMember row F11B040L16) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B040L17_lift (row : List GridPoint) (h : FamilyMember row F11B040L17) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B040L18_lift (row : List GridPoint) (h : FamilyMember row F11B040L18) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B040L19_lift (row : List GridPoint) (h : FamilyMember row F11B040L19) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B040L20_lift (row : List GridPoint) (h : FamilyMember row F11B040L20) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B040L21_lift (row : List GridPoint) (h : FamilyMember row F11B040L21) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B040L22_lift (row : List GridPoint) (h : FamilyMember row F11B040L22) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B040L23_lift (row : List GridPoint) (h : FamilyMember row F11B040L23) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B040L24_lift (row : List GridPoint) (h : FamilyMember row F11B040L24) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B040L25_lift (row : List GridPoint) (h : FamilyMember row F11B040L25) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B040L26_lift (row : List GridPoint) (h : FamilyMember row F11B040L26) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B040L27_lift (row : List GridPoint) (h : FamilyMember row F11B040L27) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B040L28_lift (row : List GridPoint) (h : FamilyMember row F11B040L28) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B040L29_lift (row : List GridPoint) (h : FamilyMember row F11B040L29) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B040L30_lift (row : List GridPoint) (h : FamilyMember row F11B040L30) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B040L31_lift (row : List GridPoint) (h : FamilyMember row F11B040L31) : FamilyMember row F11B040 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B040L32_lift (row : List GridPoint) (h : FamilyMember row F11B040L32) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B040L33_lift (row : List GridPoint) (h : FamilyMember row F11B040L33) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B040L34_lift (row : List GridPoint) (h : FamilyMember row F11B040L34) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B040L35_lift (row : List GridPoint) (h : FamilyMember row F11B040L35) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B040L36_lift (row : List GridPoint) (h : FamilyMember row F11B040L36) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B040L37_lift (row : List GridPoint) (h : FamilyMember row F11B040L37) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B040L38_lift (row : List GridPoint) (h : FamilyMember row F11B040L38) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B040L39_lift (row : List GridPoint) (h : FamilyMember row F11B040L39) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B040L40_lift (row : List GridPoint) (h : FamilyMember row F11B040L40) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B040L41_lift (row : List GridPoint) (h : FamilyMember row F11B040L41) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B040L42_lift (row : List GridPoint) (h : FamilyMember row F11B040L42) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B040L43_lift (row : List GridPoint) (h : FamilyMember row F11B040L43) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B040L44_lift (row : List GridPoint) (h : FamilyMember row F11B040L44) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B040L45_lift (row : List GridPoint) (h : FamilyMember row F11B040L45) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B040L46_lift (row : List GridPoint) (h : FamilyMember row F11B040L46) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B040L47_lift (row : List GridPoint) (h : FamilyMember row F11B040L47) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B040L48_lift (row : List GridPoint) (h : FamilyMember row F11B040L48) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B040L49_lift (row : List GridPoint) (h : FamilyMember row F11B040L49) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B040L50_lift (row : List GridPoint) (h : FamilyMember row F11B040L50) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B040L51_lift (row : List GridPoint) (h : FamilyMember row F11B040L51) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B040L52_lift (row : List GridPoint) (h : FamilyMember row F11B040L52) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B040L53_lift (row : List GridPoint) (h : FamilyMember row F11B040L53) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B040L54_lift (row : List GridPoint) (h : FamilyMember row F11B040L54) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B040L55_lift (row : List GridPoint) (h : FamilyMember row F11B040L55) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B040L56_lift (row : List GridPoint) (h : FamilyMember row F11B040L56) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B040L57_lift (row : List GridPoint) (h : FamilyMember row F11B040L57) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B040L58_lift (row : List GridPoint) (h : FamilyMember row F11B040L58) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B040L59_lift (row : List GridPoint) (h : FamilyMember row F11B040L59) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B040L60_lift (row : List GridPoint) (h : FamilyMember row F11B040L60) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B040L61_lift (row : List GridPoint) (h : FamilyMember row F11B040L61) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B040L62_lift (row : List GridPoint) (h : FamilyMember row F11B040L62) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B040L63_lift (row : List GridPoint) (h : FamilyMember row F11B040L63) : FamilyMember row F11B040 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
