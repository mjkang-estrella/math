import TreeBlock003
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B003L0 : RowFamilyTree := TreeBlock003L0
abbrev F11B003L1 : RowFamilyTree := TreeBlock003L1
abbrev F11B003L2 : RowFamilyTree := TreeBlock003L2
abbrev F11B003L3 : RowFamilyTree := TreeBlock003L3
abbrev F11B003L4 : RowFamilyTree := TreeBlock003L4
abbrev F11B003L5 : RowFamilyTree := TreeBlock003L5
abbrev F11B003L6 : RowFamilyTree := TreeBlock003L6
abbrev F11B003L7 : RowFamilyTree := TreeBlock003L7
abbrev F11B003L8 : RowFamilyTree := TreeBlock003L8
abbrev F11B003L9 : RowFamilyTree := TreeBlock003L9
abbrev F11B003L10 : RowFamilyTree := TreeBlock003L10
abbrev F11B003L11 : RowFamilyTree := TreeBlock003L11
abbrev F11B003L12 : RowFamilyTree := TreeBlock003L12
abbrev F11B003L13 : RowFamilyTree := TreeBlock003L13
abbrev F11B003L14 : RowFamilyTree := TreeBlock003L14
abbrev F11B003L15 : RowFamilyTree := TreeBlock003L15
abbrev F11B003L16 : RowFamilyTree := TreeBlock003L16
abbrev F11B003L17 : RowFamilyTree := TreeBlock003L17
abbrev F11B003L18 : RowFamilyTree := TreeBlock003L18
abbrev F11B003L19 : RowFamilyTree := TreeBlock003L19
abbrev F11B003L20 : RowFamilyTree := TreeBlock003L20
abbrev F11B003L21 : RowFamilyTree := TreeBlock003L21
abbrev F11B003L22 : RowFamilyTree := TreeBlock003L22
abbrev F11B003L23 : RowFamilyTree := TreeBlock003L23
abbrev F11B003L24 : RowFamilyTree := TreeBlock003L24
abbrev F11B003L25 : RowFamilyTree := TreeBlock003L25
abbrev F11B003L26 : RowFamilyTree := TreeBlock003L26
abbrev F11B003L27 : RowFamilyTree := TreeBlock003L27
abbrev F11B003L28 : RowFamilyTree := TreeBlock003L28
abbrev F11B003L29 : RowFamilyTree := TreeBlock003L29
abbrev F11B003L30 : RowFamilyTree := TreeBlock003L30
abbrev F11B003L31 : RowFamilyTree := TreeBlock003L31
abbrev F11B003L32 : RowFamilyTree := TreeBlock003L32
abbrev F11B003L33 : RowFamilyTree := TreeBlock003L33
abbrev F11B003L34 : RowFamilyTree := TreeBlock003L34
abbrev F11B003L35 : RowFamilyTree := TreeBlock003L35
abbrev F11B003L36 : RowFamilyTree := TreeBlock003L36
abbrev F11B003L37 : RowFamilyTree := TreeBlock003L37
abbrev F11B003L38 : RowFamilyTree := TreeBlock003L38
abbrev F11B003L39 : RowFamilyTree := TreeBlock003L39
abbrev F11B003L40 : RowFamilyTree := TreeBlock003L40
abbrev F11B003L41 : RowFamilyTree := TreeBlock003L41
abbrev F11B003L42 : RowFamilyTree := TreeBlock003L42
abbrev F11B003L43 : RowFamilyTree := TreeBlock003L43
abbrev F11B003L44 : RowFamilyTree := TreeBlock003L44
abbrev F11B003L45 : RowFamilyTree := TreeBlock003L45
abbrev F11B003L46 : RowFamilyTree := TreeBlock003L46
abbrev F11B003L47 : RowFamilyTree := TreeBlock003L47
abbrev F11B003L48 : RowFamilyTree := TreeBlock003L48
abbrev F11B003L49 : RowFamilyTree := TreeBlock003L49
abbrev F11B003L50 : RowFamilyTree := TreeBlock003L50
abbrev F11B003L51 : RowFamilyTree := TreeBlock003L51
abbrev F11B003L52 : RowFamilyTree := TreeBlock003L52
abbrev F11B003L53 : RowFamilyTree := TreeBlock003L53
abbrev F11B003L54 : RowFamilyTree := TreeBlock003L54
abbrev F11B003L55 : RowFamilyTree := TreeBlock003L55
abbrev F11B003L56 : RowFamilyTree := TreeBlock003L56
abbrev F11B003L57 : RowFamilyTree := TreeBlock003L57
abbrev F11B003L58 : RowFamilyTree := TreeBlock003L58
abbrev F11B003L59 : RowFamilyTree := TreeBlock003L59
abbrev F11B003L60 : RowFamilyTree := TreeBlock003L60
abbrev F11B003L61 : RowFamilyTree := TreeBlock003L61
abbrev F11B003L62 : RowFamilyTree := TreeBlock003L62
abbrev F11B003L63 : RowFamilyTree := TreeBlock003L63
abbrev F11B003 : RowFamilyTree := TreeBlock003
theorem F11B003L0_lift (row : List GridPoint) (h : FamilyMember row F11B003L0) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B003L1_lift (row : List GridPoint) (h : FamilyMember row F11B003L1) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B003L2_lift (row : List GridPoint) (h : FamilyMember row F11B003L2) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B003L3_lift (row : List GridPoint) (h : FamilyMember row F11B003L3) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B003L4_lift (row : List GridPoint) (h : FamilyMember row F11B003L4) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B003L5_lift (row : List GridPoint) (h : FamilyMember row F11B003L5) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B003L6_lift (row : List GridPoint) (h : FamilyMember row F11B003L6) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B003L7_lift (row : List GridPoint) (h : FamilyMember row F11B003L7) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B003L8_lift (row : List GridPoint) (h : FamilyMember row F11B003L8) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B003L9_lift (row : List GridPoint) (h : FamilyMember row F11B003L9) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B003L10_lift (row : List GridPoint) (h : FamilyMember row F11B003L10) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B003L11_lift (row : List GridPoint) (h : FamilyMember row F11B003L11) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B003L12_lift (row : List GridPoint) (h : FamilyMember row F11B003L12) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B003L13_lift (row : List GridPoint) (h : FamilyMember row F11B003L13) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B003L14_lift (row : List GridPoint) (h : FamilyMember row F11B003L14) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B003L15_lift (row : List GridPoint) (h : FamilyMember row F11B003L15) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B003L16_lift (row : List GridPoint) (h : FamilyMember row F11B003L16) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B003L17_lift (row : List GridPoint) (h : FamilyMember row F11B003L17) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B003L18_lift (row : List GridPoint) (h : FamilyMember row F11B003L18) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B003L19_lift (row : List GridPoint) (h : FamilyMember row F11B003L19) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B003L20_lift (row : List GridPoint) (h : FamilyMember row F11B003L20) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B003L21_lift (row : List GridPoint) (h : FamilyMember row F11B003L21) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B003L22_lift (row : List GridPoint) (h : FamilyMember row F11B003L22) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B003L23_lift (row : List GridPoint) (h : FamilyMember row F11B003L23) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B003L24_lift (row : List GridPoint) (h : FamilyMember row F11B003L24) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B003L25_lift (row : List GridPoint) (h : FamilyMember row F11B003L25) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B003L26_lift (row : List GridPoint) (h : FamilyMember row F11B003L26) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B003L27_lift (row : List GridPoint) (h : FamilyMember row F11B003L27) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B003L28_lift (row : List GridPoint) (h : FamilyMember row F11B003L28) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B003L29_lift (row : List GridPoint) (h : FamilyMember row F11B003L29) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B003L30_lift (row : List GridPoint) (h : FamilyMember row F11B003L30) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B003L31_lift (row : List GridPoint) (h : FamilyMember row F11B003L31) : FamilyMember row F11B003 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B003L32_lift (row : List GridPoint) (h : FamilyMember row F11B003L32) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B003L33_lift (row : List GridPoint) (h : FamilyMember row F11B003L33) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B003L34_lift (row : List GridPoint) (h : FamilyMember row F11B003L34) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B003L35_lift (row : List GridPoint) (h : FamilyMember row F11B003L35) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B003L36_lift (row : List GridPoint) (h : FamilyMember row F11B003L36) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B003L37_lift (row : List GridPoint) (h : FamilyMember row F11B003L37) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B003L38_lift (row : List GridPoint) (h : FamilyMember row F11B003L38) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B003L39_lift (row : List GridPoint) (h : FamilyMember row F11B003L39) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B003L40_lift (row : List GridPoint) (h : FamilyMember row F11B003L40) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B003L41_lift (row : List GridPoint) (h : FamilyMember row F11B003L41) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B003L42_lift (row : List GridPoint) (h : FamilyMember row F11B003L42) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B003L43_lift (row : List GridPoint) (h : FamilyMember row F11B003L43) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B003L44_lift (row : List GridPoint) (h : FamilyMember row F11B003L44) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B003L45_lift (row : List GridPoint) (h : FamilyMember row F11B003L45) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B003L46_lift (row : List GridPoint) (h : FamilyMember row F11B003L46) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B003L47_lift (row : List GridPoint) (h : FamilyMember row F11B003L47) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B003L48_lift (row : List GridPoint) (h : FamilyMember row F11B003L48) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B003L49_lift (row : List GridPoint) (h : FamilyMember row F11B003L49) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B003L50_lift (row : List GridPoint) (h : FamilyMember row F11B003L50) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B003L51_lift (row : List GridPoint) (h : FamilyMember row F11B003L51) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B003L52_lift (row : List GridPoint) (h : FamilyMember row F11B003L52) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B003L53_lift (row : List GridPoint) (h : FamilyMember row F11B003L53) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B003L54_lift (row : List GridPoint) (h : FamilyMember row F11B003L54) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B003L55_lift (row : List GridPoint) (h : FamilyMember row F11B003L55) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B003L56_lift (row : List GridPoint) (h : FamilyMember row F11B003L56) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B003L57_lift (row : List GridPoint) (h : FamilyMember row F11B003L57) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B003L58_lift (row : List GridPoint) (h : FamilyMember row F11B003L58) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B003L59_lift (row : List GridPoint) (h : FamilyMember row F11B003L59) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B003L60_lift (row : List GridPoint) (h : FamilyMember row F11B003L60) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B003L61_lift (row : List GridPoint) (h : FamilyMember row F11B003L61) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B003L62_lift (row : List GridPoint) (h : FamilyMember row F11B003L62) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B003L63_lift (row : List GridPoint) (h : FamilyMember row F11B003L63) : FamilyMember row F11B003 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
