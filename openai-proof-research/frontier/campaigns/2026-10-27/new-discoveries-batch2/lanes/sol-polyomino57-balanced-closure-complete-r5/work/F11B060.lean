import TreeBlock060
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B060L0 : RowFamilyTree := TreeBlock060L0
abbrev F11B060L1 : RowFamilyTree := TreeBlock060L1
abbrev F11B060L2 : RowFamilyTree := TreeBlock060L2
abbrev F11B060L3 : RowFamilyTree := TreeBlock060L3
abbrev F11B060L4 : RowFamilyTree := TreeBlock060L4
abbrev F11B060L5 : RowFamilyTree := TreeBlock060L5
abbrev F11B060L6 : RowFamilyTree := TreeBlock060L6
abbrev F11B060L7 : RowFamilyTree := TreeBlock060L7
abbrev F11B060L8 : RowFamilyTree := TreeBlock060L8
abbrev F11B060L9 : RowFamilyTree := TreeBlock060L9
abbrev F11B060L10 : RowFamilyTree := TreeBlock060L10
abbrev F11B060L11 : RowFamilyTree := TreeBlock060L11
abbrev F11B060L12 : RowFamilyTree := TreeBlock060L12
abbrev F11B060L13 : RowFamilyTree := TreeBlock060L13
abbrev F11B060L14 : RowFamilyTree := TreeBlock060L14
abbrev F11B060L15 : RowFamilyTree := TreeBlock060L15
abbrev F11B060L16 : RowFamilyTree := TreeBlock060L16
abbrev F11B060L17 : RowFamilyTree := TreeBlock060L17
abbrev F11B060L18 : RowFamilyTree := TreeBlock060L18
abbrev F11B060L19 : RowFamilyTree := TreeBlock060L19
abbrev F11B060L20 : RowFamilyTree := TreeBlock060L20
abbrev F11B060L21 : RowFamilyTree := TreeBlock060L21
abbrev F11B060L22 : RowFamilyTree := TreeBlock060L22
abbrev F11B060L23 : RowFamilyTree := TreeBlock060L23
abbrev F11B060L24 : RowFamilyTree := TreeBlock060L24
abbrev F11B060L25 : RowFamilyTree := TreeBlock060L25
abbrev F11B060L26 : RowFamilyTree := TreeBlock060L26
abbrev F11B060L27 : RowFamilyTree := TreeBlock060L27
abbrev F11B060L28 : RowFamilyTree := TreeBlock060L28
abbrev F11B060L29 : RowFamilyTree := TreeBlock060L29
abbrev F11B060L30 : RowFamilyTree := TreeBlock060L30
abbrev F11B060L31 : RowFamilyTree := TreeBlock060L31
abbrev F11B060L32 : RowFamilyTree := TreeBlock060L32
abbrev F11B060L33 : RowFamilyTree := TreeBlock060L33
abbrev F11B060L34 : RowFamilyTree := TreeBlock060L34
abbrev F11B060L35 : RowFamilyTree := TreeBlock060L35
abbrev F11B060L36 : RowFamilyTree := TreeBlock060L36
abbrev F11B060L37 : RowFamilyTree := TreeBlock060L37
abbrev F11B060L38 : RowFamilyTree := TreeBlock060L38
abbrev F11B060L39 : RowFamilyTree := TreeBlock060L39
abbrev F11B060L40 : RowFamilyTree := TreeBlock060L40
abbrev F11B060L41 : RowFamilyTree := TreeBlock060L41
abbrev F11B060L42 : RowFamilyTree := TreeBlock060L42
abbrev F11B060L43 : RowFamilyTree := TreeBlock060L43
abbrev F11B060L44 : RowFamilyTree := TreeBlock060L44
abbrev F11B060L45 : RowFamilyTree := TreeBlock060L45
abbrev F11B060L46 : RowFamilyTree := TreeBlock060L46
abbrev F11B060L47 : RowFamilyTree := TreeBlock060L47
abbrev F11B060L48 : RowFamilyTree := TreeBlock060L48
abbrev F11B060L49 : RowFamilyTree := TreeBlock060L49
abbrev F11B060L50 : RowFamilyTree := TreeBlock060L50
abbrev F11B060L51 : RowFamilyTree := TreeBlock060L51
abbrev F11B060L52 : RowFamilyTree := TreeBlock060L52
abbrev F11B060L53 : RowFamilyTree := TreeBlock060L53
abbrev F11B060L54 : RowFamilyTree := TreeBlock060L54
abbrev F11B060L55 : RowFamilyTree := TreeBlock060L55
abbrev F11B060L56 : RowFamilyTree := TreeBlock060L56
abbrev F11B060L57 : RowFamilyTree := TreeBlock060L57
abbrev F11B060L58 : RowFamilyTree := TreeBlock060L58
abbrev F11B060L59 : RowFamilyTree := TreeBlock060L59
abbrev F11B060L60 : RowFamilyTree := TreeBlock060L60
abbrev F11B060L61 : RowFamilyTree := TreeBlock060L61
abbrev F11B060L62 : RowFamilyTree := TreeBlock060L62
abbrev F11B060L63 : RowFamilyTree := TreeBlock060L63
abbrev F11B060 : RowFamilyTree := TreeBlock060
theorem F11B060L0_lift (row : List GridPoint) (h : FamilyMember row F11B060L0) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B060L1_lift (row : List GridPoint) (h : FamilyMember row F11B060L1) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B060L2_lift (row : List GridPoint) (h : FamilyMember row F11B060L2) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B060L3_lift (row : List GridPoint) (h : FamilyMember row F11B060L3) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B060L4_lift (row : List GridPoint) (h : FamilyMember row F11B060L4) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B060L5_lift (row : List GridPoint) (h : FamilyMember row F11B060L5) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B060L6_lift (row : List GridPoint) (h : FamilyMember row F11B060L6) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B060L7_lift (row : List GridPoint) (h : FamilyMember row F11B060L7) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B060L8_lift (row : List GridPoint) (h : FamilyMember row F11B060L8) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B060L9_lift (row : List GridPoint) (h : FamilyMember row F11B060L9) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B060L10_lift (row : List GridPoint) (h : FamilyMember row F11B060L10) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B060L11_lift (row : List GridPoint) (h : FamilyMember row F11B060L11) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B060L12_lift (row : List GridPoint) (h : FamilyMember row F11B060L12) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B060L13_lift (row : List GridPoint) (h : FamilyMember row F11B060L13) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B060L14_lift (row : List GridPoint) (h : FamilyMember row F11B060L14) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B060L15_lift (row : List GridPoint) (h : FamilyMember row F11B060L15) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B060L16_lift (row : List GridPoint) (h : FamilyMember row F11B060L16) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B060L17_lift (row : List GridPoint) (h : FamilyMember row F11B060L17) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B060L18_lift (row : List GridPoint) (h : FamilyMember row F11B060L18) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B060L19_lift (row : List GridPoint) (h : FamilyMember row F11B060L19) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B060L20_lift (row : List GridPoint) (h : FamilyMember row F11B060L20) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B060L21_lift (row : List GridPoint) (h : FamilyMember row F11B060L21) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B060L22_lift (row : List GridPoint) (h : FamilyMember row F11B060L22) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B060L23_lift (row : List GridPoint) (h : FamilyMember row F11B060L23) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B060L24_lift (row : List GridPoint) (h : FamilyMember row F11B060L24) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B060L25_lift (row : List GridPoint) (h : FamilyMember row F11B060L25) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B060L26_lift (row : List GridPoint) (h : FamilyMember row F11B060L26) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B060L27_lift (row : List GridPoint) (h : FamilyMember row F11B060L27) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B060L28_lift (row : List GridPoint) (h : FamilyMember row F11B060L28) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B060L29_lift (row : List GridPoint) (h : FamilyMember row F11B060L29) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B060L30_lift (row : List GridPoint) (h : FamilyMember row F11B060L30) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B060L31_lift (row : List GridPoint) (h : FamilyMember row F11B060L31) : FamilyMember row F11B060 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B060L32_lift (row : List GridPoint) (h : FamilyMember row F11B060L32) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B060L33_lift (row : List GridPoint) (h : FamilyMember row F11B060L33) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B060L34_lift (row : List GridPoint) (h : FamilyMember row F11B060L34) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B060L35_lift (row : List GridPoint) (h : FamilyMember row F11B060L35) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B060L36_lift (row : List GridPoint) (h : FamilyMember row F11B060L36) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B060L37_lift (row : List GridPoint) (h : FamilyMember row F11B060L37) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B060L38_lift (row : List GridPoint) (h : FamilyMember row F11B060L38) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B060L39_lift (row : List GridPoint) (h : FamilyMember row F11B060L39) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B060L40_lift (row : List GridPoint) (h : FamilyMember row F11B060L40) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B060L41_lift (row : List GridPoint) (h : FamilyMember row F11B060L41) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B060L42_lift (row : List GridPoint) (h : FamilyMember row F11B060L42) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B060L43_lift (row : List GridPoint) (h : FamilyMember row F11B060L43) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B060L44_lift (row : List GridPoint) (h : FamilyMember row F11B060L44) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B060L45_lift (row : List GridPoint) (h : FamilyMember row F11B060L45) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B060L46_lift (row : List GridPoint) (h : FamilyMember row F11B060L46) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B060L47_lift (row : List GridPoint) (h : FamilyMember row F11B060L47) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B060L48_lift (row : List GridPoint) (h : FamilyMember row F11B060L48) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B060L49_lift (row : List GridPoint) (h : FamilyMember row F11B060L49) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B060L50_lift (row : List GridPoint) (h : FamilyMember row F11B060L50) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B060L51_lift (row : List GridPoint) (h : FamilyMember row F11B060L51) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B060L52_lift (row : List GridPoint) (h : FamilyMember row F11B060L52) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B060L53_lift (row : List GridPoint) (h : FamilyMember row F11B060L53) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B060L54_lift (row : List GridPoint) (h : FamilyMember row F11B060L54) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B060L55_lift (row : List GridPoint) (h : FamilyMember row F11B060L55) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B060L56_lift (row : List GridPoint) (h : FamilyMember row F11B060L56) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B060L57_lift (row : List GridPoint) (h : FamilyMember row F11B060L57) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B060L58_lift (row : List GridPoint) (h : FamilyMember row F11B060L58) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B060L59_lift (row : List GridPoint) (h : FamilyMember row F11B060L59) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B060L60_lift (row : List GridPoint) (h : FamilyMember row F11B060L60) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B060L61_lift (row : List GridPoint) (h : FamilyMember row F11B060L61) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B060L62_lift (row : List GridPoint) (h : FamilyMember row F11B060L62) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B060L63_lift (row : List GridPoint) (h : FamilyMember row F11B060L63) : FamilyMember row F11B060 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
