import TreeBlock030
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B030L0 : RowFamilyTree := TreeBlock030L0
abbrev F11B030L1 : RowFamilyTree := TreeBlock030L1
abbrev F11B030L2 : RowFamilyTree := TreeBlock030L2
abbrev F11B030L3 : RowFamilyTree := TreeBlock030L3
abbrev F11B030L4 : RowFamilyTree := TreeBlock030L4
abbrev F11B030L5 : RowFamilyTree := TreeBlock030L5
abbrev F11B030L6 : RowFamilyTree := TreeBlock030L6
abbrev F11B030L7 : RowFamilyTree := TreeBlock030L7
abbrev F11B030L8 : RowFamilyTree := TreeBlock030L8
abbrev F11B030L9 : RowFamilyTree := TreeBlock030L9
abbrev F11B030L10 : RowFamilyTree := TreeBlock030L10
abbrev F11B030L11 : RowFamilyTree := TreeBlock030L11
abbrev F11B030L12 : RowFamilyTree := TreeBlock030L12
abbrev F11B030L13 : RowFamilyTree := TreeBlock030L13
abbrev F11B030L14 : RowFamilyTree := TreeBlock030L14
abbrev F11B030L15 : RowFamilyTree := TreeBlock030L15
abbrev F11B030L16 : RowFamilyTree := TreeBlock030L16
abbrev F11B030L17 : RowFamilyTree := TreeBlock030L17
abbrev F11B030L18 : RowFamilyTree := TreeBlock030L18
abbrev F11B030L19 : RowFamilyTree := TreeBlock030L19
abbrev F11B030L20 : RowFamilyTree := TreeBlock030L20
abbrev F11B030L21 : RowFamilyTree := TreeBlock030L21
abbrev F11B030L22 : RowFamilyTree := TreeBlock030L22
abbrev F11B030L23 : RowFamilyTree := TreeBlock030L23
abbrev F11B030L24 : RowFamilyTree := TreeBlock030L24
abbrev F11B030L25 : RowFamilyTree := TreeBlock030L25
abbrev F11B030L26 : RowFamilyTree := TreeBlock030L26
abbrev F11B030L27 : RowFamilyTree := TreeBlock030L27
abbrev F11B030L28 : RowFamilyTree := TreeBlock030L28
abbrev F11B030L29 : RowFamilyTree := TreeBlock030L29
abbrev F11B030L30 : RowFamilyTree := TreeBlock030L30
abbrev F11B030L31 : RowFamilyTree := TreeBlock030L31
abbrev F11B030L32 : RowFamilyTree := TreeBlock030L32
abbrev F11B030L33 : RowFamilyTree := TreeBlock030L33
abbrev F11B030L34 : RowFamilyTree := TreeBlock030L34
abbrev F11B030L35 : RowFamilyTree := TreeBlock030L35
abbrev F11B030L36 : RowFamilyTree := TreeBlock030L36
abbrev F11B030L37 : RowFamilyTree := TreeBlock030L37
abbrev F11B030L38 : RowFamilyTree := TreeBlock030L38
abbrev F11B030L39 : RowFamilyTree := TreeBlock030L39
abbrev F11B030L40 : RowFamilyTree := TreeBlock030L40
abbrev F11B030L41 : RowFamilyTree := TreeBlock030L41
abbrev F11B030L42 : RowFamilyTree := TreeBlock030L42
abbrev F11B030L43 : RowFamilyTree := TreeBlock030L43
abbrev F11B030L44 : RowFamilyTree := TreeBlock030L44
abbrev F11B030L45 : RowFamilyTree := TreeBlock030L45
abbrev F11B030L46 : RowFamilyTree := TreeBlock030L46
abbrev F11B030L47 : RowFamilyTree := TreeBlock030L47
abbrev F11B030L48 : RowFamilyTree := TreeBlock030L48
abbrev F11B030L49 : RowFamilyTree := TreeBlock030L49
abbrev F11B030L50 : RowFamilyTree := TreeBlock030L50
abbrev F11B030L51 : RowFamilyTree := TreeBlock030L51
abbrev F11B030L52 : RowFamilyTree := TreeBlock030L52
abbrev F11B030L53 : RowFamilyTree := TreeBlock030L53
abbrev F11B030L54 : RowFamilyTree := TreeBlock030L54
abbrev F11B030L55 : RowFamilyTree := TreeBlock030L55
abbrev F11B030L56 : RowFamilyTree := TreeBlock030L56
abbrev F11B030L57 : RowFamilyTree := TreeBlock030L57
abbrev F11B030L58 : RowFamilyTree := TreeBlock030L58
abbrev F11B030L59 : RowFamilyTree := TreeBlock030L59
abbrev F11B030L60 : RowFamilyTree := TreeBlock030L60
abbrev F11B030L61 : RowFamilyTree := TreeBlock030L61
abbrev F11B030L62 : RowFamilyTree := TreeBlock030L62
abbrev F11B030L63 : RowFamilyTree := TreeBlock030L63
abbrev F11B030 : RowFamilyTree := TreeBlock030
theorem F11B030L0_lift (row : List GridPoint) (h : FamilyMember row F11B030L0) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B030L1_lift (row : List GridPoint) (h : FamilyMember row F11B030L1) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B030L2_lift (row : List GridPoint) (h : FamilyMember row F11B030L2) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B030L3_lift (row : List GridPoint) (h : FamilyMember row F11B030L3) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B030L4_lift (row : List GridPoint) (h : FamilyMember row F11B030L4) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B030L5_lift (row : List GridPoint) (h : FamilyMember row F11B030L5) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B030L6_lift (row : List GridPoint) (h : FamilyMember row F11B030L6) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B030L7_lift (row : List GridPoint) (h : FamilyMember row F11B030L7) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B030L8_lift (row : List GridPoint) (h : FamilyMember row F11B030L8) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B030L9_lift (row : List GridPoint) (h : FamilyMember row F11B030L9) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B030L10_lift (row : List GridPoint) (h : FamilyMember row F11B030L10) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B030L11_lift (row : List GridPoint) (h : FamilyMember row F11B030L11) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B030L12_lift (row : List GridPoint) (h : FamilyMember row F11B030L12) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B030L13_lift (row : List GridPoint) (h : FamilyMember row F11B030L13) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B030L14_lift (row : List GridPoint) (h : FamilyMember row F11B030L14) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B030L15_lift (row : List GridPoint) (h : FamilyMember row F11B030L15) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B030L16_lift (row : List GridPoint) (h : FamilyMember row F11B030L16) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B030L17_lift (row : List GridPoint) (h : FamilyMember row F11B030L17) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B030L18_lift (row : List GridPoint) (h : FamilyMember row F11B030L18) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B030L19_lift (row : List GridPoint) (h : FamilyMember row F11B030L19) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B030L20_lift (row : List GridPoint) (h : FamilyMember row F11B030L20) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B030L21_lift (row : List GridPoint) (h : FamilyMember row F11B030L21) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B030L22_lift (row : List GridPoint) (h : FamilyMember row F11B030L22) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B030L23_lift (row : List GridPoint) (h : FamilyMember row F11B030L23) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B030L24_lift (row : List GridPoint) (h : FamilyMember row F11B030L24) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B030L25_lift (row : List GridPoint) (h : FamilyMember row F11B030L25) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B030L26_lift (row : List GridPoint) (h : FamilyMember row F11B030L26) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B030L27_lift (row : List GridPoint) (h : FamilyMember row F11B030L27) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B030L28_lift (row : List GridPoint) (h : FamilyMember row F11B030L28) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B030L29_lift (row : List GridPoint) (h : FamilyMember row F11B030L29) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B030L30_lift (row : List GridPoint) (h : FamilyMember row F11B030L30) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B030L31_lift (row : List GridPoint) (h : FamilyMember row F11B030L31) : FamilyMember row F11B030 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B030L32_lift (row : List GridPoint) (h : FamilyMember row F11B030L32) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B030L33_lift (row : List GridPoint) (h : FamilyMember row F11B030L33) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B030L34_lift (row : List GridPoint) (h : FamilyMember row F11B030L34) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B030L35_lift (row : List GridPoint) (h : FamilyMember row F11B030L35) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B030L36_lift (row : List GridPoint) (h : FamilyMember row F11B030L36) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B030L37_lift (row : List GridPoint) (h : FamilyMember row F11B030L37) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B030L38_lift (row : List GridPoint) (h : FamilyMember row F11B030L38) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B030L39_lift (row : List GridPoint) (h : FamilyMember row F11B030L39) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B030L40_lift (row : List GridPoint) (h : FamilyMember row F11B030L40) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B030L41_lift (row : List GridPoint) (h : FamilyMember row F11B030L41) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B030L42_lift (row : List GridPoint) (h : FamilyMember row F11B030L42) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B030L43_lift (row : List GridPoint) (h : FamilyMember row F11B030L43) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B030L44_lift (row : List GridPoint) (h : FamilyMember row F11B030L44) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B030L45_lift (row : List GridPoint) (h : FamilyMember row F11B030L45) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B030L46_lift (row : List GridPoint) (h : FamilyMember row F11B030L46) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B030L47_lift (row : List GridPoint) (h : FamilyMember row F11B030L47) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B030L48_lift (row : List GridPoint) (h : FamilyMember row F11B030L48) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B030L49_lift (row : List GridPoint) (h : FamilyMember row F11B030L49) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B030L50_lift (row : List GridPoint) (h : FamilyMember row F11B030L50) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B030L51_lift (row : List GridPoint) (h : FamilyMember row F11B030L51) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B030L52_lift (row : List GridPoint) (h : FamilyMember row F11B030L52) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B030L53_lift (row : List GridPoint) (h : FamilyMember row F11B030L53) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B030L54_lift (row : List GridPoint) (h : FamilyMember row F11B030L54) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B030L55_lift (row : List GridPoint) (h : FamilyMember row F11B030L55) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B030L56_lift (row : List GridPoint) (h : FamilyMember row F11B030L56) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B030L57_lift (row : List GridPoint) (h : FamilyMember row F11B030L57) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B030L58_lift (row : List GridPoint) (h : FamilyMember row F11B030L58) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B030L59_lift (row : List GridPoint) (h : FamilyMember row F11B030L59) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B030L60_lift (row : List GridPoint) (h : FamilyMember row F11B030L60) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B030L61_lift (row : List GridPoint) (h : FamilyMember row F11B030L61) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B030L62_lift (row : List GridPoint) (h : FamilyMember row F11B030L62) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B030L63_lift (row : List GridPoint) (h : FamilyMember row F11B030L63) : FamilyMember row F11B030 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
