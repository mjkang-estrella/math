import TreeBlock008
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B008L0 : RowFamilyTree := TreeBlock008L0
abbrev F11B008L1 : RowFamilyTree := TreeBlock008L1
abbrev F11B008L2 : RowFamilyTree := TreeBlock008L2
abbrev F11B008L3 : RowFamilyTree := TreeBlock008L3
abbrev F11B008L4 : RowFamilyTree := TreeBlock008L4
abbrev F11B008L5 : RowFamilyTree := TreeBlock008L5
abbrev F11B008L6 : RowFamilyTree := TreeBlock008L6
abbrev F11B008L7 : RowFamilyTree := TreeBlock008L7
abbrev F11B008L8 : RowFamilyTree := TreeBlock008L8
abbrev F11B008L9 : RowFamilyTree := TreeBlock008L9
abbrev F11B008L10 : RowFamilyTree := TreeBlock008L10
abbrev F11B008L11 : RowFamilyTree := TreeBlock008L11
abbrev F11B008L12 : RowFamilyTree := TreeBlock008L12
abbrev F11B008L13 : RowFamilyTree := TreeBlock008L13
abbrev F11B008L14 : RowFamilyTree := TreeBlock008L14
abbrev F11B008L15 : RowFamilyTree := TreeBlock008L15
abbrev F11B008L16 : RowFamilyTree := TreeBlock008L16
abbrev F11B008L17 : RowFamilyTree := TreeBlock008L17
abbrev F11B008L18 : RowFamilyTree := TreeBlock008L18
abbrev F11B008L19 : RowFamilyTree := TreeBlock008L19
abbrev F11B008L20 : RowFamilyTree := TreeBlock008L20
abbrev F11B008L21 : RowFamilyTree := TreeBlock008L21
abbrev F11B008L22 : RowFamilyTree := TreeBlock008L22
abbrev F11B008L23 : RowFamilyTree := TreeBlock008L23
abbrev F11B008L24 : RowFamilyTree := TreeBlock008L24
abbrev F11B008L25 : RowFamilyTree := TreeBlock008L25
abbrev F11B008L26 : RowFamilyTree := TreeBlock008L26
abbrev F11B008L27 : RowFamilyTree := TreeBlock008L27
abbrev F11B008L28 : RowFamilyTree := TreeBlock008L28
abbrev F11B008L29 : RowFamilyTree := TreeBlock008L29
abbrev F11B008L30 : RowFamilyTree := TreeBlock008L30
abbrev F11B008L31 : RowFamilyTree := TreeBlock008L31
abbrev F11B008L32 : RowFamilyTree := TreeBlock008L32
abbrev F11B008L33 : RowFamilyTree := TreeBlock008L33
abbrev F11B008L34 : RowFamilyTree := TreeBlock008L34
abbrev F11B008L35 : RowFamilyTree := TreeBlock008L35
abbrev F11B008L36 : RowFamilyTree := TreeBlock008L36
abbrev F11B008L37 : RowFamilyTree := TreeBlock008L37
abbrev F11B008L38 : RowFamilyTree := TreeBlock008L38
abbrev F11B008L39 : RowFamilyTree := TreeBlock008L39
abbrev F11B008L40 : RowFamilyTree := TreeBlock008L40
abbrev F11B008L41 : RowFamilyTree := TreeBlock008L41
abbrev F11B008L42 : RowFamilyTree := TreeBlock008L42
abbrev F11B008L43 : RowFamilyTree := TreeBlock008L43
abbrev F11B008L44 : RowFamilyTree := TreeBlock008L44
abbrev F11B008L45 : RowFamilyTree := TreeBlock008L45
abbrev F11B008L46 : RowFamilyTree := TreeBlock008L46
abbrev F11B008L47 : RowFamilyTree := TreeBlock008L47
abbrev F11B008L48 : RowFamilyTree := TreeBlock008L48
abbrev F11B008L49 : RowFamilyTree := TreeBlock008L49
abbrev F11B008L50 : RowFamilyTree := TreeBlock008L50
abbrev F11B008L51 : RowFamilyTree := TreeBlock008L51
abbrev F11B008L52 : RowFamilyTree := TreeBlock008L52
abbrev F11B008L53 : RowFamilyTree := TreeBlock008L53
abbrev F11B008L54 : RowFamilyTree := TreeBlock008L54
abbrev F11B008L55 : RowFamilyTree := TreeBlock008L55
abbrev F11B008L56 : RowFamilyTree := TreeBlock008L56
abbrev F11B008L57 : RowFamilyTree := TreeBlock008L57
abbrev F11B008L58 : RowFamilyTree := TreeBlock008L58
abbrev F11B008L59 : RowFamilyTree := TreeBlock008L59
abbrev F11B008L60 : RowFamilyTree := TreeBlock008L60
abbrev F11B008L61 : RowFamilyTree := TreeBlock008L61
abbrev F11B008L62 : RowFamilyTree := TreeBlock008L62
abbrev F11B008L63 : RowFamilyTree := TreeBlock008L63
abbrev F11B008 : RowFamilyTree := TreeBlock008
theorem F11B008L0_lift (row : List GridPoint) (h : FamilyMember row F11B008L0) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B008L1_lift (row : List GridPoint) (h : FamilyMember row F11B008L1) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B008L2_lift (row : List GridPoint) (h : FamilyMember row F11B008L2) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B008L3_lift (row : List GridPoint) (h : FamilyMember row F11B008L3) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B008L4_lift (row : List GridPoint) (h : FamilyMember row F11B008L4) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B008L5_lift (row : List GridPoint) (h : FamilyMember row F11B008L5) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B008L6_lift (row : List GridPoint) (h : FamilyMember row F11B008L6) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B008L7_lift (row : List GridPoint) (h : FamilyMember row F11B008L7) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B008L8_lift (row : List GridPoint) (h : FamilyMember row F11B008L8) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B008L9_lift (row : List GridPoint) (h : FamilyMember row F11B008L9) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B008L10_lift (row : List GridPoint) (h : FamilyMember row F11B008L10) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B008L11_lift (row : List GridPoint) (h : FamilyMember row F11B008L11) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B008L12_lift (row : List GridPoint) (h : FamilyMember row F11B008L12) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B008L13_lift (row : List GridPoint) (h : FamilyMember row F11B008L13) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B008L14_lift (row : List GridPoint) (h : FamilyMember row F11B008L14) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B008L15_lift (row : List GridPoint) (h : FamilyMember row F11B008L15) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B008L16_lift (row : List GridPoint) (h : FamilyMember row F11B008L16) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B008L17_lift (row : List GridPoint) (h : FamilyMember row F11B008L17) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B008L18_lift (row : List GridPoint) (h : FamilyMember row F11B008L18) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B008L19_lift (row : List GridPoint) (h : FamilyMember row F11B008L19) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B008L20_lift (row : List GridPoint) (h : FamilyMember row F11B008L20) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B008L21_lift (row : List GridPoint) (h : FamilyMember row F11B008L21) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B008L22_lift (row : List GridPoint) (h : FamilyMember row F11B008L22) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B008L23_lift (row : List GridPoint) (h : FamilyMember row F11B008L23) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B008L24_lift (row : List GridPoint) (h : FamilyMember row F11B008L24) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B008L25_lift (row : List GridPoint) (h : FamilyMember row F11B008L25) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B008L26_lift (row : List GridPoint) (h : FamilyMember row F11B008L26) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B008L27_lift (row : List GridPoint) (h : FamilyMember row F11B008L27) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B008L28_lift (row : List GridPoint) (h : FamilyMember row F11B008L28) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B008L29_lift (row : List GridPoint) (h : FamilyMember row F11B008L29) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B008L30_lift (row : List GridPoint) (h : FamilyMember row F11B008L30) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B008L31_lift (row : List GridPoint) (h : FamilyMember row F11B008L31) : FamilyMember row F11B008 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B008L32_lift (row : List GridPoint) (h : FamilyMember row F11B008L32) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B008L33_lift (row : List GridPoint) (h : FamilyMember row F11B008L33) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B008L34_lift (row : List GridPoint) (h : FamilyMember row F11B008L34) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B008L35_lift (row : List GridPoint) (h : FamilyMember row F11B008L35) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B008L36_lift (row : List GridPoint) (h : FamilyMember row F11B008L36) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B008L37_lift (row : List GridPoint) (h : FamilyMember row F11B008L37) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B008L38_lift (row : List GridPoint) (h : FamilyMember row F11B008L38) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B008L39_lift (row : List GridPoint) (h : FamilyMember row F11B008L39) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B008L40_lift (row : List GridPoint) (h : FamilyMember row F11B008L40) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B008L41_lift (row : List GridPoint) (h : FamilyMember row F11B008L41) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B008L42_lift (row : List GridPoint) (h : FamilyMember row F11B008L42) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B008L43_lift (row : List GridPoint) (h : FamilyMember row F11B008L43) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B008L44_lift (row : List GridPoint) (h : FamilyMember row F11B008L44) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B008L45_lift (row : List GridPoint) (h : FamilyMember row F11B008L45) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B008L46_lift (row : List GridPoint) (h : FamilyMember row F11B008L46) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B008L47_lift (row : List GridPoint) (h : FamilyMember row F11B008L47) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B008L48_lift (row : List GridPoint) (h : FamilyMember row F11B008L48) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B008L49_lift (row : List GridPoint) (h : FamilyMember row F11B008L49) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B008L50_lift (row : List GridPoint) (h : FamilyMember row F11B008L50) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B008L51_lift (row : List GridPoint) (h : FamilyMember row F11B008L51) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B008L52_lift (row : List GridPoint) (h : FamilyMember row F11B008L52) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B008L53_lift (row : List GridPoint) (h : FamilyMember row F11B008L53) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B008L54_lift (row : List GridPoint) (h : FamilyMember row F11B008L54) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B008L55_lift (row : List GridPoint) (h : FamilyMember row F11B008L55) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B008L56_lift (row : List GridPoint) (h : FamilyMember row F11B008L56) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B008L57_lift (row : List GridPoint) (h : FamilyMember row F11B008L57) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B008L58_lift (row : List GridPoint) (h : FamilyMember row F11B008L58) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B008L59_lift (row : List GridPoint) (h : FamilyMember row F11B008L59) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B008L60_lift (row : List GridPoint) (h : FamilyMember row F11B008L60) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B008L61_lift (row : List GridPoint) (h : FamilyMember row F11B008L61) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B008L62_lift (row : List GridPoint) (h : FamilyMember row F11B008L62) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B008L63_lift (row : List GridPoint) (h : FamilyMember row F11B008L63) : FamilyMember row F11B008 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
