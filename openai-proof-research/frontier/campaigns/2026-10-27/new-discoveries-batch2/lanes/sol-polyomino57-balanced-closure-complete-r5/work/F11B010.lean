import TreeBlock010
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B010L0 : RowFamilyTree := TreeBlock010L0
abbrev F11B010L1 : RowFamilyTree := TreeBlock010L1
abbrev F11B010L2 : RowFamilyTree := TreeBlock010L2
abbrev F11B010L3 : RowFamilyTree := TreeBlock010L3
abbrev F11B010L4 : RowFamilyTree := TreeBlock010L4
abbrev F11B010L5 : RowFamilyTree := TreeBlock010L5
abbrev F11B010L6 : RowFamilyTree := TreeBlock010L6
abbrev F11B010L7 : RowFamilyTree := TreeBlock010L7
abbrev F11B010L8 : RowFamilyTree := TreeBlock010L8
abbrev F11B010L9 : RowFamilyTree := TreeBlock010L9
abbrev F11B010L10 : RowFamilyTree := TreeBlock010L10
abbrev F11B010L11 : RowFamilyTree := TreeBlock010L11
abbrev F11B010L12 : RowFamilyTree := TreeBlock010L12
abbrev F11B010L13 : RowFamilyTree := TreeBlock010L13
abbrev F11B010L14 : RowFamilyTree := TreeBlock010L14
abbrev F11B010L15 : RowFamilyTree := TreeBlock010L15
abbrev F11B010L16 : RowFamilyTree := TreeBlock010L16
abbrev F11B010L17 : RowFamilyTree := TreeBlock010L17
abbrev F11B010L18 : RowFamilyTree := TreeBlock010L18
abbrev F11B010L19 : RowFamilyTree := TreeBlock010L19
abbrev F11B010L20 : RowFamilyTree := TreeBlock010L20
abbrev F11B010L21 : RowFamilyTree := TreeBlock010L21
abbrev F11B010L22 : RowFamilyTree := TreeBlock010L22
abbrev F11B010L23 : RowFamilyTree := TreeBlock010L23
abbrev F11B010L24 : RowFamilyTree := TreeBlock010L24
abbrev F11B010L25 : RowFamilyTree := TreeBlock010L25
abbrev F11B010L26 : RowFamilyTree := TreeBlock010L26
abbrev F11B010L27 : RowFamilyTree := TreeBlock010L27
abbrev F11B010L28 : RowFamilyTree := TreeBlock010L28
abbrev F11B010L29 : RowFamilyTree := TreeBlock010L29
abbrev F11B010L30 : RowFamilyTree := TreeBlock010L30
abbrev F11B010L31 : RowFamilyTree := TreeBlock010L31
abbrev F11B010L32 : RowFamilyTree := TreeBlock010L32
abbrev F11B010L33 : RowFamilyTree := TreeBlock010L33
abbrev F11B010L34 : RowFamilyTree := TreeBlock010L34
abbrev F11B010L35 : RowFamilyTree := TreeBlock010L35
abbrev F11B010L36 : RowFamilyTree := TreeBlock010L36
abbrev F11B010L37 : RowFamilyTree := TreeBlock010L37
abbrev F11B010L38 : RowFamilyTree := TreeBlock010L38
abbrev F11B010L39 : RowFamilyTree := TreeBlock010L39
abbrev F11B010L40 : RowFamilyTree := TreeBlock010L40
abbrev F11B010L41 : RowFamilyTree := TreeBlock010L41
abbrev F11B010L42 : RowFamilyTree := TreeBlock010L42
abbrev F11B010L43 : RowFamilyTree := TreeBlock010L43
abbrev F11B010L44 : RowFamilyTree := TreeBlock010L44
abbrev F11B010L45 : RowFamilyTree := TreeBlock010L45
abbrev F11B010L46 : RowFamilyTree := TreeBlock010L46
abbrev F11B010L47 : RowFamilyTree := TreeBlock010L47
abbrev F11B010L48 : RowFamilyTree := TreeBlock010L48
abbrev F11B010L49 : RowFamilyTree := TreeBlock010L49
abbrev F11B010L50 : RowFamilyTree := TreeBlock010L50
abbrev F11B010L51 : RowFamilyTree := TreeBlock010L51
abbrev F11B010L52 : RowFamilyTree := TreeBlock010L52
abbrev F11B010L53 : RowFamilyTree := TreeBlock010L53
abbrev F11B010L54 : RowFamilyTree := TreeBlock010L54
abbrev F11B010L55 : RowFamilyTree := TreeBlock010L55
abbrev F11B010L56 : RowFamilyTree := TreeBlock010L56
abbrev F11B010L57 : RowFamilyTree := TreeBlock010L57
abbrev F11B010L58 : RowFamilyTree := TreeBlock010L58
abbrev F11B010L59 : RowFamilyTree := TreeBlock010L59
abbrev F11B010L60 : RowFamilyTree := TreeBlock010L60
abbrev F11B010L61 : RowFamilyTree := TreeBlock010L61
abbrev F11B010L62 : RowFamilyTree := TreeBlock010L62
abbrev F11B010L63 : RowFamilyTree := TreeBlock010L63
abbrev F11B010 : RowFamilyTree := TreeBlock010
theorem F11B010L0_lift (row : List GridPoint) (h : FamilyMember row F11B010L0) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B010L1_lift (row : List GridPoint) (h : FamilyMember row F11B010L1) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B010L2_lift (row : List GridPoint) (h : FamilyMember row F11B010L2) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B010L3_lift (row : List GridPoint) (h : FamilyMember row F11B010L3) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B010L4_lift (row : List GridPoint) (h : FamilyMember row F11B010L4) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B010L5_lift (row : List GridPoint) (h : FamilyMember row F11B010L5) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B010L6_lift (row : List GridPoint) (h : FamilyMember row F11B010L6) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B010L7_lift (row : List GridPoint) (h : FamilyMember row F11B010L7) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B010L8_lift (row : List GridPoint) (h : FamilyMember row F11B010L8) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B010L9_lift (row : List GridPoint) (h : FamilyMember row F11B010L9) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B010L10_lift (row : List GridPoint) (h : FamilyMember row F11B010L10) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B010L11_lift (row : List GridPoint) (h : FamilyMember row F11B010L11) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B010L12_lift (row : List GridPoint) (h : FamilyMember row F11B010L12) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B010L13_lift (row : List GridPoint) (h : FamilyMember row F11B010L13) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B010L14_lift (row : List GridPoint) (h : FamilyMember row F11B010L14) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B010L15_lift (row : List GridPoint) (h : FamilyMember row F11B010L15) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B010L16_lift (row : List GridPoint) (h : FamilyMember row F11B010L16) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B010L17_lift (row : List GridPoint) (h : FamilyMember row F11B010L17) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B010L18_lift (row : List GridPoint) (h : FamilyMember row F11B010L18) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B010L19_lift (row : List GridPoint) (h : FamilyMember row F11B010L19) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B010L20_lift (row : List GridPoint) (h : FamilyMember row F11B010L20) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B010L21_lift (row : List GridPoint) (h : FamilyMember row F11B010L21) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B010L22_lift (row : List GridPoint) (h : FamilyMember row F11B010L22) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B010L23_lift (row : List GridPoint) (h : FamilyMember row F11B010L23) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B010L24_lift (row : List GridPoint) (h : FamilyMember row F11B010L24) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B010L25_lift (row : List GridPoint) (h : FamilyMember row F11B010L25) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B010L26_lift (row : List GridPoint) (h : FamilyMember row F11B010L26) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B010L27_lift (row : List GridPoint) (h : FamilyMember row F11B010L27) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B010L28_lift (row : List GridPoint) (h : FamilyMember row F11B010L28) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B010L29_lift (row : List GridPoint) (h : FamilyMember row F11B010L29) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B010L30_lift (row : List GridPoint) (h : FamilyMember row F11B010L30) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B010L31_lift (row : List GridPoint) (h : FamilyMember row F11B010L31) : FamilyMember row F11B010 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B010L32_lift (row : List GridPoint) (h : FamilyMember row F11B010L32) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B010L33_lift (row : List GridPoint) (h : FamilyMember row F11B010L33) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B010L34_lift (row : List GridPoint) (h : FamilyMember row F11B010L34) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B010L35_lift (row : List GridPoint) (h : FamilyMember row F11B010L35) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B010L36_lift (row : List GridPoint) (h : FamilyMember row F11B010L36) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B010L37_lift (row : List GridPoint) (h : FamilyMember row F11B010L37) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B010L38_lift (row : List GridPoint) (h : FamilyMember row F11B010L38) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B010L39_lift (row : List GridPoint) (h : FamilyMember row F11B010L39) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B010L40_lift (row : List GridPoint) (h : FamilyMember row F11B010L40) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B010L41_lift (row : List GridPoint) (h : FamilyMember row F11B010L41) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B010L42_lift (row : List GridPoint) (h : FamilyMember row F11B010L42) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B010L43_lift (row : List GridPoint) (h : FamilyMember row F11B010L43) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B010L44_lift (row : List GridPoint) (h : FamilyMember row F11B010L44) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B010L45_lift (row : List GridPoint) (h : FamilyMember row F11B010L45) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B010L46_lift (row : List GridPoint) (h : FamilyMember row F11B010L46) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B010L47_lift (row : List GridPoint) (h : FamilyMember row F11B010L47) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B010L48_lift (row : List GridPoint) (h : FamilyMember row F11B010L48) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B010L49_lift (row : List GridPoint) (h : FamilyMember row F11B010L49) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B010L50_lift (row : List GridPoint) (h : FamilyMember row F11B010L50) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B010L51_lift (row : List GridPoint) (h : FamilyMember row F11B010L51) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B010L52_lift (row : List GridPoint) (h : FamilyMember row F11B010L52) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B010L53_lift (row : List GridPoint) (h : FamilyMember row F11B010L53) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B010L54_lift (row : List GridPoint) (h : FamilyMember row F11B010L54) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B010L55_lift (row : List GridPoint) (h : FamilyMember row F11B010L55) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B010L56_lift (row : List GridPoint) (h : FamilyMember row F11B010L56) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B010L57_lift (row : List GridPoint) (h : FamilyMember row F11B010L57) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B010L58_lift (row : List GridPoint) (h : FamilyMember row F11B010L58) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B010L59_lift (row : List GridPoint) (h : FamilyMember row F11B010L59) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B010L60_lift (row : List GridPoint) (h : FamilyMember row F11B010L60) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B010L61_lift (row : List GridPoint) (h : FamilyMember row F11B010L61) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B010L62_lift (row : List GridPoint) (h : FamilyMember row F11B010L62) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B010L63_lift (row : List GridPoint) (h : FamilyMember row F11B010L63) : FamilyMember row F11B010 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
