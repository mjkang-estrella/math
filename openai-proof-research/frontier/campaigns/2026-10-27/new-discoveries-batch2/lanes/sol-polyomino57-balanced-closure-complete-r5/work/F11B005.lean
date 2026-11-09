import TreeBlock005
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B005L0 : RowFamilyTree := TreeBlock005L0
abbrev F11B005L1 : RowFamilyTree := TreeBlock005L1
abbrev F11B005L2 : RowFamilyTree := TreeBlock005L2
abbrev F11B005L3 : RowFamilyTree := TreeBlock005L3
abbrev F11B005L4 : RowFamilyTree := TreeBlock005L4
abbrev F11B005L5 : RowFamilyTree := TreeBlock005L5
abbrev F11B005L6 : RowFamilyTree := TreeBlock005L6
abbrev F11B005L7 : RowFamilyTree := TreeBlock005L7
abbrev F11B005L8 : RowFamilyTree := TreeBlock005L8
abbrev F11B005L9 : RowFamilyTree := TreeBlock005L9
abbrev F11B005L10 : RowFamilyTree := TreeBlock005L10
abbrev F11B005L11 : RowFamilyTree := TreeBlock005L11
abbrev F11B005L12 : RowFamilyTree := TreeBlock005L12
abbrev F11B005L13 : RowFamilyTree := TreeBlock005L13
abbrev F11B005L14 : RowFamilyTree := TreeBlock005L14
abbrev F11B005L15 : RowFamilyTree := TreeBlock005L15
abbrev F11B005L16 : RowFamilyTree := TreeBlock005L16
abbrev F11B005L17 : RowFamilyTree := TreeBlock005L17
abbrev F11B005L18 : RowFamilyTree := TreeBlock005L18
abbrev F11B005L19 : RowFamilyTree := TreeBlock005L19
abbrev F11B005L20 : RowFamilyTree := TreeBlock005L20
abbrev F11B005L21 : RowFamilyTree := TreeBlock005L21
abbrev F11B005L22 : RowFamilyTree := TreeBlock005L22
abbrev F11B005L23 : RowFamilyTree := TreeBlock005L23
abbrev F11B005L24 : RowFamilyTree := TreeBlock005L24
abbrev F11B005L25 : RowFamilyTree := TreeBlock005L25
abbrev F11B005L26 : RowFamilyTree := TreeBlock005L26
abbrev F11B005L27 : RowFamilyTree := TreeBlock005L27
abbrev F11B005L28 : RowFamilyTree := TreeBlock005L28
abbrev F11B005L29 : RowFamilyTree := TreeBlock005L29
abbrev F11B005L30 : RowFamilyTree := TreeBlock005L30
abbrev F11B005L31 : RowFamilyTree := TreeBlock005L31
abbrev F11B005L32 : RowFamilyTree := TreeBlock005L32
abbrev F11B005L33 : RowFamilyTree := TreeBlock005L33
abbrev F11B005L34 : RowFamilyTree := TreeBlock005L34
abbrev F11B005L35 : RowFamilyTree := TreeBlock005L35
abbrev F11B005L36 : RowFamilyTree := TreeBlock005L36
abbrev F11B005L37 : RowFamilyTree := TreeBlock005L37
abbrev F11B005L38 : RowFamilyTree := TreeBlock005L38
abbrev F11B005L39 : RowFamilyTree := TreeBlock005L39
abbrev F11B005L40 : RowFamilyTree := TreeBlock005L40
abbrev F11B005L41 : RowFamilyTree := TreeBlock005L41
abbrev F11B005L42 : RowFamilyTree := TreeBlock005L42
abbrev F11B005L43 : RowFamilyTree := TreeBlock005L43
abbrev F11B005L44 : RowFamilyTree := TreeBlock005L44
abbrev F11B005L45 : RowFamilyTree := TreeBlock005L45
abbrev F11B005L46 : RowFamilyTree := TreeBlock005L46
abbrev F11B005L47 : RowFamilyTree := TreeBlock005L47
abbrev F11B005L48 : RowFamilyTree := TreeBlock005L48
abbrev F11B005L49 : RowFamilyTree := TreeBlock005L49
abbrev F11B005L50 : RowFamilyTree := TreeBlock005L50
abbrev F11B005L51 : RowFamilyTree := TreeBlock005L51
abbrev F11B005L52 : RowFamilyTree := TreeBlock005L52
abbrev F11B005L53 : RowFamilyTree := TreeBlock005L53
abbrev F11B005L54 : RowFamilyTree := TreeBlock005L54
abbrev F11B005L55 : RowFamilyTree := TreeBlock005L55
abbrev F11B005L56 : RowFamilyTree := TreeBlock005L56
abbrev F11B005L57 : RowFamilyTree := TreeBlock005L57
abbrev F11B005L58 : RowFamilyTree := TreeBlock005L58
abbrev F11B005L59 : RowFamilyTree := TreeBlock005L59
abbrev F11B005L60 : RowFamilyTree := TreeBlock005L60
abbrev F11B005L61 : RowFamilyTree := TreeBlock005L61
abbrev F11B005L62 : RowFamilyTree := TreeBlock005L62
abbrev F11B005L63 : RowFamilyTree := TreeBlock005L63
abbrev F11B005 : RowFamilyTree := TreeBlock005
theorem F11B005L0_lift (row : List GridPoint) (h : FamilyMember row F11B005L0) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B005L1_lift (row : List GridPoint) (h : FamilyMember row F11B005L1) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B005L2_lift (row : List GridPoint) (h : FamilyMember row F11B005L2) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B005L3_lift (row : List GridPoint) (h : FamilyMember row F11B005L3) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B005L4_lift (row : List GridPoint) (h : FamilyMember row F11B005L4) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B005L5_lift (row : List GridPoint) (h : FamilyMember row F11B005L5) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B005L6_lift (row : List GridPoint) (h : FamilyMember row F11B005L6) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B005L7_lift (row : List GridPoint) (h : FamilyMember row F11B005L7) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B005L8_lift (row : List GridPoint) (h : FamilyMember row F11B005L8) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B005L9_lift (row : List GridPoint) (h : FamilyMember row F11B005L9) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B005L10_lift (row : List GridPoint) (h : FamilyMember row F11B005L10) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B005L11_lift (row : List GridPoint) (h : FamilyMember row F11B005L11) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B005L12_lift (row : List GridPoint) (h : FamilyMember row F11B005L12) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B005L13_lift (row : List GridPoint) (h : FamilyMember row F11B005L13) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B005L14_lift (row : List GridPoint) (h : FamilyMember row F11B005L14) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B005L15_lift (row : List GridPoint) (h : FamilyMember row F11B005L15) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B005L16_lift (row : List GridPoint) (h : FamilyMember row F11B005L16) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B005L17_lift (row : List GridPoint) (h : FamilyMember row F11B005L17) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B005L18_lift (row : List GridPoint) (h : FamilyMember row F11B005L18) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B005L19_lift (row : List GridPoint) (h : FamilyMember row F11B005L19) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B005L20_lift (row : List GridPoint) (h : FamilyMember row F11B005L20) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B005L21_lift (row : List GridPoint) (h : FamilyMember row F11B005L21) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B005L22_lift (row : List GridPoint) (h : FamilyMember row F11B005L22) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B005L23_lift (row : List GridPoint) (h : FamilyMember row F11B005L23) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B005L24_lift (row : List GridPoint) (h : FamilyMember row F11B005L24) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B005L25_lift (row : List GridPoint) (h : FamilyMember row F11B005L25) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B005L26_lift (row : List GridPoint) (h : FamilyMember row F11B005L26) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B005L27_lift (row : List GridPoint) (h : FamilyMember row F11B005L27) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B005L28_lift (row : List GridPoint) (h : FamilyMember row F11B005L28) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B005L29_lift (row : List GridPoint) (h : FamilyMember row F11B005L29) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B005L30_lift (row : List GridPoint) (h : FamilyMember row F11B005L30) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B005L31_lift (row : List GridPoint) (h : FamilyMember row F11B005L31) : FamilyMember row F11B005 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B005L32_lift (row : List GridPoint) (h : FamilyMember row F11B005L32) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B005L33_lift (row : List GridPoint) (h : FamilyMember row F11B005L33) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B005L34_lift (row : List GridPoint) (h : FamilyMember row F11B005L34) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B005L35_lift (row : List GridPoint) (h : FamilyMember row F11B005L35) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B005L36_lift (row : List GridPoint) (h : FamilyMember row F11B005L36) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B005L37_lift (row : List GridPoint) (h : FamilyMember row F11B005L37) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B005L38_lift (row : List GridPoint) (h : FamilyMember row F11B005L38) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B005L39_lift (row : List GridPoint) (h : FamilyMember row F11B005L39) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B005L40_lift (row : List GridPoint) (h : FamilyMember row F11B005L40) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B005L41_lift (row : List GridPoint) (h : FamilyMember row F11B005L41) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B005L42_lift (row : List GridPoint) (h : FamilyMember row F11B005L42) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B005L43_lift (row : List GridPoint) (h : FamilyMember row F11B005L43) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B005L44_lift (row : List GridPoint) (h : FamilyMember row F11B005L44) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B005L45_lift (row : List GridPoint) (h : FamilyMember row F11B005L45) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B005L46_lift (row : List GridPoint) (h : FamilyMember row F11B005L46) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B005L47_lift (row : List GridPoint) (h : FamilyMember row F11B005L47) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B005L48_lift (row : List GridPoint) (h : FamilyMember row F11B005L48) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B005L49_lift (row : List GridPoint) (h : FamilyMember row F11B005L49) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B005L50_lift (row : List GridPoint) (h : FamilyMember row F11B005L50) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B005L51_lift (row : List GridPoint) (h : FamilyMember row F11B005L51) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B005L52_lift (row : List GridPoint) (h : FamilyMember row F11B005L52) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B005L53_lift (row : List GridPoint) (h : FamilyMember row F11B005L53) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B005L54_lift (row : List GridPoint) (h : FamilyMember row F11B005L54) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B005L55_lift (row : List GridPoint) (h : FamilyMember row F11B005L55) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B005L56_lift (row : List GridPoint) (h : FamilyMember row F11B005L56) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B005L57_lift (row : List GridPoint) (h : FamilyMember row F11B005L57) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B005L58_lift (row : List GridPoint) (h : FamilyMember row F11B005L58) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B005L59_lift (row : List GridPoint) (h : FamilyMember row F11B005L59) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B005L60_lift (row : List GridPoint) (h : FamilyMember row F11B005L60) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B005L61_lift (row : List GridPoint) (h : FamilyMember row F11B005L61) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B005L62_lift (row : List GridPoint) (h : FamilyMember row F11B005L62) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B005L63_lift (row : List GridPoint) (h : FamilyMember row F11B005L63) : FamilyMember row F11B005 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
