import TreeBlock042
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B042L0 : RowFamilyTree := TreeBlock042L0
abbrev F11B042L1 : RowFamilyTree := TreeBlock042L1
abbrev F11B042L2 : RowFamilyTree := TreeBlock042L2
abbrev F11B042L3 : RowFamilyTree := TreeBlock042L3
abbrev F11B042L4 : RowFamilyTree := TreeBlock042L4
abbrev F11B042L5 : RowFamilyTree := TreeBlock042L5
abbrev F11B042L6 : RowFamilyTree := TreeBlock042L6
abbrev F11B042L7 : RowFamilyTree := TreeBlock042L7
abbrev F11B042L8 : RowFamilyTree := TreeBlock042L8
abbrev F11B042L9 : RowFamilyTree := TreeBlock042L9
abbrev F11B042L10 : RowFamilyTree := TreeBlock042L10
abbrev F11B042L11 : RowFamilyTree := TreeBlock042L11
abbrev F11B042L12 : RowFamilyTree := TreeBlock042L12
abbrev F11B042L13 : RowFamilyTree := TreeBlock042L13
abbrev F11B042L14 : RowFamilyTree := TreeBlock042L14
abbrev F11B042L15 : RowFamilyTree := TreeBlock042L15
abbrev F11B042L16 : RowFamilyTree := TreeBlock042L16
abbrev F11B042L17 : RowFamilyTree := TreeBlock042L17
abbrev F11B042L18 : RowFamilyTree := TreeBlock042L18
abbrev F11B042L19 : RowFamilyTree := TreeBlock042L19
abbrev F11B042L20 : RowFamilyTree := TreeBlock042L20
abbrev F11B042L21 : RowFamilyTree := TreeBlock042L21
abbrev F11B042L22 : RowFamilyTree := TreeBlock042L22
abbrev F11B042L23 : RowFamilyTree := TreeBlock042L23
abbrev F11B042L24 : RowFamilyTree := TreeBlock042L24
abbrev F11B042L25 : RowFamilyTree := TreeBlock042L25
abbrev F11B042L26 : RowFamilyTree := TreeBlock042L26
abbrev F11B042L27 : RowFamilyTree := TreeBlock042L27
abbrev F11B042L28 : RowFamilyTree := TreeBlock042L28
abbrev F11B042L29 : RowFamilyTree := TreeBlock042L29
abbrev F11B042L30 : RowFamilyTree := TreeBlock042L30
abbrev F11B042L31 : RowFamilyTree := TreeBlock042L31
abbrev F11B042L32 : RowFamilyTree := TreeBlock042L32
abbrev F11B042L33 : RowFamilyTree := TreeBlock042L33
abbrev F11B042L34 : RowFamilyTree := TreeBlock042L34
abbrev F11B042L35 : RowFamilyTree := TreeBlock042L35
abbrev F11B042L36 : RowFamilyTree := TreeBlock042L36
abbrev F11B042L37 : RowFamilyTree := TreeBlock042L37
abbrev F11B042L38 : RowFamilyTree := TreeBlock042L38
abbrev F11B042L39 : RowFamilyTree := TreeBlock042L39
abbrev F11B042L40 : RowFamilyTree := TreeBlock042L40
abbrev F11B042L41 : RowFamilyTree := TreeBlock042L41
abbrev F11B042L42 : RowFamilyTree := TreeBlock042L42
abbrev F11B042L43 : RowFamilyTree := TreeBlock042L43
abbrev F11B042L44 : RowFamilyTree := TreeBlock042L44
abbrev F11B042L45 : RowFamilyTree := TreeBlock042L45
abbrev F11B042L46 : RowFamilyTree := TreeBlock042L46
abbrev F11B042L47 : RowFamilyTree := TreeBlock042L47
abbrev F11B042L48 : RowFamilyTree := TreeBlock042L48
abbrev F11B042L49 : RowFamilyTree := TreeBlock042L49
abbrev F11B042L50 : RowFamilyTree := TreeBlock042L50
abbrev F11B042L51 : RowFamilyTree := TreeBlock042L51
abbrev F11B042L52 : RowFamilyTree := TreeBlock042L52
abbrev F11B042L53 : RowFamilyTree := TreeBlock042L53
abbrev F11B042L54 : RowFamilyTree := TreeBlock042L54
abbrev F11B042L55 : RowFamilyTree := TreeBlock042L55
abbrev F11B042L56 : RowFamilyTree := TreeBlock042L56
abbrev F11B042L57 : RowFamilyTree := TreeBlock042L57
abbrev F11B042L58 : RowFamilyTree := TreeBlock042L58
abbrev F11B042L59 : RowFamilyTree := TreeBlock042L59
abbrev F11B042L60 : RowFamilyTree := TreeBlock042L60
abbrev F11B042L61 : RowFamilyTree := TreeBlock042L61
abbrev F11B042L62 : RowFamilyTree := TreeBlock042L62
abbrev F11B042L63 : RowFamilyTree := TreeBlock042L63
abbrev F11B042 : RowFamilyTree := TreeBlock042
theorem F11B042L0_lift (row : List GridPoint) (h : FamilyMember row F11B042L0) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B042L1_lift (row : List GridPoint) (h : FamilyMember row F11B042L1) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B042L2_lift (row : List GridPoint) (h : FamilyMember row F11B042L2) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B042L3_lift (row : List GridPoint) (h : FamilyMember row F11B042L3) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B042L4_lift (row : List GridPoint) (h : FamilyMember row F11B042L4) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B042L5_lift (row : List GridPoint) (h : FamilyMember row F11B042L5) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B042L6_lift (row : List GridPoint) (h : FamilyMember row F11B042L6) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B042L7_lift (row : List GridPoint) (h : FamilyMember row F11B042L7) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B042L8_lift (row : List GridPoint) (h : FamilyMember row F11B042L8) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B042L9_lift (row : List GridPoint) (h : FamilyMember row F11B042L9) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B042L10_lift (row : List GridPoint) (h : FamilyMember row F11B042L10) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B042L11_lift (row : List GridPoint) (h : FamilyMember row F11B042L11) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B042L12_lift (row : List GridPoint) (h : FamilyMember row F11B042L12) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B042L13_lift (row : List GridPoint) (h : FamilyMember row F11B042L13) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B042L14_lift (row : List GridPoint) (h : FamilyMember row F11B042L14) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B042L15_lift (row : List GridPoint) (h : FamilyMember row F11B042L15) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B042L16_lift (row : List GridPoint) (h : FamilyMember row F11B042L16) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B042L17_lift (row : List GridPoint) (h : FamilyMember row F11B042L17) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B042L18_lift (row : List GridPoint) (h : FamilyMember row F11B042L18) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B042L19_lift (row : List GridPoint) (h : FamilyMember row F11B042L19) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B042L20_lift (row : List GridPoint) (h : FamilyMember row F11B042L20) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B042L21_lift (row : List GridPoint) (h : FamilyMember row F11B042L21) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B042L22_lift (row : List GridPoint) (h : FamilyMember row F11B042L22) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B042L23_lift (row : List GridPoint) (h : FamilyMember row F11B042L23) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B042L24_lift (row : List GridPoint) (h : FamilyMember row F11B042L24) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B042L25_lift (row : List GridPoint) (h : FamilyMember row F11B042L25) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B042L26_lift (row : List GridPoint) (h : FamilyMember row F11B042L26) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B042L27_lift (row : List GridPoint) (h : FamilyMember row F11B042L27) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B042L28_lift (row : List GridPoint) (h : FamilyMember row F11B042L28) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B042L29_lift (row : List GridPoint) (h : FamilyMember row F11B042L29) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B042L30_lift (row : List GridPoint) (h : FamilyMember row F11B042L30) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B042L31_lift (row : List GridPoint) (h : FamilyMember row F11B042L31) : FamilyMember row F11B042 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B042L32_lift (row : List GridPoint) (h : FamilyMember row F11B042L32) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B042L33_lift (row : List GridPoint) (h : FamilyMember row F11B042L33) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B042L34_lift (row : List GridPoint) (h : FamilyMember row F11B042L34) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B042L35_lift (row : List GridPoint) (h : FamilyMember row F11B042L35) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B042L36_lift (row : List GridPoint) (h : FamilyMember row F11B042L36) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B042L37_lift (row : List GridPoint) (h : FamilyMember row F11B042L37) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B042L38_lift (row : List GridPoint) (h : FamilyMember row F11B042L38) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B042L39_lift (row : List GridPoint) (h : FamilyMember row F11B042L39) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B042L40_lift (row : List GridPoint) (h : FamilyMember row F11B042L40) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B042L41_lift (row : List GridPoint) (h : FamilyMember row F11B042L41) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B042L42_lift (row : List GridPoint) (h : FamilyMember row F11B042L42) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B042L43_lift (row : List GridPoint) (h : FamilyMember row F11B042L43) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B042L44_lift (row : List GridPoint) (h : FamilyMember row F11B042L44) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B042L45_lift (row : List GridPoint) (h : FamilyMember row F11B042L45) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B042L46_lift (row : List GridPoint) (h : FamilyMember row F11B042L46) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B042L47_lift (row : List GridPoint) (h : FamilyMember row F11B042L47) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B042L48_lift (row : List GridPoint) (h : FamilyMember row F11B042L48) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B042L49_lift (row : List GridPoint) (h : FamilyMember row F11B042L49) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B042L50_lift (row : List GridPoint) (h : FamilyMember row F11B042L50) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B042L51_lift (row : List GridPoint) (h : FamilyMember row F11B042L51) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B042L52_lift (row : List GridPoint) (h : FamilyMember row F11B042L52) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B042L53_lift (row : List GridPoint) (h : FamilyMember row F11B042L53) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B042L54_lift (row : List GridPoint) (h : FamilyMember row F11B042L54) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B042L55_lift (row : List GridPoint) (h : FamilyMember row F11B042L55) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B042L56_lift (row : List GridPoint) (h : FamilyMember row F11B042L56) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B042L57_lift (row : List GridPoint) (h : FamilyMember row F11B042L57) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B042L58_lift (row : List GridPoint) (h : FamilyMember row F11B042L58) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B042L59_lift (row : List GridPoint) (h : FamilyMember row F11B042L59) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B042L60_lift (row : List GridPoint) (h : FamilyMember row F11B042L60) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B042L61_lift (row : List GridPoint) (h : FamilyMember row F11B042L61) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B042L62_lift (row : List GridPoint) (h : FamilyMember row F11B042L62) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B042L63_lift (row : List GridPoint) (h : FamilyMember row F11B042L63) : FamilyMember row F11B042 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
