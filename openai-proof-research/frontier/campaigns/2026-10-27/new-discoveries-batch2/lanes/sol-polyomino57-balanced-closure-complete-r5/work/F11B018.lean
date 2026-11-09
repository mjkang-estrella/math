import TreeBlock018
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B018L0 : RowFamilyTree := TreeBlock018L0
abbrev F11B018L1 : RowFamilyTree := TreeBlock018L1
abbrev F11B018L2 : RowFamilyTree := TreeBlock018L2
abbrev F11B018L3 : RowFamilyTree := TreeBlock018L3
abbrev F11B018L4 : RowFamilyTree := TreeBlock018L4
abbrev F11B018L5 : RowFamilyTree := TreeBlock018L5
abbrev F11B018L6 : RowFamilyTree := TreeBlock018L6
abbrev F11B018L7 : RowFamilyTree := TreeBlock018L7
abbrev F11B018L8 : RowFamilyTree := TreeBlock018L8
abbrev F11B018L9 : RowFamilyTree := TreeBlock018L9
abbrev F11B018L10 : RowFamilyTree := TreeBlock018L10
abbrev F11B018L11 : RowFamilyTree := TreeBlock018L11
abbrev F11B018L12 : RowFamilyTree := TreeBlock018L12
abbrev F11B018L13 : RowFamilyTree := TreeBlock018L13
abbrev F11B018L14 : RowFamilyTree := TreeBlock018L14
abbrev F11B018L15 : RowFamilyTree := TreeBlock018L15
abbrev F11B018L16 : RowFamilyTree := TreeBlock018L16
abbrev F11B018L17 : RowFamilyTree := TreeBlock018L17
abbrev F11B018L18 : RowFamilyTree := TreeBlock018L18
abbrev F11B018L19 : RowFamilyTree := TreeBlock018L19
abbrev F11B018L20 : RowFamilyTree := TreeBlock018L20
abbrev F11B018L21 : RowFamilyTree := TreeBlock018L21
abbrev F11B018L22 : RowFamilyTree := TreeBlock018L22
abbrev F11B018L23 : RowFamilyTree := TreeBlock018L23
abbrev F11B018L24 : RowFamilyTree := TreeBlock018L24
abbrev F11B018L25 : RowFamilyTree := TreeBlock018L25
abbrev F11B018L26 : RowFamilyTree := TreeBlock018L26
abbrev F11B018L27 : RowFamilyTree := TreeBlock018L27
abbrev F11B018L28 : RowFamilyTree := TreeBlock018L28
abbrev F11B018L29 : RowFamilyTree := TreeBlock018L29
abbrev F11B018L30 : RowFamilyTree := TreeBlock018L30
abbrev F11B018L31 : RowFamilyTree := TreeBlock018L31
abbrev F11B018L32 : RowFamilyTree := TreeBlock018L32
abbrev F11B018L33 : RowFamilyTree := TreeBlock018L33
abbrev F11B018L34 : RowFamilyTree := TreeBlock018L34
abbrev F11B018L35 : RowFamilyTree := TreeBlock018L35
abbrev F11B018L36 : RowFamilyTree := TreeBlock018L36
abbrev F11B018L37 : RowFamilyTree := TreeBlock018L37
abbrev F11B018L38 : RowFamilyTree := TreeBlock018L38
abbrev F11B018L39 : RowFamilyTree := TreeBlock018L39
abbrev F11B018L40 : RowFamilyTree := TreeBlock018L40
abbrev F11B018L41 : RowFamilyTree := TreeBlock018L41
abbrev F11B018L42 : RowFamilyTree := TreeBlock018L42
abbrev F11B018L43 : RowFamilyTree := TreeBlock018L43
abbrev F11B018L44 : RowFamilyTree := TreeBlock018L44
abbrev F11B018L45 : RowFamilyTree := TreeBlock018L45
abbrev F11B018L46 : RowFamilyTree := TreeBlock018L46
abbrev F11B018L47 : RowFamilyTree := TreeBlock018L47
abbrev F11B018L48 : RowFamilyTree := TreeBlock018L48
abbrev F11B018L49 : RowFamilyTree := TreeBlock018L49
abbrev F11B018L50 : RowFamilyTree := TreeBlock018L50
abbrev F11B018L51 : RowFamilyTree := TreeBlock018L51
abbrev F11B018L52 : RowFamilyTree := TreeBlock018L52
abbrev F11B018L53 : RowFamilyTree := TreeBlock018L53
abbrev F11B018L54 : RowFamilyTree := TreeBlock018L54
abbrev F11B018L55 : RowFamilyTree := TreeBlock018L55
abbrev F11B018L56 : RowFamilyTree := TreeBlock018L56
abbrev F11B018L57 : RowFamilyTree := TreeBlock018L57
abbrev F11B018L58 : RowFamilyTree := TreeBlock018L58
abbrev F11B018L59 : RowFamilyTree := TreeBlock018L59
abbrev F11B018L60 : RowFamilyTree := TreeBlock018L60
abbrev F11B018L61 : RowFamilyTree := TreeBlock018L61
abbrev F11B018L62 : RowFamilyTree := TreeBlock018L62
abbrev F11B018L63 : RowFamilyTree := TreeBlock018L63
abbrev F11B018 : RowFamilyTree := TreeBlock018
theorem F11B018L0_lift (row : List GridPoint) (h : FamilyMember row F11B018L0) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B018L1_lift (row : List GridPoint) (h : FamilyMember row F11B018L1) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B018L2_lift (row : List GridPoint) (h : FamilyMember row F11B018L2) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B018L3_lift (row : List GridPoint) (h : FamilyMember row F11B018L3) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B018L4_lift (row : List GridPoint) (h : FamilyMember row F11B018L4) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B018L5_lift (row : List GridPoint) (h : FamilyMember row F11B018L5) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B018L6_lift (row : List GridPoint) (h : FamilyMember row F11B018L6) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B018L7_lift (row : List GridPoint) (h : FamilyMember row F11B018L7) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B018L8_lift (row : List GridPoint) (h : FamilyMember row F11B018L8) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B018L9_lift (row : List GridPoint) (h : FamilyMember row F11B018L9) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B018L10_lift (row : List GridPoint) (h : FamilyMember row F11B018L10) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B018L11_lift (row : List GridPoint) (h : FamilyMember row F11B018L11) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B018L12_lift (row : List GridPoint) (h : FamilyMember row F11B018L12) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B018L13_lift (row : List GridPoint) (h : FamilyMember row F11B018L13) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B018L14_lift (row : List GridPoint) (h : FamilyMember row F11B018L14) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B018L15_lift (row : List GridPoint) (h : FamilyMember row F11B018L15) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B018L16_lift (row : List GridPoint) (h : FamilyMember row F11B018L16) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B018L17_lift (row : List GridPoint) (h : FamilyMember row F11B018L17) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B018L18_lift (row : List GridPoint) (h : FamilyMember row F11B018L18) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B018L19_lift (row : List GridPoint) (h : FamilyMember row F11B018L19) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B018L20_lift (row : List GridPoint) (h : FamilyMember row F11B018L20) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B018L21_lift (row : List GridPoint) (h : FamilyMember row F11B018L21) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B018L22_lift (row : List GridPoint) (h : FamilyMember row F11B018L22) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B018L23_lift (row : List GridPoint) (h : FamilyMember row F11B018L23) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B018L24_lift (row : List GridPoint) (h : FamilyMember row F11B018L24) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B018L25_lift (row : List GridPoint) (h : FamilyMember row F11B018L25) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B018L26_lift (row : List GridPoint) (h : FamilyMember row F11B018L26) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B018L27_lift (row : List GridPoint) (h : FamilyMember row F11B018L27) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B018L28_lift (row : List GridPoint) (h : FamilyMember row F11B018L28) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B018L29_lift (row : List GridPoint) (h : FamilyMember row F11B018L29) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B018L30_lift (row : List GridPoint) (h : FamilyMember row F11B018L30) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B018L31_lift (row : List GridPoint) (h : FamilyMember row F11B018L31) : FamilyMember row F11B018 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B018L32_lift (row : List GridPoint) (h : FamilyMember row F11B018L32) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B018L33_lift (row : List GridPoint) (h : FamilyMember row F11B018L33) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B018L34_lift (row : List GridPoint) (h : FamilyMember row F11B018L34) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B018L35_lift (row : List GridPoint) (h : FamilyMember row F11B018L35) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B018L36_lift (row : List GridPoint) (h : FamilyMember row F11B018L36) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B018L37_lift (row : List GridPoint) (h : FamilyMember row F11B018L37) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B018L38_lift (row : List GridPoint) (h : FamilyMember row F11B018L38) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B018L39_lift (row : List GridPoint) (h : FamilyMember row F11B018L39) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B018L40_lift (row : List GridPoint) (h : FamilyMember row F11B018L40) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B018L41_lift (row : List GridPoint) (h : FamilyMember row F11B018L41) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B018L42_lift (row : List GridPoint) (h : FamilyMember row F11B018L42) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B018L43_lift (row : List GridPoint) (h : FamilyMember row F11B018L43) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B018L44_lift (row : List GridPoint) (h : FamilyMember row F11B018L44) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B018L45_lift (row : List GridPoint) (h : FamilyMember row F11B018L45) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B018L46_lift (row : List GridPoint) (h : FamilyMember row F11B018L46) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B018L47_lift (row : List GridPoint) (h : FamilyMember row F11B018L47) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B018L48_lift (row : List GridPoint) (h : FamilyMember row F11B018L48) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B018L49_lift (row : List GridPoint) (h : FamilyMember row F11B018L49) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B018L50_lift (row : List GridPoint) (h : FamilyMember row F11B018L50) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B018L51_lift (row : List GridPoint) (h : FamilyMember row F11B018L51) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B018L52_lift (row : List GridPoint) (h : FamilyMember row F11B018L52) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B018L53_lift (row : List GridPoint) (h : FamilyMember row F11B018L53) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B018L54_lift (row : List GridPoint) (h : FamilyMember row F11B018L54) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B018L55_lift (row : List GridPoint) (h : FamilyMember row F11B018L55) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B018L56_lift (row : List GridPoint) (h : FamilyMember row F11B018L56) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B018L57_lift (row : List GridPoint) (h : FamilyMember row F11B018L57) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B018L58_lift (row : List GridPoint) (h : FamilyMember row F11B018L58) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B018L59_lift (row : List GridPoint) (h : FamilyMember row F11B018L59) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B018L60_lift (row : List GridPoint) (h : FamilyMember row F11B018L60) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B018L61_lift (row : List GridPoint) (h : FamilyMember row F11B018L61) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B018L62_lift (row : List GridPoint) (h : FamilyMember row F11B018L62) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B018L63_lift (row : List GridPoint) (h : FamilyMember row F11B018L63) : FamilyMember row F11B018 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
