import TreeBlock032
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B032L0 : RowFamilyTree := TreeBlock032L0
abbrev F11B032L1 : RowFamilyTree := TreeBlock032L1
abbrev F11B032L2 : RowFamilyTree := TreeBlock032L2
abbrev F11B032L3 : RowFamilyTree := TreeBlock032L3
abbrev F11B032L4 : RowFamilyTree := TreeBlock032L4
abbrev F11B032L5 : RowFamilyTree := TreeBlock032L5
abbrev F11B032L6 : RowFamilyTree := TreeBlock032L6
abbrev F11B032L7 : RowFamilyTree := TreeBlock032L7
abbrev F11B032L8 : RowFamilyTree := TreeBlock032L8
abbrev F11B032L9 : RowFamilyTree := TreeBlock032L9
abbrev F11B032L10 : RowFamilyTree := TreeBlock032L10
abbrev F11B032L11 : RowFamilyTree := TreeBlock032L11
abbrev F11B032L12 : RowFamilyTree := TreeBlock032L12
abbrev F11B032L13 : RowFamilyTree := TreeBlock032L13
abbrev F11B032L14 : RowFamilyTree := TreeBlock032L14
abbrev F11B032L15 : RowFamilyTree := TreeBlock032L15
abbrev F11B032L16 : RowFamilyTree := TreeBlock032L16
abbrev F11B032L17 : RowFamilyTree := TreeBlock032L17
abbrev F11B032L18 : RowFamilyTree := TreeBlock032L18
abbrev F11B032L19 : RowFamilyTree := TreeBlock032L19
abbrev F11B032L20 : RowFamilyTree := TreeBlock032L20
abbrev F11B032L21 : RowFamilyTree := TreeBlock032L21
abbrev F11B032L22 : RowFamilyTree := TreeBlock032L22
abbrev F11B032L23 : RowFamilyTree := TreeBlock032L23
abbrev F11B032L24 : RowFamilyTree := TreeBlock032L24
abbrev F11B032L25 : RowFamilyTree := TreeBlock032L25
abbrev F11B032L26 : RowFamilyTree := TreeBlock032L26
abbrev F11B032L27 : RowFamilyTree := TreeBlock032L27
abbrev F11B032L28 : RowFamilyTree := TreeBlock032L28
abbrev F11B032L29 : RowFamilyTree := TreeBlock032L29
abbrev F11B032L30 : RowFamilyTree := TreeBlock032L30
abbrev F11B032L31 : RowFamilyTree := TreeBlock032L31
abbrev F11B032L32 : RowFamilyTree := TreeBlock032L32
abbrev F11B032L33 : RowFamilyTree := TreeBlock032L33
abbrev F11B032L34 : RowFamilyTree := TreeBlock032L34
abbrev F11B032L35 : RowFamilyTree := TreeBlock032L35
abbrev F11B032L36 : RowFamilyTree := TreeBlock032L36
abbrev F11B032L37 : RowFamilyTree := TreeBlock032L37
abbrev F11B032L38 : RowFamilyTree := TreeBlock032L38
abbrev F11B032L39 : RowFamilyTree := TreeBlock032L39
abbrev F11B032L40 : RowFamilyTree := TreeBlock032L40
abbrev F11B032L41 : RowFamilyTree := TreeBlock032L41
abbrev F11B032L42 : RowFamilyTree := TreeBlock032L42
abbrev F11B032L43 : RowFamilyTree := TreeBlock032L43
abbrev F11B032L44 : RowFamilyTree := TreeBlock032L44
abbrev F11B032L45 : RowFamilyTree := TreeBlock032L45
abbrev F11B032L46 : RowFamilyTree := TreeBlock032L46
abbrev F11B032L47 : RowFamilyTree := TreeBlock032L47
abbrev F11B032L48 : RowFamilyTree := TreeBlock032L48
abbrev F11B032L49 : RowFamilyTree := TreeBlock032L49
abbrev F11B032L50 : RowFamilyTree := TreeBlock032L50
abbrev F11B032L51 : RowFamilyTree := TreeBlock032L51
abbrev F11B032L52 : RowFamilyTree := TreeBlock032L52
abbrev F11B032L53 : RowFamilyTree := TreeBlock032L53
abbrev F11B032L54 : RowFamilyTree := TreeBlock032L54
abbrev F11B032L55 : RowFamilyTree := TreeBlock032L55
abbrev F11B032L56 : RowFamilyTree := TreeBlock032L56
abbrev F11B032L57 : RowFamilyTree := TreeBlock032L57
abbrev F11B032L58 : RowFamilyTree := TreeBlock032L58
abbrev F11B032L59 : RowFamilyTree := TreeBlock032L59
abbrev F11B032L60 : RowFamilyTree := TreeBlock032L60
abbrev F11B032L61 : RowFamilyTree := TreeBlock032L61
abbrev F11B032L62 : RowFamilyTree := TreeBlock032L62
abbrev F11B032L63 : RowFamilyTree := TreeBlock032L63
abbrev F11B032 : RowFamilyTree := TreeBlock032
theorem F11B032L0_lift (row : List GridPoint) (h : FamilyMember row F11B032L0) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B032L1_lift (row : List GridPoint) (h : FamilyMember row F11B032L1) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B032L2_lift (row : List GridPoint) (h : FamilyMember row F11B032L2) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B032L3_lift (row : List GridPoint) (h : FamilyMember row F11B032L3) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B032L4_lift (row : List GridPoint) (h : FamilyMember row F11B032L4) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B032L5_lift (row : List GridPoint) (h : FamilyMember row F11B032L5) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B032L6_lift (row : List GridPoint) (h : FamilyMember row F11B032L6) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B032L7_lift (row : List GridPoint) (h : FamilyMember row F11B032L7) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B032L8_lift (row : List GridPoint) (h : FamilyMember row F11B032L8) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B032L9_lift (row : List GridPoint) (h : FamilyMember row F11B032L9) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B032L10_lift (row : List GridPoint) (h : FamilyMember row F11B032L10) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B032L11_lift (row : List GridPoint) (h : FamilyMember row F11B032L11) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B032L12_lift (row : List GridPoint) (h : FamilyMember row F11B032L12) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B032L13_lift (row : List GridPoint) (h : FamilyMember row F11B032L13) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B032L14_lift (row : List GridPoint) (h : FamilyMember row F11B032L14) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B032L15_lift (row : List GridPoint) (h : FamilyMember row F11B032L15) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B032L16_lift (row : List GridPoint) (h : FamilyMember row F11B032L16) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B032L17_lift (row : List GridPoint) (h : FamilyMember row F11B032L17) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B032L18_lift (row : List GridPoint) (h : FamilyMember row F11B032L18) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B032L19_lift (row : List GridPoint) (h : FamilyMember row F11B032L19) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B032L20_lift (row : List GridPoint) (h : FamilyMember row F11B032L20) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B032L21_lift (row : List GridPoint) (h : FamilyMember row F11B032L21) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B032L22_lift (row : List GridPoint) (h : FamilyMember row F11B032L22) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B032L23_lift (row : List GridPoint) (h : FamilyMember row F11B032L23) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B032L24_lift (row : List GridPoint) (h : FamilyMember row F11B032L24) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B032L25_lift (row : List GridPoint) (h : FamilyMember row F11B032L25) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B032L26_lift (row : List GridPoint) (h : FamilyMember row F11B032L26) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B032L27_lift (row : List GridPoint) (h : FamilyMember row F11B032L27) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B032L28_lift (row : List GridPoint) (h : FamilyMember row F11B032L28) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B032L29_lift (row : List GridPoint) (h : FamilyMember row F11B032L29) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B032L30_lift (row : List GridPoint) (h : FamilyMember row F11B032L30) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B032L31_lift (row : List GridPoint) (h : FamilyMember row F11B032L31) : FamilyMember row F11B032 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B032L32_lift (row : List GridPoint) (h : FamilyMember row F11B032L32) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B032L33_lift (row : List GridPoint) (h : FamilyMember row F11B032L33) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B032L34_lift (row : List GridPoint) (h : FamilyMember row F11B032L34) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B032L35_lift (row : List GridPoint) (h : FamilyMember row F11B032L35) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B032L36_lift (row : List GridPoint) (h : FamilyMember row F11B032L36) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B032L37_lift (row : List GridPoint) (h : FamilyMember row F11B032L37) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B032L38_lift (row : List GridPoint) (h : FamilyMember row F11B032L38) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B032L39_lift (row : List GridPoint) (h : FamilyMember row F11B032L39) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B032L40_lift (row : List GridPoint) (h : FamilyMember row F11B032L40) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B032L41_lift (row : List GridPoint) (h : FamilyMember row F11B032L41) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B032L42_lift (row : List GridPoint) (h : FamilyMember row F11B032L42) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B032L43_lift (row : List GridPoint) (h : FamilyMember row F11B032L43) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B032L44_lift (row : List GridPoint) (h : FamilyMember row F11B032L44) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B032L45_lift (row : List GridPoint) (h : FamilyMember row F11B032L45) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B032L46_lift (row : List GridPoint) (h : FamilyMember row F11B032L46) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B032L47_lift (row : List GridPoint) (h : FamilyMember row F11B032L47) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B032L48_lift (row : List GridPoint) (h : FamilyMember row F11B032L48) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B032L49_lift (row : List GridPoint) (h : FamilyMember row F11B032L49) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B032L50_lift (row : List GridPoint) (h : FamilyMember row F11B032L50) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B032L51_lift (row : List GridPoint) (h : FamilyMember row F11B032L51) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B032L52_lift (row : List GridPoint) (h : FamilyMember row F11B032L52) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B032L53_lift (row : List GridPoint) (h : FamilyMember row F11B032L53) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B032L54_lift (row : List GridPoint) (h : FamilyMember row F11B032L54) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B032L55_lift (row : List GridPoint) (h : FamilyMember row F11B032L55) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B032L56_lift (row : List GridPoint) (h : FamilyMember row F11B032L56) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B032L57_lift (row : List GridPoint) (h : FamilyMember row F11B032L57) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B032L58_lift (row : List GridPoint) (h : FamilyMember row F11B032L58) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B032L59_lift (row : List GridPoint) (h : FamilyMember row F11B032L59) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B032L60_lift (row : List GridPoint) (h : FamilyMember row F11B032L60) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B032L61_lift (row : List GridPoint) (h : FamilyMember row F11B032L61) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B032L62_lift (row : List GridPoint) (h : FamilyMember row F11B032L62) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B032L63_lift (row : List GridPoint) (h : FamilyMember row F11B032L63) : FamilyMember row F11B032 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
