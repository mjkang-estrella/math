import TreeBlock021
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B021L0 : RowFamilyTree := TreeBlock021L0
abbrev F11B021L1 : RowFamilyTree := TreeBlock021L1
abbrev F11B021L2 : RowFamilyTree := TreeBlock021L2
abbrev F11B021L3 : RowFamilyTree := TreeBlock021L3
abbrev F11B021L4 : RowFamilyTree := TreeBlock021L4
abbrev F11B021L5 : RowFamilyTree := TreeBlock021L5
abbrev F11B021L6 : RowFamilyTree := TreeBlock021L6
abbrev F11B021L7 : RowFamilyTree := TreeBlock021L7
abbrev F11B021L8 : RowFamilyTree := TreeBlock021L8
abbrev F11B021L9 : RowFamilyTree := TreeBlock021L9
abbrev F11B021L10 : RowFamilyTree := TreeBlock021L10
abbrev F11B021L11 : RowFamilyTree := TreeBlock021L11
abbrev F11B021L12 : RowFamilyTree := TreeBlock021L12
abbrev F11B021L13 : RowFamilyTree := TreeBlock021L13
abbrev F11B021L14 : RowFamilyTree := TreeBlock021L14
abbrev F11B021L15 : RowFamilyTree := TreeBlock021L15
abbrev F11B021L16 : RowFamilyTree := TreeBlock021L16
abbrev F11B021L17 : RowFamilyTree := TreeBlock021L17
abbrev F11B021L18 : RowFamilyTree := TreeBlock021L18
abbrev F11B021L19 : RowFamilyTree := TreeBlock021L19
abbrev F11B021L20 : RowFamilyTree := TreeBlock021L20
abbrev F11B021L21 : RowFamilyTree := TreeBlock021L21
abbrev F11B021L22 : RowFamilyTree := TreeBlock021L22
abbrev F11B021L23 : RowFamilyTree := TreeBlock021L23
abbrev F11B021L24 : RowFamilyTree := TreeBlock021L24
abbrev F11B021L25 : RowFamilyTree := TreeBlock021L25
abbrev F11B021L26 : RowFamilyTree := TreeBlock021L26
abbrev F11B021L27 : RowFamilyTree := TreeBlock021L27
abbrev F11B021L28 : RowFamilyTree := TreeBlock021L28
abbrev F11B021L29 : RowFamilyTree := TreeBlock021L29
abbrev F11B021L30 : RowFamilyTree := TreeBlock021L30
abbrev F11B021L31 : RowFamilyTree := TreeBlock021L31
abbrev F11B021L32 : RowFamilyTree := TreeBlock021L32
abbrev F11B021L33 : RowFamilyTree := TreeBlock021L33
abbrev F11B021L34 : RowFamilyTree := TreeBlock021L34
abbrev F11B021L35 : RowFamilyTree := TreeBlock021L35
abbrev F11B021L36 : RowFamilyTree := TreeBlock021L36
abbrev F11B021L37 : RowFamilyTree := TreeBlock021L37
abbrev F11B021L38 : RowFamilyTree := TreeBlock021L38
abbrev F11B021L39 : RowFamilyTree := TreeBlock021L39
abbrev F11B021L40 : RowFamilyTree := TreeBlock021L40
abbrev F11B021L41 : RowFamilyTree := TreeBlock021L41
abbrev F11B021L42 : RowFamilyTree := TreeBlock021L42
abbrev F11B021L43 : RowFamilyTree := TreeBlock021L43
abbrev F11B021L44 : RowFamilyTree := TreeBlock021L44
abbrev F11B021L45 : RowFamilyTree := TreeBlock021L45
abbrev F11B021L46 : RowFamilyTree := TreeBlock021L46
abbrev F11B021L47 : RowFamilyTree := TreeBlock021L47
abbrev F11B021L48 : RowFamilyTree := TreeBlock021L48
abbrev F11B021L49 : RowFamilyTree := TreeBlock021L49
abbrev F11B021L50 : RowFamilyTree := TreeBlock021L50
abbrev F11B021L51 : RowFamilyTree := TreeBlock021L51
abbrev F11B021L52 : RowFamilyTree := TreeBlock021L52
abbrev F11B021L53 : RowFamilyTree := TreeBlock021L53
abbrev F11B021L54 : RowFamilyTree := TreeBlock021L54
abbrev F11B021L55 : RowFamilyTree := TreeBlock021L55
abbrev F11B021L56 : RowFamilyTree := TreeBlock021L56
abbrev F11B021L57 : RowFamilyTree := TreeBlock021L57
abbrev F11B021L58 : RowFamilyTree := TreeBlock021L58
abbrev F11B021L59 : RowFamilyTree := TreeBlock021L59
abbrev F11B021L60 : RowFamilyTree := TreeBlock021L60
abbrev F11B021L61 : RowFamilyTree := TreeBlock021L61
abbrev F11B021L62 : RowFamilyTree := TreeBlock021L62
abbrev F11B021L63 : RowFamilyTree := TreeBlock021L63
abbrev F11B021 : RowFamilyTree := TreeBlock021
theorem F11B021L0_lift (row : List GridPoint) (h : FamilyMember row F11B021L0) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B021L1_lift (row : List GridPoint) (h : FamilyMember row F11B021L1) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B021L2_lift (row : List GridPoint) (h : FamilyMember row F11B021L2) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B021L3_lift (row : List GridPoint) (h : FamilyMember row F11B021L3) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B021L4_lift (row : List GridPoint) (h : FamilyMember row F11B021L4) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B021L5_lift (row : List GridPoint) (h : FamilyMember row F11B021L5) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B021L6_lift (row : List GridPoint) (h : FamilyMember row F11B021L6) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B021L7_lift (row : List GridPoint) (h : FamilyMember row F11B021L7) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B021L8_lift (row : List GridPoint) (h : FamilyMember row F11B021L8) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B021L9_lift (row : List GridPoint) (h : FamilyMember row F11B021L9) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B021L10_lift (row : List GridPoint) (h : FamilyMember row F11B021L10) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B021L11_lift (row : List GridPoint) (h : FamilyMember row F11B021L11) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B021L12_lift (row : List GridPoint) (h : FamilyMember row F11B021L12) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B021L13_lift (row : List GridPoint) (h : FamilyMember row F11B021L13) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B021L14_lift (row : List GridPoint) (h : FamilyMember row F11B021L14) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B021L15_lift (row : List GridPoint) (h : FamilyMember row F11B021L15) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B021L16_lift (row : List GridPoint) (h : FamilyMember row F11B021L16) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B021L17_lift (row : List GridPoint) (h : FamilyMember row F11B021L17) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B021L18_lift (row : List GridPoint) (h : FamilyMember row F11B021L18) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B021L19_lift (row : List GridPoint) (h : FamilyMember row F11B021L19) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B021L20_lift (row : List GridPoint) (h : FamilyMember row F11B021L20) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B021L21_lift (row : List GridPoint) (h : FamilyMember row F11B021L21) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B021L22_lift (row : List GridPoint) (h : FamilyMember row F11B021L22) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B021L23_lift (row : List GridPoint) (h : FamilyMember row F11B021L23) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B021L24_lift (row : List GridPoint) (h : FamilyMember row F11B021L24) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B021L25_lift (row : List GridPoint) (h : FamilyMember row F11B021L25) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B021L26_lift (row : List GridPoint) (h : FamilyMember row F11B021L26) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B021L27_lift (row : List GridPoint) (h : FamilyMember row F11B021L27) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B021L28_lift (row : List GridPoint) (h : FamilyMember row F11B021L28) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B021L29_lift (row : List GridPoint) (h : FamilyMember row F11B021L29) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B021L30_lift (row : List GridPoint) (h : FamilyMember row F11B021L30) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B021L31_lift (row : List GridPoint) (h : FamilyMember row F11B021L31) : FamilyMember row F11B021 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B021L32_lift (row : List GridPoint) (h : FamilyMember row F11B021L32) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B021L33_lift (row : List GridPoint) (h : FamilyMember row F11B021L33) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B021L34_lift (row : List GridPoint) (h : FamilyMember row F11B021L34) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B021L35_lift (row : List GridPoint) (h : FamilyMember row F11B021L35) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B021L36_lift (row : List GridPoint) (h : FamilyMember row F11B021L36) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B021L37_lift (row : List GridPoint) (h : FamilyMember row F11B021L37) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B021L38_lift (row : List GridPoint) (h : FamilyMember row F11B021L38) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B021L39_lift (row : List GridPoint) (h : FamilyMember row F11B021L39) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B021L40_lift (row : List GridPoint) (h : FamilyMember row F11B021L40) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B021L41_lift (row : List GridPoint) (h : FamilyMember row F11B021L41) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B021L42_lift (row : List GridPoint) (h : FamilyMember row F11B021L42) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B021L43_lift (row : List GridPoint) (h : FamilyMember row F11B021L43) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B021L44_lift (row : List GridPoint) (h : FamilyMember row F11B021L44) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B021L45_lift (row : List GridPoint) (h : FamilyMember row F11B021L45) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B021L46_lift (row : List GridPoint) (h : FamilyMember row F11B021L46) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B021L47_lift (row : List GridPoint) (h : FamilyMember row F11B021L47) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B021L48_lift (row : List GridPoint) (h : FamilyMember row F11B021L48) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B021L49_lift (row : List GridPoint) (h : FamilyMember row F11B021L49) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B021L50_lift (row : List GridPoint) (h : FamilyMember row F11B021L50) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B021L51_lift (row : List GridPoint) (h : FamilyMember row F11B021L51) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B021L52_lift (row : List GridPoint) (h : FamilyMember row F11B021L52) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B021L53_lift (row : List GridPoint) (h : FamilyMember row F11B021L53) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B021L54_lift (row : List GridPoint) (h : FamilyMember row F11B021L54) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B021L55_lift (row : List GridPoint) (h : FamilyMember row F11B021L55) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B021L56_lift (row : List GridPoint) (h : FamilyMember row F11B021L56) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B021L57_lift (row : List GridPoint) (h : FamilyMember row F11B021L57) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B021L58_lift (row : List GridPoint) (h : FamilyMember row F11B021L58) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B021L59_lift (row : List GridPoint) (h : FamilyMember row F11B021L59) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B021L60_lift (row : List GridPoint) (h : FamilyMember row F11B021L60) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B021L61_lift (row : List GridPoint) (h : FamilyMember row F11B021L61) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B021L62_lift (row : List GridPoint) (h : FamilyMember row F11B021L62) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B021L63_lift (row : List GridPoint) (h : FamilyMember row F11B021L63) : FamilyMember row F11B021 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
