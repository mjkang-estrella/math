import TreeBlock015
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B015L0 : RowFamilyTree := TreeBlock015L0
abbrev F11B015L1 : RowFamilyTree := TreeBlock015L1
abbrev F11B015L2 : RowFamilyTree := TreeBlock015L2
abbrev F11B015L3 : RowFamilyTree := TreeBlock015L3
abbrev F11B015L4 : RowFamilyTree := TreeBlock015L4
abbrev F11B015L5 : RowFamilyTree := TreeBlock015L5
abbrev F11B015L6 : RowFamilyTree := TreeBlock015L6
abbrev F11B015L7 : RowFamilyTree := TreeBlock015L7
abbrev F11B015L8 : RowFamilyTree := TreeBlock015L8
abbrev F11B015L9 : RowFamilyTree := TreeBlock015L9
abbrev F11B015L10 : RowFamilyTree := TreeBlock015L10
abbrev F11B015L11 : RowFamilyTree := TreeBlock015L11
abbrev F11B015L12 : RowFamilyTree := TreeBlock015L12
abbrev F11B015L13 : RowFamilyTree := TreeBlock015L13
abbrev F11B015L14 : RowFamilyTree := TreeBlock015L14
abbrev F11B015L15 : RowFamilyTree := TreeBlock015L15
abbrev F11B015L16 : RowFamilyTree := TreeBlock015L16
abbrev F11B015L17 : RowFamilyTree := TreeBlock015L17
abbrev F11B015L18 : RowFamilyTree := TreeBlock015L18
abbrev F11B015L19 : RowFamilyTree := TreeBlock015L19
abbrev F11B015L20 : RowFamilyTree := TreeBlock015L20
abbrev F11B015L21 : RowFamilyTree := TreeBlock015L21
abbrev F11B015L22 : RowFamilyTree := TreeBlock015L22
abbrev F11B015L23 : RowFamilyTree := TreeBlock015L23
abbrev F11B015L24 : RowFamilyTree := TreeBlock015L24
abbrev F11B015L25 : RowFamilyTree := TreeBlock015L25
abbrev F11B015L26 : RowFamilyTree := TreeBlock015L26
abbrev F11B015L27 : RowFamilyTree := TreeBlock015L27
abbrev F11B015L28 : RowFamilyTree := TreeBlock015L28
abbrev F11B015L29 : RowFamilyTree := TreeBlock015L29
abbrev F11B015L30 : RowFamilyTree := TreeBlock015L30
abbrev F11B015L31 : RowFamilyTree := TreeBlock015L31
abbrev F11B015L32 : RowFamilyTree := TreeBlock015L32
abbrev F11B015L33 : RowFamilyTree := TreeBlock015L33
abbrev F11B015L34 : RowFamilyTree := TreeBlock015L34
abbrev F11B015L35 : RowFamilyTree := TreeBlock015L35
abbrev F11B015L36 : RowFamilyTree := TreeBlock015L36
abbrev F11B015L37 : RowFamilyTree := TreeBlock015L37
abbrev F11B015L38 : RowFamilyTree := TreeBlock015L38
abbrev F11B015L39 : RowFamilyTree := TreeBlock015L39
abbrev F11B015L40 : RowFamilyTree := TreeBlock015L40
abbrev F11B015L41 : RowFamilyTree := TreeBlock015L41
abbrev F11B015L42 : RowFamilyTree := TreeBlock015L42
abbrev F11B015L43 : RowFamilyTree := TreeBlock015L43
abbrev F11B015L44 : RowFamilyTree := TreeBlock015L44
abbrev F11B015L45 : RowFamilyTree := TreeBlock015L45
abbrev F11B015L46 : RowFamilyTree := TreeBlock015L46
abbrev F11B015L47 : RowFamilyTree := TreeBlock015L47
abbrev F11B015L48 : RowFamilyTree := TreeBlock015L48
abbrev F11B015L49 : RowFamilyTree := TreeBlock015L49
abbrev F11B015L50 : RowFamilyTree := TreeBlock015L50
abbrev F11B015L51 : RowFamilyTree := TreeBlock015L51
abbrev F11B015L52 : RowFamilyTree := TreeBlock015L52
abbrev F11B015L53 : RowFamilyTree := TreeBlock015L53
abbrev F11B015L54 : RowFamilyTree := TreeBlock015L54
abbrev F11B015L55 : RowFamilyTree := TreeBlock015L55
abbrev F11B015L56 : RowFamilyTree := TreeBlock015L56
abbrev F11B015L57 : RowFamilyTree := TreeBlock015L57
abbrev F11B015L58 : RowFamilyTree := TreeBlock015L58
abbrev F11B015L59 : RowFamilyTree := TreeBlock015L59
abbrev F11B015L60 : RowFamilyTree := TreeBlock015L60
abbrev F11B015L61 : RowFamilyTree := TreeBlock015L61
abbrev F11B015L62 : RowFamilyTree := TreeBlock015L62
abbrev F11B015L63 : RowFamilyTree := TreeBlock015L63
abbrev F11B015 : RowFamilyTree := TreeBlock015
theorem F11B015L0_lift (row : List GridPoint) (h : FamilyMember row F11B015L0) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B015L1_lift (row : List GridPoint) (h : FamilyMember row F11B015L1) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B015L2_lift (row : List GridPoint) (h : FamilyMember row F11B015L2) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B015L3_lift (row : List GridPoint) (h : FamilyMember row F11B015L3) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B015L4_lift (row : List GridPoint) (h : FamilyMember row F11B015L4) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B015L5_lift (row : List GridPoint) (h : FamilyMember row F11B015L5) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B015L6_lift (row : List GridPoint) (h : FamilyMember row F11B015L6) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B015L7_lift (row : List GridPoint) (h : FamilyMember row F11B015L7) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B015L8_lift (row : List GridPoint) (h : FamilyMember row F11B015L8) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B015L9_lift (row : List GridPoint) (h : FamilyMember row F11B015L9) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B015L10_lift (row : List GridPoint) (h : FamilyMember row F11B015L10) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B015L11_lift (row : List GridPoint) (h : FamilyMember row F11B015L11) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B015L12_lift (row : List GridPoint) (h : FamilyMember row F11B015L12) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B015L13_lift (row : List GridPoint) (h : FamilyMember row F11B015L13) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B015L14_lift (row : List GridPoint) (h : FamilyMember row F11B015L14) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B015L15_lift (row : List GridPoint) (h : FamilyMember row F11B015L15) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B015L16_lift (row : List GridPoint) (h : FamilyMember row F11B015L16) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B015L17_lift (row : List GridPoint) (h : FamilyMember row F11B015L17) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B015L18_lift (row : List GridPoint) (h : FamilyMember row F11B015L18) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B015L19_lift (row : List GridPoint) (h : FamilyMember row F11B015L19) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B015L20_lift (row : List GridPoint) (h : FamilyMember row F11B015L20) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B015L21_lift (row : List GridPoint) (h : FamilyMember row F11B015L21) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B015L22_lift (row : List GridPoint) (h : FamilyMember row F11B015L22) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B015L23_lift (row : List GridPoint) (h : FamilyMember row F11B015L23) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B015L24_lift (row : List GridPoint) (h : FamilyMember row F11B015L24) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B015L25_lift (row : List GridPoint) (h : FamilyMember row F11B015L25) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B015L26_lift (row : List GridPoint) (h : FamilyMember row F11B015L26) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B015L27_lift (row : List GridPoint) (h : FamilyMember row F11B015L27) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B015L28_lift (row : List GridPoint) (h : FamilyMember row F11B015L28) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B015L29_lift (row : List GridPoint) (h : FamilyMember row F11B015L29) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B015L30_lift (row : List GridPoint) (h : FamilyMember row F11B015L30) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B015L31_lift (row : List GridPoint) (h : FamilyMember row F11B015L31) : FamilyMember row F11B015 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B015L32_lift (row : List GridPoint) (h : FamilyMember row F11B015L32) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B015L33_lift (row : List GridPoint) (h : FamilyMember row F11B015L33) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B015L34_lift (row : List GridPoint) (h : FamilyMember row F11B015L34) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B015L35_lift (row : List GridPoint) (h : FamilyMember row F11B015L35) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B015L36_lift (row : List GridPoint) (h : FamilyMember row F11B015L36) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B015L37_lift (row : List GridPoint) (h : FamilyMember row F11B015L37) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B015L38_lift (row : List GridPoint) (h : FamilyMember row F11B015L38) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B015L39_lift (row : List GridPoint) (h : FamilyMember row F11B015L39) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B015L40_lift (row : List GridPoint) (h : FamilyMember row F11B015L40) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B015L41_lift (row : List GridPoint) (h : FamilyMember row F11B015L41) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B015L42_lift (row : List GridPoint) (h : FamilyMember row F11B015L42) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B015L43_lift (row : List GridPoint) (h : FamilyMember row F11B015L43) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B015L44_lift (row : List GridPoint) (h : FamilyMember row F11B015L44) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B015L45_lift (row : List GridPoint) (h : FamilyMember row F11B015L45) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B015L46_lift (row : List GridPoint) (h : FamilyMember row F11B015L46) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B015L47_lift (row : List GridPoint) (h : FamilyMember row F11B015L47) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B015L48_lift (row : List GridPoint) (h : FamilyMember row F11B015L48) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B015L49_lift (row : List GridPoint) (h : FamilyMember row F11B015L49) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B015L50_lift (row : List GridPoint) (h : FamilyMember row F11B015L50) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B015L51_lift (row : List GridPoint) (h : FamilyMember row F11B015L51) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B015L52_lift (row : List GridPoint) (h : FamilyMember row F11B015L52) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B015L53_lift (row : List GridPoint) (h : FamilyMember row F11B015L53) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B015L54_lift (row : List GridPoint) (h : FamilyMember row F11B015L54) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B015L55_lift (row : List GridPoint) (h : FamilyMember row F11B015L55) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B015L56_lift (row : List GridPoint) (h : FamilyMember row F11B015L56) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B015L57_lift (row : List GridPoint) (h : FamilyMember row F11B015L57) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B015L58_lift (row : List GridPoint) (h : FamilyMember row F11B015L58) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B015L59_lift (row : List GridPoint) (h : FamilyMember row F11B015L59) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B015L60_lift (row : List GridPoint) (h : FamilyMember row F11B015L60) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B015L61_lift (row : List GridPoint) (h : FamilyMember row F11B015L61) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B015L62_lift (row : List GridPoint) (h : FamilyMember row F11B015L62) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B015L63_lift (row : List GridPoint) (h : FamilyMember row F11B015L63) : FamilyMember row F11B015 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
