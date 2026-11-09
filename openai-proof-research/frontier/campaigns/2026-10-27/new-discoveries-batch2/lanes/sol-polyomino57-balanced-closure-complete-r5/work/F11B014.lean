import TreeBlock014
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B014L0 : RowFamilyTree := TreeBlock014L0
abbrev F11B014L1 : RowFamilyTree := TreeBlock014L1
abbrev F11B014L2 : RowFamilyTree := TreeBlock014L2
abbrev F11B014L3 : RowFamilyTree := TreeBlock014L3
abbrev F11B014L4 : RowFamilyTree := TreeBlock014L4
abbrev F11B014L5 : RowFamilyTree := TreeBlock014L5
abbrev F11B014L6 : RowFamilyTree := TreeBlock014L6
abbrev F11B014L7 : RowFamilyTree := TreeBlock014L7
abbrev F11B014L8 : RowFamilyTree := TreeBlock014L8
abbrev F11B014L9 : RowFamilyTree := TreeBlock014L9
abbrev F11B014L10 : RowFamilyTree := TreeBlock014L10
abbrev F11B014L11 : RowFamilyTree := TreeBlock014L11
abbrev F11B014L12 : RowFamilyTree := TreeBlock014L12
abbrev F11B014L13 : RowFamilyTree := TreeBlock014L13
abbrev F11B014L14 : RowFamilyTree := TreeBlock014L14
abbrev F11B014L15 : RowFamilyTree := TreeBlock014L15
abbrev F11B014L16 : RowFamilyTree := TreeBlock014L16
abbrev F11B014L17 : RowFamilyTree := TreeBlock014L17
abbrev F11B014L18 : RowFamilyTree := TreeBlock014L18
abbrev F11B014L19 : RowFamilyTree := TreeBlock014L19
abbrev F11B014L20 : RowFamilyTree := TreeBlock014L20
abbrev F11B014L21 : RowFamilyTree := TreeBlock014L21
abbrev F11B014L22 : RowFamilyTree := TreeBlock014L22
abbrev F11B014L23 : RowFamilyTree := TreeBlock014L23
abbrev F11B014L24 : RowFamilyTree := TreeBlock014L24
abbrev F11B014L25 : RowFamilyTree := TreeBlock014L25
abbrev F11B014L26 : RowFamilyTree := TreeBlock014L26
abbrev F11B014L27 : RowFamilyTree := TreeBlock014L27
abbrev F11B014L28 : RowFamilyTree := TreeBlock014L28
abbrev F11B014L29 : RowFamilyTree := TreeBlock014L29
abbrev F11B014L30 : RowFamilyTree := TreeBlock014L30
abbrev F11B014L31 : RowFamilyTree := TreeBlock014L31
abbrev F11B014L32 : RowFamilyTree := TreeBlock014L32
abbrev F11B014L33 : RowFamilyTree := TreeBlock014L33
abbrev F11B014L34 : RowFamilyTree := TreeBlock014L34
abbrev F11B014L35 : RowFamilyTree := TreeBlock014L35
abbrev F11B014L36 : RowFamilyTree := TreeBlock014L36
abbrev F11B014L37 : RowFamilyTree := TreeBlock014L37
abbrev F11B014L38 : RowFamilyTree := TreeBlock014L38
abbrev F11B014L39 : RowFamilyTree := TreeBlock014L39
abbrev F11B014L40 : RowFamilyTree := TreeBlock014L40
abbrev F11B014L41 : RowFamilyTree := TreeBlock014L41
abbrev F11B014L42 : RowFamilyTree := TreeBlock014L42
abbrev F11B014L43 : RowFamilyTree := TreeBlock014L43
abbrev F11B014L44 : RowFamilyTree := TreeBlock014L44
abbrev F11B014L45 : RowFamilyTree := TreeBlock014L45
abbrev F11B014L46 : RowFamilyTree := TreeBlock014L46
abbrev F11B014L47 : RowFamilyTree := TreeBlock014L47
abbrev F11B014L48 : RowFamilyTree := TreeBlock014L48
abbrev F11B014L49 : RowFamilyTree := TreeBlock014L49
abbrev F11B014L50 : RowFamilyTree := TreeBlock014L50
abbrev F11B014L51 : RowFamilyTree := TreeBlock014L51
abbrev F11B014L52 : RowFamilyTree := TreeBlock014L52
abbrev F11B014L53 : RowFamilyTree := TreeBlock014L53
abbrev F11B014L54 : RowFamilyTree := TreeBlock014L54
abbrev F11B014L55 : RowFamilyTree := TreeBlock014L55
abbrev F11B014L56 : RowFamilyTree := TreeBlock014L56
abbrev F11B014L57 : RowFamilyTree := TreeBlock014L57
abbrev F11B014L58 : RowFamilyTree := TreeBlock014L58
abbrev F11B014L59 : RowFamilyTree := TreeBlock014L59
abbrev F11B014L60 : RowFamilyTree := TreeBlock014L60
abbrev F11B014L61 : RowFamilyTree := TreeBlock014L61
abbrev F11B014L62 : RowFamilyTree := TreeBlock014L62
abbrev F11B014L63 : RowFamilyTree := TreeBlock014L63
abbrev F11B014 : RowFamilyTree := TreeBlock014
theorem F11B014L0_lift (row : List GridPoint) (h : FamilyMember row F11B014L0) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B014L1_lift (row : List GridPoint) (h : FamilyMember row F11B014L1) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B014L2_lift (row : List GridPoint) (h : FamilyMember row F11B014L2) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B014L3_lift (row : List GridPoint) (h : FamilyMember row F11B014L3) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B014L4_lift (row : List GridPoint) (h : FamilyMember row F11B014L4) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B014L5_lift (row : List GridPoint) (h : FamilyMember row F11B014L5) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B014L6_lift (row : List GridPoint) (h : FamilyMember row F11B014L6) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B014L7_lift (row : List GridPoint) (h : FamilyMember row F11B014L7) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B014L8_lift (row : List GridPoint) (h : FamilyMember row F11B014L8) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B014L9_lift (row : List GridPoint) (h : FamilyMember row F11B014L9) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B014L10_lift (row : List GridPoint) (h : FamilyMember row F11B014L10) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B014L11_lift (row : List GridPoint) (h : FamilyMember row F11B014L11) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B014L12_lift (row : List GridPoint) (h : FamilyMember row F11B014L12) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B014L13_lift (row : List GridPoint) (h : FamilyMember row F11B014L13) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B014L14_lift (row : List GridPoint) (h : FamilyMember row F11B014L14) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B014L15_lift (row : List GridPoint) (h : FamilyMember row F11B014L15) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B014L16_lift (row : List GridPoint) (h : FamilyMember row F11B014L16) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B014L17_lift (row : List GridPoint) (h : FamilyMember row F11B014L17) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B014L18_lift (row : List GridPoint) (h : FamilyMember row F11B014L18) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B014L19_lift (row : List GridPoint) (h : FamilyMember row F11B014L19) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B014L20_lift (row : List GridPoint) (h : FamilyMember row F11B014L20) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B014L21_lift (row : List GridPoint) (h : FamilyMember row F11B014L21) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B014L22_lift (row : List GridPoint) (h : FamilyMember row F11B014L22) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B014L23_lift (row : List GridPoint) (h : FamilyMember row F11B014L23) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B014L24_lift (row : List GridPoint) (h : FamilyMember row F11B014L24) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B014L25_lift (row : List GridPoint) (h : FamilyMember row F11B014L25) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B014L26_lift (row : List GridPoint) (h : FamilyMember row F11B014L26) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B014L27_lift (row : List GridPoint) (h : FamilyMember row F11B014L27) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B014L28_lift (row : List GridPoint) (h : FamilyMember row F11B014L28) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B014L29_lift (row : List GridPoint) (h : FamilyMember row F11B014L29) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B014L30_lift (row : List GridPoint) (h : FamilyMember row F11B014L30) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B014L31_lift (row : List GridPoint) (h : FamilyMember row F11B014L31) : FamilyMember row F11B014 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B014L32_lift (row : List GridPoint) (h : FamilyMember row F11B014L32) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B014L33_lift (row : List GridPoint) (h : FamilyMember row F11B014L33) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B014L34_lift (row : List GridPoint) (h : FamilyMember row F11B014L34) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B014L35_lift (row : List GridPoint) (h : FamilyMember row F11B014L35) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B014L36_lift (row : List GridPoint) (h : FamilyMember row F11B014L36) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B014L37_lift (row : List GridPoint) (h : FamilyMember row F11B014L37) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B014L38_lift (row : List GridPoint) (h : FamilyMember row F11B014L38) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B014L39_lift (row : List GridPoint) (h : FamilyMember row F11B014L39) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B014L40_lift (row : List GridPoint) (h : FamilyMember row F11B014L40) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B014L41_lift (row : List GridPoint) (h : FamilyMember row F11B014L41) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B014L42_lift (row : List GridPoint) (h : FamilyMember row F11B014L42) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B014L43_lift (row : List GridPoint) (h : FamilyMember row F11B014L43) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B014L44_lift (row : List GridPoint) (h : FamilyMember row F11B014L44) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B014L45_lift (row : List GridPoint) (h : FamilyMember row F11B014L45) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B014L46_lift (row : List GridPoint) (h : FamilyMember row F11B014L46) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B014L47_lift (row : List GridPoint) (h : FamilyMember row F11B014L47) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B014L48_lift (row : List GridPoint) (h : FamilyMember row F11B014L48) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B014L49_lift (row : List GridPoint) (h : FamilyMember row F11B014L49) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B014L50_lift (row : List GridPoint) (h : FamilyMember row F11B014L50) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B014L51_lift (row : List GridPoint) (h : FamilyMember row F11B014L51) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B014L52_lift (row : List GridPoint) (h : FamilyMember row F11B014L52) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B014L53_lift (row : List GridPoint) (h : FamilyMember row F11B014L53) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B014L54_lift (row : List GridPoint) (h : FamilyMember row F11B014L54) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B014L55_lift (row : List GridPoint) (h : FamilyMember row F11B014L55) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B014L56_lift (row : List GridPoint) (h : FamilyMember row F11B014L56) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B014L57_lift (row : List GridPoint) (h : FamilyMember row F11B014L57) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B014L58_lift (row : List GridPoint) (h : FamilyMember row F11B014L58) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B014L59_lift (row : List GridPoint) (h : FamilyMember row F11B014L59) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B014L60_lift (row : List GridPoint) (h : FamilyMember row F11B014L60) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B014L61_lift (row : List GridPoint) (h : FamilyMember row F11B014L61) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B014L62_lift (row : List GridPoint) (h : FamilyMember row F11B014L62) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B014L63_lift (row : List GridPoint) (h : FamilyMember row F11B014L63) : FamilyMember row F11B014 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
