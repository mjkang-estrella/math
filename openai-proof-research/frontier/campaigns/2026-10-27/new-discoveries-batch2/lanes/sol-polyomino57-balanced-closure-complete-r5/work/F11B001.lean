import TreeBlock001
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B001L0 : RowFamilyTree := TreeBlock001L0
abbrev F11B001L1 : RowFamilyTree := TreeBlock001L1
abbrev F11B001L2 : RowFamilyTree := TreeBlock001L2
abbrev F11B001L3 : RowFamilyTree := TreeBlock001L3
abbrev F11B001L4 : RowFamilyTree := TreeBlock001L4
abbrev F11B001L5 : RowFamilyTree := TreeBlock001L5
abbrev F11B001L6 : RowFamilyTree := TreeBlock001L6
abbrev F11B001L7 : RowFamilyTree := TreeBlock001L7
abbrev F11B001L8 : RowFamilyTree := TreeBlock001L8
abbrev F11B001L9 : RowFamilyTree := TreeBlock001L9
abbrev F11B001L10 : RowFamilyTree := TreeBlock001L10
abbrev F11B001L11 : RowFamilyTree := TreeBlock001L11
abbrev F11B001L12 : RowFamilyTree := TreeBlock001L12
abbrev F11B001L13 : RowFamilyTree := TreeBlock001L13
abbrev F11B001L14 : RowFamilyTree := TreeBlock001L14
abbrev F11B001L15 : RowFamilyTree := TreeBlock001L15
abbrev F11B001L16 : RowFamilyTree := TreeBlock001L16
abbrev F11B001L17 : RowFamilyTree := TreeBlock001L17
abbrev F11B001L18 : RowFamilyTree := TreeBlock001L18
abbrev F11B001L19 : RowFamilyTree := TreeBlock001L19
abbrev F11B001L20 : RowFamilyTree := TreeBlock001L20
abbrev F11B001L21 : RowFamilyTree := TreeBlock001L21
abbrev F11B001L22 : RowFamilyTree := TreeBlock001L22
abbrev F11B001L23 : RowFamilyTree := TreeBlock001L23
abbrev F11B001L24 : RowFamilyTree := TreeBlock001L24
abbrev F11B001L25 : RowFamilyTree := TreeBlock001L25
abbrev F11B001L26 : RowFamilyTree := TreeBlock001L26
abbrev F11B001L27 : RowFamilyTree := TreeBlock001L27
abbrev F11B001L28 : RowFamilyTree := TreeBlock001L28
abbrev F11B001L29 : RowFamilyTree := TreeBlock001L29
abbrev F11B001L30 : RowFamilyTree := TreeBlock001L30
abbrev F11B001L31 : RowFamilyTree := TreeBlock001L31
abbrev F11B001L32 : RowFamilyTree := TreeBlock001L32
abbrev F11B001L33 : RowFamilyTree := TreeBlock001L33
abbrev F11B001L34 : RowFamilyTree := TreeBlock001L34
abbrev F11B001L35 : RowFamilyTree := TreeBlock001L35
abbrev F11B001L36 : RowFamilyTree := TreeBlock001L36
abbrev F11B001L37 : RowFamilyTree := TreeBlock001L37
abbrev F11B001L38 : RowFamilyTree := TreeBlock001L38
abbrev F11B001L39 : RowFamilyTree := TreeBlock001L39
abbrev F11B001L40 : RowFamilyTree := TreeBlock001L40
abbrev F11B001L41 : RowFamilyTree := TreeBlock001L41
abbrev F11B001L42 : RowFamilyTree := TreeBlock001L42
abbrev F11B001L43 : RowFamilyTree := TreeBlock001L43
abbrev F11B001L44 : RowFamilyTree := TreeBlock001L44
abbrev F11B001L45 : RowFamilyTree := TreeBlock001L45
abbrev F11B001L46 : RowFamilyTree := TreeBlock001L46
abbrev F11B001L47 : RowFamilyTree := TreeBlock001L47
abbrev F11B001L48 : RowFamilyTree := TreeBlock001L48
abbrev F11B001L49 : RowFamilyTree := TreeBlock001L49
abbrev F11B001L50 : RowFamilyTree := TreeBlock001L50
abbrev F11B001L51 : RowFamilyTree := TreeBlock001L51
abbrev F11B001L52 : RowFamilyTree := TreeBlock001L52
abbrev F11B001L53 : RowFamilyTree := TreeBlock001L53
abbrev F11B001L54 : RowFamilyTree := TreeBlock001L54
abbrev F11B001L55 : RowFamilyTree := TreeBlock001L55
abbrev F11B001L56 : RowFamilyTree := TreeBlock001L56
abbrev F11B001L57 : RowFamilyTree := TreeBlock001L57
abbrev F11B001L58 : RowFamilyTree := TreeBlock001L58
abbrev F11B001L59 : RowFamilyTree := TreeBlock001L59
abbrev F11B001L60 : RowFamilyTree := TreeBlock001L60
abbrev F11B001L61 : RowFamilyTree := TreeBlock001L61
abbrev F11B001L62 : RowFamilyTree := TreeBlock001L62
abbrev F11B001L63 : RowFamilyTree := TreeBlock001L63
abbrev F11B001 : RowFamilyTree := TreeBlock001
theorem F11B001L0_lift (row : List GridPoint) (h : FamilyMember row F11B001L0) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B001L1_lift (row : List GridPoint) (h : FamilyMember row F11B001L1) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B001L2_lift (row : List GridPoint) (h : FamilyMember row F11B001L2) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B001L3_lift (row : List GridPoint) (h : FamilyMember row F11B001L3) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B001L4_lift (row : List GridPoint) (h : FamilyMember row F11B001L4) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B001L5_lift (row : List GridPoint) (h : FamilyMember row F11B001L5) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B001L6_lift (row : List GridPoint) (h : FamilyMember row F11B001L6) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B001L7_lift (row : List GridPoint) (h : FamilyMember row F11B001L7) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B001L8_lift (row : List GridPoint) (h : FamilyMember row F11B001L8) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B001L9_lift (row : List GridPoint) (h : FamilyMember row F11B001L9) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B001L10_lift (row : List GridPoint) (h : FamilyMember row F11B001L10) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B001L11_lift (row : List GridPoint) (h : FamilyMember row F11B001L11) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B001L12_lift (row : List GridPoint) (h : FamilyMember row F11B001L12) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B001L13_lift (row : List GridPoint) (h : FamilyMember row F11B001L13) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B001L14_lift (row : List GridPoint) (h : FamilyMember row F11B001L14) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B001L15_lift (row : List GridPoint) (h : FamilyMember row F11B001L15) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B001L16_lift (row : List GridPoint) (h : FamilyMember row F11B001L16) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B001L17_lift (row : List GridPoint) (h : FamilyMember row F11B001L17) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B001L18_lift (row : List GridPoint) (h : FamilyMember row F11B001L18) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B001L19_lift (row : List GridPoint) (h : FamilyMember row F11B001L19) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B001L20_lift (row : List GridPoint) (h : FamilyMember row F11B001L20) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B001L21_lift (row : List GridPoint) (h : FamilyMember row F11B001L21) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B001L22_lift (row : List GridPoint) (h : FamilyMember row F11B001L22) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B001L23_lift (row : List GridPoint) (h : FamilyMember row F11B001L23) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B001L24_lift (row : List GridPoint) (h : FamilyMember row F11B001L24) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B001L25_lift (row : List GridPoint) (h : FamilyMember row F11B001L25) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B001L26_lift (row : List GridPoint) (h : FamilyMember row F11B001L26) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B001L27_lift (row : List GridPoint) (h : FamilyMember row F11B001L27) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B001L28_lift (row : List GridPoint) (h : FamilyMember row F11B001L28) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B001L29_lift (row : List GridPoint) (h : FamilyMember row F11B001L29) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B001L30_lift (row : List GridPoint) (h : FamilyMember row F11B001L30) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B001L31_lift (row : List GridPoint) (h : FamilyMember row F11B001L31) : FamilyMember row F11B001 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B001L32_lift (row : List GridPoint) (h : FamilyMember row F11B001L32) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B001L33_lift (row : List GridPoint) (h : FamilyMember row F11B001L33) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B001L34_lift (row : List GridPoint) (h : FamilyMember row F11B001L34) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B001L35_lift (row : List GridPoint) (h : FamilyMember row F11B001L35) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B001L36_lift (row : List GridPoint) (h : FamilyMember row F11B001L36) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B001L37_lift (row : List GridPoint) (h : FamilyMember row F11B001L37) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B001L38_lift (row : List GridPoint) (h : FamilyMember row F11B001L38) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B001L39_lift (row : List GridPoint) (h : FamilyMember row F11B001L39) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B001L40_lift (row : List GridPoint) (h : FamilyMember row F11B001L40) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B001L41_lift (row : List GridPoint) (h : FamilyMember row F11B001L41) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B001L42_lift (row : List GridPoint) (h : FamilyMember row F11B001L42) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B001L43_lift (row : List GridPoint) (h : FamilyMember row F11B001L43) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B001L44_lift (row : List GridPoint) (h : FamilyMember row F11B001L44) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B001L45_lift (row : List GridPoint) (h : FamilyMember row F11B001L45) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B001L46_lift (row : List GridPoint) (h : FamilyMember row F11B001L46) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B001L47_lift (row : List GridPoint) (h : FamilyMember row F11B001L47) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B001L48_lift (row : List GridPoint) (h : FamilyMember row F11B001L48) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B001L49_lift (row : List GridPoint) (h : FamilyMember row F11B001L49) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B001L50_lift (row : List GridPoint) (h : FamilyMember row F11B001L50) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B001L51_lift (row : List GridPoint) (h : FamilyMember row F11B001L51) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B001L52_lift (row : List GridPoint) (h : FamilyMember row F11B001L52) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B001L53_lift (row : List GridPoint) (h : FamilyMember row F11B001L53) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B001L54_lift (row : List GridPoint) (h : FamilyMember row F11B001L54) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B001L55_lift (row : List GridPoint) (h : FamilyMember row F11B001L55) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B001L56_lift (row : List GridPoint) (h : FamilyMember row F11B001L56) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B001L57_lift (row : List GridPoint) (h : FamilyMember row F11B001L57) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B001L58_lift (row : List GridPoint) (h : FamilyMember row F11B001L58) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B001L59_lift (row : List GridPoint) (h : FamilyMember row F11B001L59) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B001L60_lift (row : List GridPoint) (h : FamilyMember row F11B001L60) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B001L61_lift (row : List GridPoint) (h : FamilyMember row F11B001L61) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B001L62_lift (row : List GridPoint) (h : FamilyMember row F11B001L62) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B001L63_lift (row : List GridPoint) (h : FamilyMember row F11B001L63) : FamilyMember row F11B001 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
