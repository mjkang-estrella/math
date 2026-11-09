import TreeBlock026
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B026L0 : RowFamilyTree := TreeBlock026L0
abbrev F11B026L1 : RowFamilyTree := TreeBlock026L1
abbrev F11B026L2 : RowFamilyTree := TreeBlock026L2
abbrev F11B026L3 : RowFamilyTree := TreeBlock026L3
abbrev F11B026L4 : RowFamilyTree := TreeBlock026L4
abbrev F11B026L5 : RowFamilyTree := TreeBlock026L5
abbrev F11B026L6 : RowFamilyTree := TreeBlock026L6
abbrev F11B026L7 : RowFamilyTree := TreeBlock026L7
abbrev F11B026L8 : RowFamilyTree := TreeBlock026L8
abbrev F11B026L9 : RowFamilyTree := TreeBlock026L9
abbrev F11B026L10 : RowFamilyTree := TreeBlock026L10
abbrev F11B026L11 : RowFamilyTree := TreeBlock026L11
abbrev F11B026L12 : RowFamilyTree := TreeBlock026L12
abbrev F11B026L13 : RowFamilyTree := TreeBlock026L13
abbrev F11B026L14 : RowFamilyTree := TreeBlock026L14
abbrev F11B026L15 : RowFamilyTree := TreeBlock026L15
abbrev F11B026L16 : RowFamilyTree := TreeBlock026L16
abbrev F11B026L17 : RowFamilyTree := TreeBlock026L17
abbrev F11B026L18 : RowFamilyTree := TreeBlock026L18
abbrev F11B026L19 : RowFamilyTree := TreeBlock026L19
abbrev F11B026L20 : RowFamilyTree := TreeBlock026L20
abbrev F11B026L21 : RowFamilyTree := TreeBlock026L21
abbrev F11B026L22 : RowFamilyTree := TreeBlock026L22
abbrev F11B026L23 : RowFamilyTree := TreeBlock026L23
abbrev F11B026L24 : RowFamilyTree := TreeBlock026L24
abbrev F11B026L25 : RowFamilyTree := TreeBlock026L25
abbrev F11B026L26 : RowFamilyTree := TreeBlock026L26
abbrev F11B026L27 : RowFamilyTree := TreeBlock026L27
abbrev F11B026L28 : RowFamilyTree := TreeBlock026L28
abbrev F11B026L29 : RowFamilyTree := TreeBlock026L29
abbrev F11B026L30 : RowFamilyTree := TreeBlock026L30
abbrev F11B026L31 : RowFamilyTree := TreeBlock026L31
abbrev F11B026L32 : RowFamilyTree := TreeBlock026L32
abbrev F11B026L33 : RowFamilyTree := TreeBlock026L33
abbrev F11B026L34 : RowFamilyTree := TreeBlock026L34
abbrev F11B026L35 : RowFamilyTree := TreeBlock026L35
abbrev F11B026L36 : RowFamilyTree := TreeBlock026L36
abbrev F11B026L37 : RowFamilyTree := TreeBlock026L37
abbrev F11B026L38 : RowFamilyTree := TreeBlock026L38
abbrev F11B026L39 : RowFamilyTree := TreeBlock026L39
abbrev F11B026L40 : RowFamilyTree := TreeBlock026L40
abbrev F11B026L41 : RowFamilyTree := TreeBlock026L41
abbrev F11B026L42 : RowFamilyTree := TreeBlock026L42
abbrev F11B026L43 : RowFamilyTree := TreeBlock026L43
abbrev F11B026L44 : RowFamilyTree := TreeBlock026L44
abbrev F11B026L45 : RowFamilyTree := TreeBlock026L45
abbrev F11B026L46 : RowFamilyTree := TreeBlock026L46
abbrev F11B026L47 : RowFamilyTree := TreeBlock026L47
abbrev F11B026L48 : RowFamilyTree := TreeBlock026L48
abbrev F11B026L49 : RowFamilyTree := TreeBlock026L49
abbrev F11B026L50 : RowFamilyTree := TreeBlock026L50
abbrev F11B026L51 : RowFamilyTree := TreeBlock026L51
abbrev F11B026L52 : RowFamilyTree := TreeBlock026L52
abbrev F11B026L53 : RowFamilyTree := TreeBlock026L53
abbrev F11B026L54 : RowFamilyTree := TreeBlock026L54
abbrev F11B026L55 : RowFamilyTree := TreeBlock026L55
abbrev F11B026L56 : RowFamilyTree := TreeBlock026L56
abbrev F11B026L57 : RowFamilyTree := TreeBlock026L57
abbrev F11B026L58 : RowFamilyTree := TreeBlock026L58
abbrev F11B026L59 : RowFamilyTree := TreeBlock026L59
abbrev F11B026L60 : RowFamilyTree := TreeBlock026L60
abbrev F11B026L61 : RowFamilyTree := TreeBlock026L61
abbrev F11B026L62 : RowFamilyTree := TreeBlock026L62
abbrev F11B026L63 : RowFamilyTree := TreeBlock026L63
abbrev F11B026 : RowFamilyTree := TreeBlock026
theorem F11B026L0_lift (row : List GridPoint) (h : FamilyMember row F11B026L0) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B026L1_lift (row : List GridPoint) (h : FamilyMember row F11B026L1) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B026L2_lift (row : List GridPoint) (h : FamilyMember row F11B026L2) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B026L3_lift (row : List GridPoint) (h : FamilyMember row F11B026L3) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B026L4_lift (row : List GridPoint) (h : FamilyMember row F11B026L4) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B026L5_lift (row : List GridPoint) (h : FamilyMember row F11B026L5) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B026L6_lift (row : List GridPoint) (h : FamilyMember row F11B026L6) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B026L7_lift (row : List GridPoint) (h : FamilyMember row F11B026L7) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B026L8_lift (row : List GridPoint) (h : FamilyMember row F11B026L8) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B026L9_lift (row : List GridPoint) (h : FamilyMember row F11B026L9) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B026L10_lift (row : List GridPoint) (h : FamilyMember row F11B026L10) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B026L11_lift (row : List GridPoint) (h : FamilyMember row F11B026L11) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B026L12_lift (row : List GridPoint) (h : FamilyMember row F11B026L12) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B026L13_lift (row : List GridPoint) (h : FamilyMember row F11B026L13) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B026L14_lift (row : List GridPoint) (h : FamilyMember row F11B026L14) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B026L15_lift (row : List GridPoint) (h : FamilyMember row F11B026L15) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B026L16_lift (row : List GridPoint) (h : FamilyMember row F11B026L16) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B026L17_lift (row : List GridPoint) (h : FamilyMember row F11B026L17) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B026L18_lift (row : List GridPoint) (h : FamilyMember row F11B026L18) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B026L19_lift (row : List GridPoint) (h : FamilyMember row F11B026L19) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B026L20_lift (row : List GridPoint) (h : FamilyMember row F11B026L20) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B026L21_lift (row : List GridPoint) (h : FamilyMember row F11B026L21) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B026L22_lift (row : List GridPoint) (h : FamilyMember row F11B026L22) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B026L23_lift (row : List GridPoint) (h : FamilyMember row F11B026L23) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B026L24_lift (row : List GridPoint) (h : FamilyMember row F11B026L24) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B026L25_lift (row : List GridPoint) (h : FamilyMember row F11B026L25) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B026L26_lift (row : List GridPoint) (h : FamilyMember row F11B026L26) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B026L27_lift (row : List GridPoint) (h : FamilyMember row F11B026L27) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B026L28_lift (row : List GridPoint) (h : FamilyMember row F11B026L28) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B026L29_lift (row : List GridPoint) (h : FamilyMember row F11B026L29) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B026L30_lift (row : List GridPoint) (h : FamilyMember row F11B026L30) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B026L31_lift (row : List GridPoint) (h : FamilyMember row F11B026L31) : FamilyMember row F11B026 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B026L32_lift (row : List GridPoint) (h : FamilyMember row F11B026L32) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B026L33_lift (row : List GridPoint) (h : FamilyMember row F11B026L33) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B026L34_lift (row : List GridPoint) (h : FamilyMember row F11B026L34) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B026L35_lift (row : List GridPoint) (h : FamilyMember row F11B026L35) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B026L36_lift (row : List GridPoint) (h : FamilyMember row F11B026L36) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B026L37_lift (row : List GridPoint) (h : FamilyMember row F11B026L37) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B026L38_lift (row : List GridPoint) (h : FamilyMember row F11B026L38) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B026L39_lift (row : List GridPoint) (h : FamilyMember row F11B026L39) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B026L40_lift (row : List GridPoint) (h : FamilyMember row F11B026L40) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B026L41_lift (row : List GridPoint) (h : FamilyMember row F11B026L41) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B026L42_lift (row : List GridPoint) (h : FamilyMember row F11B026L42) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B026L43_lift (row : List GridPoint) (h : FamilyMember row F11B026L43) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B026L44_lift (row : List GridPoint) (h : FamilyMember row F11B026L44) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B026L45_lift (row : List GridPoint) (h : FamilyMember row F11B026L45) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B026L46_lift (row : List GridPoint) (h : FamilyMember row F11B026L46) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B026L47_lift (row : List GridPoint) (h : FamilyMember row F11B026L47) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B026L48_lift (row : List GridPoint) (h : FamilyMember row F11B026L48) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B026L49_lift (row : List GridPoint) (h : FamilyMember row F11B026L49) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B026L50_lift (row : List GridPoint) (h : FamilyMember row F11B026L50) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B026L51_lift (row : List GridPoint) (h : FamilyMember row F11B026L51) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B026L52_lift (row : List GridPoint) (h : FamilyMember row F11B026L52) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B026L53_lift (row : List GridPoint) (h : FamilyMember row F11B026L53) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B026L54_lift (row : List GridPoint) (h : FamilyMember row F11B026L54) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B026L55_lift (row : List GridPoint) (h : FamilyMember row F11B026L55) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B026L56_lift (row : List GridPoint) (h : FamilyMember row F11B026L56) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B026L57_lift (row : List GridPoint) (h : FamilyMember row F11B026L57) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B026L58_lift (row : List GridPoint) (h : FamilyMember row F11B026L58) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B026L59_lift (row : List GridPoint) (h : FamilyMember row F11B026L59) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B026L60_lift (row : List GridPoint) (h : FamilyMember row F11B026L60) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B026L61_lift (row : List GridPoint) (h : FamilyMember row F11B026L61) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B026L62_lift (row : List GridPoint) (h : FamilyMember row F11B026L62) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B026L63_lift (row : List GridPoint) (h : FamilyMember row F11B026L63) : FamilyMember row F11B026 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
