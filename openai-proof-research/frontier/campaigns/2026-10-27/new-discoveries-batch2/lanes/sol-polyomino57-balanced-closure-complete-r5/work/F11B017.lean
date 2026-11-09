import TreeBlock017
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B017L0 : RowFamilyTree := TreeBlock017L0
abbrev F11B017L1 : RowFamilyTree := TreeBlock017L1
abbrev F11B017L2 : RowFamilyTree := TreeBlock017L2
abbrev F11B017L3 : RowFamilyTree := TreeBlock017L3
abbrev F11B017L4 : RowFamilyTree := TreeBlock017L4
abbrev F11B017L5 : RowFamilyTree := TreeBlock017L5
abbrev F11B017L6 : RowFamilyTree := TreeBlock017L6
abbrev F11B017L7 : RowFamilyTree := TreeBlock017L7
abbrev F11B017L8 : RowFamilyTree := TreeBlock017L8
abbrev F11B017L9 : RowFamilyTree := TreeBlock017L9
abbrev F11B017L10 : RowFamilyTree := TreeBlock017L10
abbrev F11B017L11 : RowFamilyTree := TreeBlock017L11
abbrev F11B017L12 : RowFamilyTree := TreeBlock017L12
abbrev F11B017L13 : RowFamilyTree := TreeBlock017L13
abbrev F11B017L14 : RowFamilyTree := TreeBlock017L14
abbrev F11B017L15 : RowFamilyTree := TreeBlock017L15
abbrev F11B017L16 : RowFamilyTree := TreeBlock017L16
abbrev F11B017L17 : RowFamilyTree := TreeBlock017L17
abbrev F11B017L18 : RowFamilyTree := TreeBlock017L18
abbrev F11B017L19 : RowFamilyTree := TreeBlock017L19
abbrev F11B017L20 : RowFamilyTree := TreeBlock017L20
abbrev F11B017L21 : RowFamilyTree := TreeBlock017L21
abbrev F11B017L22 : RowFamilyTree := TreeBlock017L22
abbrev F11B017L23 : RowFamilyTree := TreeBlock017L23
abbrev F11B017L24 : RowFamilyTree := TreeBlock017L24
abbrev F11B017L25 : RowFamilyTree := TreeBlock017L25
abbrev F11B017L26 : RowFamilyTree := TreeBlock017L26
abbrev F11B017L27 : RowFamilyTree := TreeBlock017L27
abbrev F11B017L28 : RowFamilyTree := TreeBlock017L28
abbrev F11B017L29 : RowFamilyTree := TreeBlock017L29
abbrev F11B017L30 : RowFamilyTree := TreeBlock017L30
abbrev F11B017L31 : RowFamilyTree := TreeBlock017L31
abbrev F11B017L32 : RowFamilyTree := TreeBlock017L32
abbrev F11B017L33 : RowFamilyTree := TreeBlock017L33
abbrev F11B017L34 : RowFamilyTree := TreeBlock017L34
abbrev F11B017L35 : RowFamilyTree := TreeBlock017L35
abbrev F11B017L36 : RowFamilyTree := TreeBlock017L36
abbrev F11B017L37 : RowFamilyTree := TreeBlock017L37
abbrev F11B017L38 : RowFamilyTree := TreeBlock017L38
abbrev F11B017L39 : RowFamilyTree := TreeBlock017L39
abbrev F11B017L40 : RowFamilyTree := TreeBlock017L40
abbrev F11B017L41 : RowFamilyTree := TreeBlock017L41
abbrev F11B017L42 : RowFamilyTree := TreeBlock017L42
abbrev F11B017L43 : RowFamilyTree := TreeBlock017L43
abbrev F11B017L44 : RowFamilyTree := TreeBlock017L44
abbrev F11B017L45 : RowFamilyTree := TreeBlock017L45
abbrev F11B017L46 : RowFamilyTree := TreeBlock017L46
abbrev F11B017L47 : RowFamilyTree := TreeBlock017L47
abbrev F11B017L48 : RowFamilyTree := TreeBlock017L48
abbrev F11B017L49 : RowFamilyTree := TreeBlock017L49
abbrev F11B017L50 : RowFamilyTree := TreeBlock017L50
abbrev F11B017L51 : RowFamilyTree := TreeBlock017L51
abbrev F11B017L52 : RowFamilyTree := TreeBlock017L52
abbrev F11B017L53 : RowFamilyTree := TreeBlock017L53
abbrev F11B017L54 : RowFamilyTree := TreeBlock017L54
abbrev F11B017L55 : RowFamilyTree := TreeBlock017L55
abbrev F11B017L56 : RowFamilyTree := TreeBlock017L56
abbrev F11B017L57 : RowFamilyTree := TreeBlock017L57
abbrev F11B017L58 : RowFamilyTree := TreeBlock017L58
abbrev F11B017L59 : RowFamilyTree := TreeBlock017L59
abbrev F11B017L60 : RowFamilyTree := TreeBlock017L60
abbrev F11B017L61 : RowFamilyTree := TreeBlock017L61
abbrev F11B017L62 : RowFamilyTree := TreeBlock017L62
abbrev F11B017L63 : RowFamilyTree := TreeBlock017L63
abbrev F11B017 : RowFamilyTree := TreeBlock017
theorem F11B017L0_lift (row : List GridPoint) (h : FamilyMember row F11B017L0) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B017L1_lift (row : List GridPoint) (h : FamilyMember row F11B017L1) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B017L2_lift (row : List GridPoint) (h : FamilyMember row F11B017L2) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B017L3_lift (row : List GridPoint) (h : FamilyMember row F11B017L3) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B017L4_lift (row : List GridPoint) (h : FamilyMember row F11B017L4) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B017L5_lift (row : List GridPoint) (h : FamilyMember row F11B017L5) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B017L6_lift (row : List GridPoint) (h : FamilyMember row F11B017L6) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B017L7_lift (row : List GridPoint) (h : FamilyMember row F11B017L7) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B017L8_lift (row : List GridPoint) (h : FamilyMember row F11B017L8) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B017L9_lift (row : List GridPoint) (h : FamilyMember row F11B017L9) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B017L10_lift (row : List GridPoint) (h : FamilyMember row F11B017L10) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B017L11_lift (row : List GridPoint) (h : FamilyMember row F11B017L11) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B017L12_lift (row : List GridPoint) (h : FamilyMember row F11B017L12) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B017L13_lift (row : List GridPoint) (h : FamilyMember row F11B017L13) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B017L14_lift (row : List GridPoint) (h : FamilyMember row F11B017L14) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B017L15_lift (row : List GridPoint) (h : FamilyMember row F11B017L15) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B017L16_lift (row : List GridPoint) (h : FamilyMember row F11B017L16) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B017L17_lift (row : List GridPoint) (h : FamilyMember row F11B017L17) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B017L18_lift (row : List GridPoint) (h : FamilyMember row F11B017L18) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B017L19_lift (row : List GridPoint) (h : FamilyMember row F11B017L19) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B017L20_lift (row : List GridPoint) (h : FamilyMember row F11B017L20) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B017L21_lift (row : List GridPoint) (h : FamilyMember row F11B017L21) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B017L22_lift (row : List GridPoint) (h : FamilyMember row F11B017L22) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B017L23_lift (row : List GridPoint) (h : FamilyMember row F11B017L23) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B017L24_lift (row : List GridPoint) (h : FamilyMember row F11B017L24) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B017L25_lift (row : List GridPoint) (h : FamilyMember row F11B017L25) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B017L26_lift (row : List GridPoint) (h : FamilyMember row F11B017L26) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B017L27_lift (row : List GridPoint) (h : FamilyMember row F11B017L27) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B017L28_lift (row : List GridPoint) (h : FamilyMember row F11B017L28) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B017L29_lift (row : List GridPoint) (h : FamilyMember row F11B017L29) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B017L30_lift (row : List GridPoint) (h : FamilyMember row F11B017L30) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B017L31_lift (row : List GridPoint) (h : FamilyMember row F11B017L31) : FamilyMember row F11B017 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B017L32_lift (row : List GridPoint) (h : FamilyMember row F11B017L32) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B017L33_lift (row : List GridPoint) (h : FamilyMember row F11B017L33) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B017L34_lift (row : List GridPoint) (h : FamilyMember row F11B017L34) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B017L35_lift (row : List GridPoint) (h : FamilyMember row F11B017L35) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B017L36_lift (row : List GridPoint) (h : FamilyMember row F11B017L36) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B017L37_lift (row : List GridPoint) (h : FamilyMember row F11B017L37) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B017L38_lift (row : List GridPoint) (h : FamilyMember row F11B017L38) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B017L39_lift (row : List GridPoint) (h : FamilyMember row F11B017L39) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B017L40_lift (row : List GridPoint) (h : FamilyMember row F11B017L40) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B017L41_lift (row : List GridPoint) (h : FamilyMember row F11B017L41) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B017L42_lift (row : List GridPoint) (h : FamilyMember row F11B017L42) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B017L43_lift (row : List GridPoint) (h : FamilyMember row F11B017L43) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B017L44_lift (row : List GridPoint) (h : FamilyMember row F11B017L44) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B017L45_lift (row : List GridPoint) (h : FamilyMember row F11B017L45) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B017L46_lift (row : List GridPoint) (h : FamilyMember row F11B017L46) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B017L47_lift (row : List GridPoint) (h : FamilyMember row F11B017L47) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B017L48_lift (row : List GridPoint) (h : FamilyMember row F11B017L48) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B017L49_lift (row : List GridPoint) (h : FamilyMember row F11B017L49) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B017L50_lift (row : List GridPoint) (h : FamilyMember row F11B017L50) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B017L51_lift (row : List GridPoint) (h : FamilyMember row F11B017L51) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B017L52_lift (row : List GridPoint) (h : FamilyMember row F11B017L52) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B017L53_lift (row : List GridPoint) (h : FamilyMember row F11B017L53) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B017L54_lift (row : List GridPoint) (h : FamilyMember row F11B017L54) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B017L55_lift (row : List GridPoint) (h : FamilyMember row F11B017L55) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B017L56_lift (row : List GridPoint) (h : FamilyMember row F11B017L56) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B017L57_lift (row : List GridPoint) (h : FamilyMember row F11B017L57) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B017L58_lift (row : List GridPoint) (h : FamilyMember row F11B017L58) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B017L59_lift (row : List GridPoint) (h : FamilyMember row F11B017L59) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B017L60_lift (row : List GridPoint) (h : FamilyMember row F11B017L60) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B017L61_lift (row : List GridPoint) (h : FamilyMember row F11B017L61) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B017L62_lift (row : List GridPoint) (h : FamilyMember row F11B017L62) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B017L63_lift (row : List GridPoint) (h : FamilyMember row F11B017L63) : FamilyMember row F11B017 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
