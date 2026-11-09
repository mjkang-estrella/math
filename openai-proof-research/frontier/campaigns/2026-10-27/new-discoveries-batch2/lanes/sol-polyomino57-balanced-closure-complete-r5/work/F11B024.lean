import TreeBlock024
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B024L0 : RowFamilyTree := TreeBlock024L0
abbrev F11B024L1 : RowFamilyTree := TreeBlock024L1
abbrev F11B024L2 : RowFamilyTree := TreeBlock024L2
abbrev F11B024L3 : RowFamilyTree := TreeBlock024L3
abbrev F11B024L4 : RowFamilyTree := TreeBlock024L4
abbrev F11B024L5 : RowFamilyTree := TreeBlock024L5
abbrev F11B024L6 : RowFamilyTree := TreeBlock024L6
abbrev F11B024L7 : RowFamilyTree := TreeBlock024L7
abbrev F11B024L8 : RowFamilyTree := TreeBlock024L8
abbrev F11B024L9 : RowFamilyTree := TreeBlock024L9
abbrev F11B024L10 : RowFamilyTree := TreeBlock024L10
abbrev F11B024L11 : RowFamilyTree := TreeBlock024L11
abbrev F11B024L12 : RowFamilyTree := TreeBlock024L12
abbrev F11B024L13 : RowFamilyTree := TreeBlock024L13
abbrev F11B024L14 : RowFamilyTree := TreeBlock024L14
abbrev F11B024L15 : RowFamilyTree := TreeBlock024L15
abbrev F11B024L16 : RowFamilyTree := TreeBlock024L16
abbrev F11B024L17 : RowFamilyTree := TreeBlock024L17
abbrev F11B024L18 : RowFamilyTree := TreeBlock024L18
abbrev F11B024L19 : RowFamilyTree := TreeBlock024L19
abbrev F11B024L20 : RowFamilyTree := TreeBlock024L20
abbrev F11B024L21 : RowFamilyTree := TreeBlock024L21
abbrev F11B024L22 : RowFamilyTree := TreeBlock024L22
abbrev F11B024L23 : RowFamilyTree := TreeBlock024L23
abbrev F11B024L24 : RowFamilyTree := TreeBlock024L24
abbrev F11B024L25 : RowFamilyTree := TreeBlock024L25
abbrev F11B024L26 : RowFamilyTree := TreeBlock024L26
abbrev F11B024L27 : RowFamilyTree := TreeBlock024L27
abbrev F11B024L28 : RowFamilyTree := TreeBlock024L28
abbrev F11B024L29 : RowFamilyTree := TreeBlock024L29
abbrev F11B024L30 : RowFamilyTree := TreeBlock024L30
abbrev F11B024L31 : RowFamilyTree := TreeBlock024L31
abbrev F11B024L32 : RowFamilyTree := TreeBlock024L32
abbrev F11B024L33 : RowFamilyTree := TreeBlock024L33
abbrev F11B024L34 : RowFamilyTree := TreeBlock024L34
abbrev F11B024L35 : RowFamilyTree := TreeBlock024L35
abbrev F11B024L36 : RowFamilyTree := TreeBlock024L36
abbrev F11B024L37 : RowFamilyTree := TreeBlock024L37
abbrev F11B024L38 : RowFamilyTree := TreeBlock024L38
abbrev F11B024L39 : RowFamilyTree := TreeBlock024L39
abbrev F11B024L40 : RowFamilyTree := TreeBlock024L40
abbrev F11B024L41 : RowFamilyTree := TreeBlock024L41
abbrev F11B024L42 : RowFamilyTree := TreeBlock024L42
abbrev F11B024L43 : RowFamilyTree := TreeBlock024L43
abbrev F11B024L44 : RowFamilyTree := TreeBlock024L44
abbrev F11B024L45 : RowFamilyTree := TreeBlock024L45
abbrev F11B024L46 : RowFamilyTree := TreeBlock024L46
abbrev F11B024L47 : RowFamilyTree := TreeBlock024L47
abbrev F11B024L48 : RowFamilyTree := TreeBlock024L48
abbrev F11B024L49 : RowFamilyTree := TreeBlock024L49
abbrev F11B024L50 : RowFamilyTree := TreeBlock024L50
abbrev F11B024L51 : RowFamilyTree := TreeBlock024L51
abbrev F11B024L52 : RowFamilyTree := TreeBlock024L52
abbrev F11B024L53 : RowFamilyTree := TreeBlock024L53
abbrev F11B024L54 : RowFamilyTree := TreeBlock024L54
abbrev F11B024L55 : RowFamilyTree := TreeBlock024L55
abbrev F11B024L56 : RowFamilyTree := TreeBlock024L56
abbrev F11B024L57 : RowFamilyTree := TreeBlock024L57
abbrev F11B024L58 : RowFamilyTree := TreeBlock024L58
abbrev F11B024L59 : RowFamilyTree := TreeBlock024L59
abbrev F11B024L60 : RowFamilyTree := TreeBlock024L60
abbrev F11B024L61 : RowFamilyTree := TreeBlock024L61
abbrev F11B024L62 : RowFamilyTree := TreeBlock024L62
abbrev F11B024L63 : RowFamilyTree := TreeBlock024L63
abbrev F11B024 : RowFamilyTree := TreeBlock024
theorem F11B024L0_lift (row : List GridPoint) (h : FamilyMember row F11B024L0) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B024L1_lift (row : List GridPoint) (h : FamilyMember row F11B024L1) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B024L2_lift (row : List GridPoint) (h : FamilyMember row F11B024L2) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B024L3_lift (row : List GridPoint) (h : FamilyMember row F11B024L3) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B024L4_lift (row : List GridPoint) (h : FamilyMember row F11B024L4) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B024L5_lift (row : List GridPoint) (h : FamilyMember row F11B024L5) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B024L6_lift (row : List GridPoint) (h : FamilyMember row F11B024L6) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B024L7_lift (row : List GridPoint) (h : FamilyMember row F11B024L7) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B024L8_lift (row : List GridPoint) (h : FamilyMember row F11B024L8) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B024L9_lift (row : List GridPoint) (h : FamilyMember row F11B024L9) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B024L10_lift (row : List GridPoint) (h : FamilyMember row F11B024L10) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B024L11_lift (row : List GridPoint) (h : FamilyMember row F11B024L11) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B024L12_lift (row : List GridPoint) (h : FamilyMember row F11B024L12) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B024L13_lift (row : List GridPoint) (h : FamilyMember row F11B024L13) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B024L14_lift (row : List GridPoint) (h : FamilyMember row F11B024L14) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B024L15_lift (row : List GridPoint) (h : FamilyMember row F11B024L15) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B024L16_lift (row : List GridPoint) (h : FamilyMember row F11B024L16) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B024L17_lift (row : List GridPoint) (h : FamilyMember row F11B024L17) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B024L18_lift (row : List GridPoint) (h : FamilyMember row F11B024L18) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B024L19_lift (row : List GridPoint) (h : FamilyMember row F11B024L19) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B024L20_lift (row : List GridPoint) (h : FamilyMember row F11B024L20) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B024L21_lift (row : List GridPoint) (h : FamilyMember row F11B024L21) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B024L22_lift (row : List GridPoint) (h : FamilyMember row F11B024L22) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B024L23_lift (row : List GridPoint) (h : FamilyMember row F11B024L23) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B024L24_lift (row : List GridPoint) (h : FamilyMember row F11B024L24) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B024L25_lift (row : List GridPoint) (h : FamilyMember row F11B024L25) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B024L26_lift (row : List GridPoint) (h : FamilyMember row F11B024L26) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B024L27_lift (row : List GridPoint) (h : FamilyMember row F11B024L27) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B024L28_lift (row : List GridPoint) (h : FamilyMember row F11B024L28) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B024L29_lift (row : List GridPoint) (h : FamilyMember row F11B024L29) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B024L30_lift (row : List GridPoint) (h : FamilyMember row F11B024L30) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B024L31_lift (row : List GridPoint) (h : FamilyMember row F11B024L31) : FamilyMember row F11B024 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B024L32_lift (row : List GridPoint) (h : FamilyMember row F11B024L32) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B024L33_lift (row : List GridPoint) (h : FamilyMember row F11B024L33) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B024L34_lift (row : List GridPoint) (h : FamilyMember row F11B024L34) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B024L35_lift (row : List GridPoint) (h : FamilyMember row F11B024L35) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B024L36_lift (row : List GridPoint) (h : FamilyMember row F11B024L36) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B024L37_lift (row : List GridPoint) (h : FamilyMember row F11B024L37) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B024L38_lift (row : List GridPoint) (h : FamilyMember row F11B024L38) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B024L39_lift (row : List GridPoint) (h : FamilyMember row F11B024L39) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B024L40_lift (row : List GridPoint) (h : FamilyMember row F11B024L40) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B024L41_lift (row : List GridPoint) (h : FamilyMember row F11B024L41) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B024L42_lift (row : List GridPoint) (h : FamilyMember row F11B024L42) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B024L43_lift (row : List GridPoint) (h : FamilyMember row F11B024L43) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B024L44_lift (row : List GridPoint) (h : FamilyMember row F11B024L44) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B024L45_lift (row : List GridPoint) (h : FamilyMember row F11B024L45) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B024L46_lift (row : List GridPoint) (h : FamilyMember row F11B024L46) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B024L47_lift (row : List GridPoint) (h : FamilyMember row F11B024L47) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B024L48_lift (row : List GridPoint) (h : FamilyMember row F11B024L48) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B024L49_lift (row : List GridPoint) (h : FamilyMember row F11B024L49) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B024L50_lift (row : List GridPoint) (h : FamilyMember row F11B024L50) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B024L51_lift (row : List GridPoint) (h : FamilyMember row F11B024L51) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B024L52_lift (row : List GridPoint) (h : FamilyMember row F11B024L52) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B024L53_lift (row : List GridPoint) (h : FamilyMember row F11B024L53) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B024L54_lift (row : List GridPoint) (h : FamilyMember row F11B024L54) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B024L55_lift (row : List GridPoint) (h : FamilyMember row F11B024L55) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B024L56_lift (row : List GridPoint) (h : FamilyMember row F11B024L56) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B024L57_lift (row : List GridPoint) (h : FamilyMember row F11B024L57) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B024L58_lift (row : List GridPoint) (h : FamilyMember row F11B024L58) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B024L59_lift (row : List GridPoint) (h : FamilyMember row F11B024L59) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B024L60_lift (row : List GridPoint) (h : FamilyMember row F11B024L60) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B024L61_lift (row : List GridPoint) (h : FamilyMember row F11B024L61) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B024L62_lift (row : List GridPoint) (h : FamilyMember row F11B024L62) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B024L63_lift (row : List GridPoint) (h : FamilyMember row F11B024L63) : FamilyMember row F11B024 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
