import TreeBlock004
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B004L0 : RowFamilyTree := TreeBlock004L0
abbrev F11B004L1 : RowFamilyTree := TreeBlock004L1
abbrev F11B004L2 : RowFamilyTree := TreeBlock004L2
abbrev F11B004L3 : RowFamilyTree := TreeBlock004L3
abbrev F11B004L4 : RowFamilyTree := TreeBlock004L4
abbrev F11B004L5 : RowFamilyTree := TreeBlock004L5
abbrev F11B004L6 : RowFamilyTree := TreeBlock004L6
abbrev F11B004L7 : RowFamilyTree := TreeBlock004L7
abbrev F11B004L8 : RowFamilyTree := TreeBlock004L8
abbrev F11B004L9 : RowFamilyTree := TreeBlock004L9
abbrev F11B004L10 : RowFamilyTree := TreeBlock004L10
abbrev F11B004L11 : RowFamilyTree := TreeBlock004L11
abbrev F11B004L12 : RowFamilyTree := TreeBlock004L12
abbrev F11B004L13 : RowFamilyTree := TreeBlock004L13
abbrev F11B004L14 : RowFamilyTree := TreeBlock004L14
abbrev F11B004L15 : RowFamilyTree := TreeBlock004L15
abbrev F11B004L16 : RowFamilyTree := TreeBlock004L16
abbrev F11B004L17 : RowFamilyTree := TreeBlock004L17
abbrev F11B004L18 : RowFamilyTree := TreeBlock004L18
abbrev F11B004L19 : RowFamilyTree := TreeBlock004L19
abbrev F11B004L20 : RowFamilyTree := TreeBlock004L20
abbrev F11B004L21 : RowFamilyTree := TreeBlock004L21
abbrev F11B004L22 : RowFamilyTree := TreeBlock004L22
abbrev F11B004L23 : RowFamilyTree := TreeBlock004L23
abbrev F11B004L24 : RowFamilyTree := TreeBlock004L24
abbrev F11B004L25 : RowFamilyTree := TreeBlock004L25
abbrev F11B004L26 : RowFamilyTree := TreeBlock004L26
abbrev F11B004L27 : RowFamilyTree := TreeBlock004L27
abbrev F11B004L28 : RowFamilyTree := TreeBlock004L28
abbrev F11B004L29 : RowFamilyTree := TreeBlock004L29
abbrev F11B004L30 : RowFamilyTree := TreeBlock004L30
abbrev F11B004L31 : RowFamilyTree := TreeBlock004L31
abbrev F11B004L32 : RowFamilyTree := TreeBlock004L32
abbrev F11B004L33 : RowFamilyTree := TreeBlock004L33
abbrev F11B004L34 : RowFamilyTree := TreeBlock004L34
abbrev F11B004L35 : RowFamilyTree := TreeBlock004L35
abbrev F11B004L36 : RowFamilyTree := TreeBlock004L36
abbrev F11B004L37 : RowFamilyTree := TreeBlock004L37
abbrev F11B004L38 : RowFamilyTree := TreeBlock004L38
abbrev F11B004L39 : RowFamilyTree := TreeBlock004L39
abbrev F11B004L40 : RowFamilyTree := TreeBlock004L40
abbrev F11B004L41 : RowFamilyTree := TreeBlock004L41
abbrev F11B004L42 : RowFamilyTree := TreeBlock004L42
abbrev F11B004L43 : RowFamilyTree := TreeBlock004L43
abbrev F11B004L44 : RowFamilyTree := TreeBlock004L44
abbrev F11B004L45 : RowFamilyTree := TreeBlock004L45
abbrev F11B004L46 : RowFamilyTree := TreeBlock004L46
abbrev F11B004L47 : RowFamilyTree := TreeBlock004L47
abbrev F11B004L48 : RowFamilyTree := TreeBlock004L48
abbrev F11B004L49 : RowFamilyTree := TreeBlock004L49
abbrev F11B004L50 : RowFamilyTree := TreeBlock004L50
abbrev F11B004L51 : RowFamilyTree := TreeBlock004L51
abbrev F11B004L52 : RowFamilyTree := TreeBlock004L52
abbrev F11B004L53 : RowFamilyTree := TreeBlock004L53
abbrev F11B004L54 : RowFamilyTree := TreeBlock004L54
abbrev F11B004L55 : RowFamilyTree := TreeBlock004L55
abbrev F11B004L56 : RowFamilyTree := TreeBlock004L56
abbrev F11B004L57 : RowFamilyTree := TreeBlock004L57
abbrev F11B004L58 : RowFamilyTree := TreeBlock004L58
abbrev F11B004L59 : RowFamilyTree := TreeBlock004L59
abbrev F11B004L60 : RowFamilyTree := TreeBlock004L60
abbrev F11B004L61 : RowFamilyTree := TreeBlock004L61
abbrev F11B004L62 : RowFamilyTree := TreeBlock004L62
abbrev F11B004L63 : RowFamilyTree := TreeBlock004L63
abbrev F11B004 : RowFamilyTree := TreeBlock004
theorem F11B004L0_lift (row : List GridPoint) (h : FamilyMember row F11B004L0) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B004L1_lift (row : List GridPoint) (h : FamilyMember row F11B004L1) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B004L2_lift (row : List GridPoint) (h : FamilyMember row F11B004L2) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B004L3_lift (row : List GridPoint) (h : FamilyMember row F11B004L3) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B004L4_lift (row : List GridPoint) (h : FamilyMember row F11B004L4) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B004L5_lift (row : List GridPoint) (h : FamilyMember row F11B004L5) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B004L6_lift (row : List GridPoint) (h : FamilyMember row F11B004L6) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B004L7_lift (row : List GridPoint) (h : FamilyMember row F11B004L7) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B004L8_lift (row : List GridPoint) (h : FamilyMember row F11B004L8) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B004L9_lift (row : List GridPoint) (h : FamilyMember row F11B004L9) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B004L10_lift (row : List GridPoint) (h : FamilyMember row F11B004L10) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B004L11_lift (row : List GridPoint) (h : FamilyMember row F11B004L11) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B004L12_lift (row : List GridPoint) (h : FamilyMember row F11B004L12) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B004L13_lift (row : List GridPoint) (h : FamilyMember row F11B004L13) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B004L14_lift (row : List GridPoint) (h : FamilyMember row F11B004L14) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B004L15_lift (row : List GridPoint) (h : FamilyMember row F11B004L15) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B004L16_lift (row : List GridPoint) (h : FamilyMember row F11B004L16) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B004L17_lift (row : List GridPoint) (h : FamilyMember row F11B004L17) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B004L18_lift (row : List GridPoint) (h : FamilyMember row F11B004L18) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B004L19_lift (row : List GridPoint) (h : FamilyMember row F11B004L19) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B004L20_lift (row : List GridPoint) (h : FamilyMember row F11B004L20) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B004L21_lift (row : List GridPoint) (h : FamilyMember row F11B004L21) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B004L22_lift (row : List GridPoint) (h : FamilyMember row F11B004L22) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B004L23_lift (row : List GridPoint) (h : FamilyMember row F11B004L23) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B004L24_lift (row : List GridPoint) (h : FamilyMember row F11B004L24) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B004L25_lift (row : List GridPoint) (h : FamilyMember row F11B004L25) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B004L26_lift (row : List GridPoint) (h : FamilyMember row F11B004L26) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B004L27_lift (row : List GridPoint) (h : FamilyMember row F11B004L27) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B004L28_lift (row : List GridPoint) (h : FamilyMember row F11B004L28) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B004L29_lift (row : List GridPoint) (h : FamilyMember row F11B004L29) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B004L30_lift (row : List GridPoint) (h : FamilyMember row F11B004L30) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B004L31_lift (row : List GridPoint) (h : FamilyMember row F11B004L31) : FamilyMember row F11B004 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B004L32_lift (row : List GridPoint) (h : FamilyMember row F11B004L32) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B004L33_lift (row : List GridPoint) (h : FamilyMember row F11B004L33) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B004L34_lift (row : List GridPoint) (h : FamilyMember row F11B004L34) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B004L35_lift (row : List GridPoint) (h : FamilyMember row F11B004L35) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B004L36_lift (row : List GridPoint) (h : FamilyMember row F11B004L36) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B004L37_lift (row : List GridPoint) (h : FamilyMember row F11B004L37) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B004L38_lift (row : List GridPoint) (h : FamilyMember row F11B004L38) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B004L39_lift (row : List GridPoint) (h : FamilyMember row F11B004L39) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B004L40_lift (row : List GridPoint) (h : FamilyMember row F11B004L40) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B004L41_lift (row : List GridPoint) (h : FamilyMember row F11B004L41) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B004L42_lift (row : List GridPoint) (h : FamilyMember row F11B004L42) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B004L43_lift (row : List GridPoint) (h : FamilyMember row F11B004L43) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B004L44_lift (row : List GridPoint) (h : FamilyMember row F11B004L44) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B004L45_lift (row : List GridPoint) (h : FamilyMember row F11B004L45) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B004L46_lift (row : List GridPoint) (h : FamilyMember row F11B004L46) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B004L47_lift (row : List GridPoint) (h : FamilyMember row F11B004L47) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B004L48_lift (row : List GridPoint) (h : FamilyMember row F11B004L48) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B004L49_lift (row : List GridPoint) (h : FamilyMember row F11B004L49) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B004L50_lift (row : List GridPoint) (h : FamilyMember row F11B004L50) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B004L51_lift (row : List GridPoint) (h : FamilyMember row F11B004L51) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B004L52_lift (row : List GridPoint) (h : FamilyMember row F11B004L52) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B004L53_lift (row : List GridPoint) (h : FamilyMember row F11B004L53) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B004L54_lift (row : List GridPoint) (h : FamilyMember row F11B004L54) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B004L55_lift (row : List GridPoint) (h : FamilyMember row F11B004L55) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B004L56_lift (row : List GridPoint) (h : FamilyMember row F11B004L56) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B004L57_lift (row : List GridPoint) (h : FamilyMember row F11B004L57) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B004L58_lift (row : List GridPoint) (h : FamilyMember row F11B004L58) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B004L59_lift (row : List GridPoint) (h : FamilyMember row F11B004L59) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B004L60_lift (row : List GridPoint) (h : FamilyMember row F11B004L60) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B004L61_lift (row : List GridPoint) (h : FamilyMember row F11B004L61) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B004L62_lift (row : List GridPoint) (h : FamilyMember row F11B004L62) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B004L63_lift (row : List GridPoint) (h : FamilyMember row F11B004L63) : FamilyMember row F11B004 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
