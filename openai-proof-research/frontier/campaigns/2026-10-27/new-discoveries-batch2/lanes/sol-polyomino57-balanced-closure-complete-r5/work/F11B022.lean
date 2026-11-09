import TreeBlock022
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B022L0 : RowFamilyTree := TreeBlock022L0
abbrev F11B022L1 : RowFamilyTree := TreeBlock022L1
abbrev F11B022L2 : RowFamilyTree := TreeBlock022L2
abbrev F11B022L3 : RowFamilyTree := TreeBlock022L3
abbrev F11B022L4 : RowFamilyTree := TreeBlock022L4
abbrev F11B022L5 : RowFamilyTree := TreeBlock022L5
abbrev F11B022L6 : RowFamilyTree := TreeBlock022L6
abbrev F11B022L7 : RowFamilyTree := TreeBlock022L7
abbrev F11B022L8 : RowFamilyTree := TreeBlock022L8
abbrev F11B022L9 : RowFamilyTree := TreeBlock022L9
abbrev F11B022L10 : RowFamilyTree := TreeBlock022L10
abbrev F11B022L11 : RowFamilyTree := TreeBlock022L11
abbrev F11B022L12 : RowFamilyTree := TreeBlock022L12
abbrev F11B022L13 : RowFamilyTree := TreeBlock022L13
abbrev F11B022L14 : RowFamilyTree := TreeBlock022L14
abbrev F11B022L15 : RowFamilyTree := TreeBlock022L15
abbrev F11B022L16 : RowFamilyTree := TreeBlock022L16
abbrev F11B022L17 : RowFamilyTree := TreeBlock022L17
abbrev F11B022L18 : RowFamilyTree := TreeBlock022L18
abbrev F11B022L19 : RowFamilyTree := TreeBlock022L19
abbrev F11B022L20 : RowFamilyTree := TreeBlock022L20
abbrev F11B022L21 : RowFamilyTree := TreeBlock022L21
abbrev F11B022L22 : RowFamilyTree := TreeBlock022L22
abbrev F11B022L23 : RowFamilyTree := TreeBlock022L23
abbrev F11B022L24 : RowFamilyTree := TreeBlock022L24
abbrev F11B022L25 : RowFamilyTree := TreeBlock022L25
abbrev F11B022L26 : RowFamilyTree := TreeBlock022L26
abbrev F11B022L27 : RowFamilyTree := TreeBlock022L27
abbrev F11B022L28 : RowFamilyTree := TreeBlock022L28
abbrev F11B022L29 : RowFamilyTree := TreeBlock022L29
abbrev F11B022L30 : RowFamilyTree := TreeBlock022L30
abbrev F11B022L31 : RowFamilyTree := TreeBlock022L31
abbrev F11B022L32 : RowFamilyTree := TreeBlock022L32
abbrev F11B022L33 : RowFamilyTree := TreeBlock022L33
abbrev F11B022L34 : RowFamilyTree := TreeBlock022L34
abbrev F11B022L35 : RowFamilyTree := TreeBlock022L35
abbrev F11B022L36 : RowFamilyTree := TreeBlock022L36
abbrev F11B022L37 : RowFamilyTree := TreeBlock022L37
abbrev F11B022L38 : RowFamilyTree := TreeBlock022L38
abbrev F11B022L39 : RowFamilyTree := TreeBlock022L39
abbrev F11B022L40 : RowFamilyTree := TreeBlock022L40
abbrev F11B022L41 : RowFamilyTree := TreeBlock022L41
abbrev F11B022L42 : RowFamilyTree := TreeBlock022L42
abbrev F11B022L43 : RowFamilyTree := TreeBlock022L43
abbrev F11B022L44 : RowFamilyTree := TreeBlock022L44
abbrev F11B022L45 : RowFamilyTree := TreeBlock022L45
abbrev F11B022L46 : RowFamilyTree := TreeBlock022L46
abbrev F11B022L47 : RowFamilyTree := TreeBlock022L47
abbrev F11B022L48 : RowFamilyTree := TreeBlock022L48
abbrev F11B022L49 : RowFamilyTree := TreeBlock022L49
abbrev F11B022L50 : RowFamilyTree := TreeBlock022L50
abbrev F11B022L51 : RowFamilyTree := TreeBlock022L51
abbrev F11B022L52 : RowFamilyTree := TreeBlock022L52
abbrev F11B022L53 : RowFamilyTree := TreeBlock022L53
abbrev F11B022L54 : RowFamilyTree := TreeBlock022L54
abbrev F11B022L55 : RowFamilyTree := TreeBlock022L55
abbrev F11B022L56 : RowFamilyTree := TreeBlock022L56
abbrev F11B022L57 : RowFamilyTree := TreeBlock022L57
abbrev F11B022L58 : RowFamilyTree := TreeBlock022L58
abbrev F11B022L59 : RowFamilyTree := TreeBlock022L59
abbrev F11B022L60 : RowFamilyTree := TreeBlock022L60
abbrev F11B022L61 : RowFamilyTree := TreeBlock022L61
abbrev F11B022L62 : RowFamilyTree := TreeBlock022L62
abbrev F11B022L63 : RowFamilyTree := TreeBlock022L63
abbrev F11B022 : RowFamilyTree := TreeBlock022
theorem F11B022L0_lift (row : List GridPoint) (h : FamilyMember row F11B022L0) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B022L1_lift (row : List GridPoint) (h : FamilyMember row F11B022L1) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B022L2_lift (row : List GridPoint) (h : FamilyMember row F11B022L2) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B022L3_lift (row : List GridPoint) (h : FamilyMember row F11B022L3) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B022L4_lift (row : List GridPoint) (h : FamilyMember row F11B022L4) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B022L5_lift (row : List GridPoint) (h : FamilyMember row F11B022L5) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B022L6_lift (row : List GridPoint) (h : FamilyMember row F11B022L6) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B022L7_lift (row : List GridPoint) (h : FamilyMember row F11B022L7) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B022L8_lift (row : List GridPoint) (h : FamilyMember row F11B022L8) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B022L9_lift (row : List GridPoint) (h : FamilyMember row F11B022L9) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B022L10_lift (row : List GridPoint) (h : FamilyMember row F11B022L10) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B022L11_lift (row : List GridPoint) (h : FamilyMember row F11B022L11) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B022L12_lift (row : List GridPoint) (h : FamilyMember row F11B022L12) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B022L13_lift (row : List GridPoint) (h : FamilyMember row F11B022L13) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B022L14_lift (row : List GridPoint) (h : FamilyMember row F11B022L14) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B022L15_lift (row : List GridPoint) (h : FamilyMember row F11B022L15) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B022L16_lift (row : List GridPoint) (h : FamilyMember row F11B022L16) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B022L17_lift (row : List GridPoint) (h : FamilyMember row F11B022L17) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B022L18_lift (row : List GridPoint) (h : FamilyMember row F11B022L18) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B022L19_lift (row : List GridPoint) (h : FamilyMember row F11B022L19) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B022L20_lift (row : List GridPoint) (h : FamilyMember row F11B022L20) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B022L21_lift (row : List GridPoint) (h : FamilyMember row F11B022L21) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B022L22_lift (row : List GridPoint) (h : FamilyMember row F11B022L22) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B022L23_lift (row : List GridPoint) (h : FamilyMember row F11B022L23) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B022L24_lift (row : List GridPoint) (h : FamilyMember row F11B022L24) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B022L25_lift (row : List GridPoint) (h : FamilyMember row F11B022L25) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B022L26_lift (row : List GridPoint) (h : FamilyMember row F11B022L26) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B022L27_lift (row : List GridPoint) (h : FamilyMember row F11B022L27) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B022L28_lift (row : List GridPoint) (h : FamilyMember row F11B022L28) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B022L29_lift (row : List GridPoint) (h : FamilyMember row F11B022L29) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B022L30_lift (row : List GridPoint) (h : FamilyMember row F11B022L30) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B022L31_lift (row : List GridPoint) (h : FamilyMember row F11B022L31) : FamilyMember row F11B022 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B022L32_lift (row : List GridPoint) (h : FamilyMember row F11B022L32) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B022L33_lift (row : List GridPoint) (h : FamilyMember row F11B022L33) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B022L34_lift (row : List GridPoint) (h : FamilyMember row F11B022L34) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B022L35_lift (row : List GridPoint) (h : FamilyMember row F11B022L35) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B022L36_lift (row : List GridPoint) (h : FamilyMember row F11B022L36) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B022L37_lift (row : List GridPoint) (h : FamilyMember row F11B022L37) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B022L38_lift (row : List GridPoint) (h : FamilyMember row F11B022L38) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B022L39_lift (row : List GridPoint) (h : FamilyMember row F11B022L39) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B022L40_lift (row : List GridPoint) (h : FamilyMember row F11B022L40) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B022L41_lift (row : List GridPoint) (h : FamilyMember row F11B022L41) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B022L42_lift (row : List GridPoint) (h : FamilyMember row F11B022L42) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B022L43_lift (row : List GridPoint) (h : FamilyMember row F11B022L43) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B022L44_lift (row : List GridPoint) (h : FamilyMember row F11B022L44) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B022L45_lift (row : List GridPoint) (h : FamilyMember row F11B022L45) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B022L46_lift (row : List GridPoint) (h : FamilyMember row F11B022L46) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B022L47_lift (row : List GridPoint) (h : FamilyMember row F11B022L47) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B022L48_lift (row : List GridPoint) (h : FamilyMember row F11B022L48) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B022L49_lift (row : List GridPoint) (h : FamilyMember row F11B022L49) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B022L50_lift (row : List GridPoint) (h : FamilyMember row F11B022L50) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B022L51_lift (row : List GridPoint) (h : FamilyMember row F11B022L51) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B022L52_lift (row : List GridPoint) (h : FamilyMember row F11B022L52) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B022L53_lift (row : List GridPoint) (h : FamilyMember row F11B022L53) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B022L54_lift (row : List GridPoint) (h : FamilyMember row F11B022L54) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B022L55_lift (row : List GridPoint) (h : FamilyMember row F11B022L55) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B022L56_lift (row : List GridPoint) (h : FamilyMember row F11B022L56) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B022L57_lift (row : List GridPoint) (h : FamilyMember row F11B022L57) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B022L58_lift (row : List GridPoint) (h : FamilyMember row F11B022L58) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B022L59_lift (row : List GridPoint) (h : FamilyMember row F11B022L59) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B022L60_lift (row : List GridPoint) (h : FamilyMember row F11B022L60) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B022L61_lift (row : List GridPoint) (h : FamilyMember row F11B022L61) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B022L62_lift (row : List GridPoint) (h : FamilyMember row F11B022L62) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B022L63_lift (row : List GridPoint) (h : FamilyMember row F11B022L63) : FamilyMember row F11B022 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
