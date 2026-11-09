import TreeBlock028
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B028L0 : RowFamilyTree := TreeBlock028L0
abbrev F11B028L1 : RowFamilyTree := TreeBlock028L1
abbrev F11B028L2 : RowFamilyTree := TreeBlock028L2
abbrev F11B028L3 : RowFamilyTree := TreeBlock028L3
abbrev F11B028L4 : RowFamilyTree := TreeBlock028L4
abbrev F11B028L5 : RowFamilyTree := TreeBlock028L5
abbrev F11B028L6 : RowFamilyTree := TreeBlock028L6
abbrev F11B028L7 : RowFamilyTree := TreeBlock028L7
abbrev F11B028L8 : RowFamilyTree := TreeBlock028L8
abbrev F11B028L9 : RowFamilyTree := TreeBlock028L9
abbrev F11B028L10 : RowFamilyTree := TreeBlock028L10
abbrev F11B028L11 : RowFamilyTree := TreeBlock028L11
abbrev F11B028L12 : RowFamilyTree := TreeBlock028L12
abbrev F11B028L13 : RowFamilyTree := TreeBlock028L13
abbrev F11B028L14 : RowFamilyTree := TreeBlock028L14
abbrev F11B028L15 : RowFamilyTree := TreeBlock028L15
abbrev F11B028L16 : RowFamilyTree := TreeBlock028L16
abbrev F11B028L17 : RowFamilyTree := TreeBlock028L17
abbrev F11B028L18 : RowFamilyTree := TreeBlock028L18
abbrev F11B028L19 : RowFamilyTree := TreeBlock028L19
abbrev F11B028L20 : RowFamilyTree := TreeBlock028L20
abbrev F11B028L21 : RowFamilyTree := TreeBlock028L21
abbrev F11B028L22 : RowFamilyTree := TreeBlock028L22
abbrev F11B028L23 : RowFamilyTree := TreeBlock028L23
abbrev F11B028L24 : RowFamilyTree := TreeBlock028L24
abbrev F11B028L25 : RowFamilyTree := TreeBlock028L25
abbrev F11B028L26 : RowFamilyTree := TreeBlock028L26
abbrev F11B028L27 : RowFamilyTree := TreeBlock028L27
abbrev F11B028L28 : RowFamilyTree := TreeBlock028L28
abbrev F11B028L29 : RowFamilyTree := TreeBlock028L29
abbrev F11B028L30 : RowFamilyTree := TreeBlock028L30
abbrev F11B028L31 : RowFamilyTree := TreeBlock028L31
abbrev F11B028L32 : RowFamilyTree := TreeBlock028L32
abbrev F11B028L33 : RowFamilyTree := TreeBlock028L33
abbrev F11B028L34 : RowFamilyTree := TreeBlock028L34
abbrev F11B028L35 : RowFamilyTree := TreeBlock028L35
abbrev F11B028L36 : RowFamilyTree := TreeBlock028L36
abbrev F11B028L37 : RowFamilyTree := TreeBlock028L37
abbrev F11B028L38 : RowFamilyTree := TreeBlock028L38
abbrev F11B028L39 : RowFamilyTree := TreeBlock028L39
abbrev F11B028L40 : RowFamilyTree := TreeBlock028L40
abbrev F11B028L41 : RowFamilyTree := TreeBlock028L41
abbrev F11B028L42 : RowFamilyTree := TreeBlock028L42
abbrev F11B028L43 : RowFamilyTree := TreeBlock028L43
abbrev F11B028L44 : RowFamilyTree := TreeBlock028L44
abbrev F11B028L45 : RowFamilyTree := TreeBlock028L45
abbrev F11B028L46 : RowFamilyTree := TreeBlock028L46
abbrev F11B028L47 : RowFamilyTree := TreeBlock028L47
abbrev F11B028L48 : RowFamilyTree := TreeBlock028L48
abbrev F11B028L49 : RowFamilyTree := TreeBlock028L49
abbrev F11B028L50 : RowFamilyTree := TreeBlock028L50
abbrev F11B028L51 : RowFamilyTree := TreeBlock028L51
abbrev F11B028L52 : RowFamilyTree := TreeBlock028L52
abbrev F11B028L53 : RowFamilyTree := TreeBlock028L53
abbrev F11B028L54 : RowFamilyTree := TreeBlock028L54
abbrev F11B028L55 : RowFamilyTree := TreeBlock028L55
abbrev F11B028L56 : RowFamilyTree := TreeBlock028L56
abbrev F11B028L57 : RowFamilyTree := TreeBlock028L57
abbrev F11B028L58 : RowFamilyTree := TreeBlock028L58
abbrev F11B028L59 : RowFamilyTree := TreeBlock028L59
abbrev F11B028L60 : RowFamilyTree := TreeBlock028L60
abbrev F11B028L61 : RowFamilyTree := TreeBlock028L61
abbrev F11B028L62 : RowFamilyTree := TreeBlock028L62
abbrev F11B028L63 : RowFamilyTree := TreeBlock028L63
abbrev F11B028 : RowFamilyTree := TreeBlock028
theorem F11B028L0_lift (row : List GridPoint) (h : FamilyMember row F11B028L0) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B028L1_lift (row : List GridPoint) (h : FamilyMember row F11B028L1) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B028L2_lift (row : List GridPoint) (h : FamilyMember row F11B028L2) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B028L3_lift (row : List GridPoint) (h : FamilyMember row F11B028L3) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B028L4_lift (row : List GridPoint) (h : FamilyMember row F11B028L4) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B028L5_lift (row : List GridPoint) (h : FamilyMember row F11B028L5) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B028L6_lift (row : List GridPoint) (h : FamilyMember row F11B028L6) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B028L7_lift (row : List GridPoint) (h : FamilyMember row F11B028L7) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B028L8_lift (row : List GridPoint) (h : FamilyMember row F11B028L8) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B028L9_lift (row : List GridPoint) (h : FamilyMember row F11B028L9) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B028L10_lift (row : List GridPoint) (h : FamilyMember row F11B028L10) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B028L11_lift (row : List GridPoint) (h : FamilyMember row F11B028L11) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B028L12_lift (row : List GridPoint) (h : FamilyMember row F11B028L12) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B028L13_lift (row : List GridPoint) (h : FamilyMember row F11B028L13) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B028L14_lift (row : List GridPoint) (h : FamilyMember row F11B028L14) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B028L15_lift (row : List GridPoint) (h : FamilyMember row F11B028L15) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B028L16_lift (row : List GridPoint) (h : FamilyMember row F11B028L16) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B028L17_lift (row : List GridPoint) (h : FamilyMember row F11B028L17) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B028L18_lift (row : List GridPoint) (h : FamilyMember row F11B028L18) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B028L19_lift (row : List GridPoint) (h : FamilyMember row F11B028L19) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B028L20_lift (row : List GridPoint) (h : FamilyMember row F11B028L20) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B028L21_lift (row : List GridPoint) (h : FamilyMember row F11B028L21) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B028L22_lift (row : List GridPoint) (h : FamilyMember row F11B028L22) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B028L23_lift (row : List GridPoint) (h : FamilyMember row F11B028L23) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B028L24_lift (row : List GridPoint) (h : FamilyMember row F11B028L24) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B028L25_lift (row : List GridPoint) (h : FamilyMember row F11B028L25) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B028L26_lift (row : List GridPoint) (h : FamilyMember row F11B028L26) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B028L27_lift (row : List GridPoint) (h : FamilyMember row F11B028L27) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B028L28_lift (row : List GridPoint) (h : FamilyMember row F11B028L28) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B028L29_lift (row : List GridPoint) (h : FamilyMember row F11B028L29) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B028L30_lift (row : List GridPoint) (h : FamilyMember row F11B028L30) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B028L31_lift (row : List GridPoint) (h : FamilyMember row F11B028L31) : FamilyMember row F11B028 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B028L32_lift (row : List GridPoint) (h : FamilyMember row F11B028L32) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B028L33_lift (row : List GridPoint) (h : FamilyMember row F11B028L33) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B028L34_lift (row : List GridPoint) (h : FamilyMember row F11B028L34) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B028L35_lift (row : List GridPoint) (h : FamilyMember row F11B028L35) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B028L36_lift (row : List GridPoint) (h : FamilyMember row F11B028L36) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B028L37_lift (row : List GridPoint) (h : FamilyMember row F11B028L37) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B028L38_lift (row : List GridPoint) (h : FamilyMember row F11B028L38) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B028L39_lift (row : List GridPoint) (h : FamilyMember row F11B028L39) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B028L40_lift (row : List GridPoint) (h : FamilyMember row F11B028L40) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B028L41_lift (row : List GridPoint) (h : FamilyMember row F11B028L41) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B028L42_lift (row : List GridPoint) (h : FamilyMember row F11B028L42) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B028L43_lift (row : List GridPoint) (h : FamilyMember row F11B028L43) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B028L44_lift (row : List GridPoint) (h : FamilyMember row F11B028L44) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B028L45_lift (row : List GridPoint) (h : FamilyMember row F11B028L45) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B028L46_lift (row : List GridPoint) (h : FamilyMember row F11B028L46) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B028L47_lift (row : List GridPoint) (h : FamilyMember row F11B028L47) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B028L48_lift (row : List GridPoint) (h : FamilyMember row F11B028L48) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B028L49_lift (row : List GridPoint) (h : FamilyMember row F11B028L49) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B028L50_lift (row : List GridPoint) (h : FamilyMember row F11B028L50) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B028L51_lift (row : List GridPoint) (h : FamilyMember row F11B028L51) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B028L52_lift (row : List GridPoint) (h : FamilyMember row F11B028L52) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B028L53_lift (row : List GridPoint) (h : FamilyMember row F11B028L53) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B028L54_lift (row : List GridPoint) (h : FamilyMember row F11B028L54) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B028L55_lift (row : List GridPoint) (h : FamilyMember row F11B028L55) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B028L56_lift (row : List GridPoint) (h : FamilyMember row F11B028L56) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B028L57_lift (row : List GridPoint) (h : FamilyMember row F11B028L57) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B028L58_lift (row : List GridPoint) (h : FamilyMember row F11B028L58) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B028L59_lift (row : List GridPoint) (h : FamilyMember row F11B028L59) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B028L60_lift (row : List GridPoint) (h : FamilyMember row F11B028L60) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B028L61_lift (row : List GridPoint) (h : FamilyMember row F11B028L61) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B028L62_lift (row : List GridPoint) (h : FamilyMember row F11B028L62) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B028L63_lift (row : List GridPoint) (h : FamilyMember row F11B028L63) : FamilyMember row F11B028 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
