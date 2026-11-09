import TreeBlock025
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B025L0 : RowFamilyTree := TreeBlock025L0
abbrev F11B025L1 : RowFamilyTree := TreeBlock025L1
abbrev F11B025L2 : RowFamilyTree := TreeBlock025L2
abbrev F11B025L3 : RowFamilyTree := TreeBlock025L3
abbrev F11B025L4 : RowFamilyTree := TreeBlock025L4
abbrev F11B025L5 : RowFamilyTree := TreeBlock025L5
abbrev F11B025L6 : RowFamilyTree := TreeBlock025L6
abbrev F11B025L7 : RowFamilyTree := TreeBlock025L7
abbrev F11B025L8 : RowFamilyTree := TreeBlock025L8
abbrev F11B025L9 : RowFamilyTree := TreeBlock025L9
abbrev F11B025L10 : RowFamilyTree := TreeBlock025L10
abbrev F11B025L11 : RowFamilyTree := TreeBlock025L11
abbrev F11B025L12 : RowFamilyTree := TreeBlock025L12
abbrev F11B025L13 : RowFamilyTree := TreeBlock025L13
abbrev F11B025L14 : RowFamilyTree := TreeBlock025L14
abbrev F11B025L15 : RowFamilyTree := TreeBlock025L15
abbrev F11B025L16 : RowFamilyTree := TreeBlock025L16
abbrev F11B025L17 : RowFamilyTree := TreeBlock025L17
abbrev F11B025L18 : RowFamilyTree := TreeBlock025L18
abbrev F11B025L19 : RowFamilyTree := TreeBlock025L19
abbrev F11B025L20 : RowFamilyTree := TreeBlock025L20
abbrev F11B025L21 : RowFamilyTree := TreeBlock025L21
abbrev F11B025L22 : RowFamilyTree := TreeBlock025L22
abbrev F11B025L23 : RowFamilyTree := TreeBlock025L23
abbrev F11B025L24 : RowFamilyTree := TreeBlock025L24
abbrev F11B025L25 : RowFamilyTree := TreeBlock025L25
abbrev F11B025L26 : RowFamilyTree := TreeBlock025L26
abbrev F11B025L27 : RowFamilyTree := TreeBlock025L27
abbrev F11B025L28 : RowFamilyTree := TreeBlock025L28
abbrev F11B025L29 : RowFamilyTree := TreeBlock025L29
abbrev F11B025L30 : RowFamilyTree := TreeBlock025L30
abbrev F11B025L31 : RowFamilyTree := TreeBlock025L31
abbrev F11B025L32 : RowFamilyTree := TreeBlock025L32
abbrev F11B025L33 : RowFamilyTree := TreeBlock025L33
abbrev F11B025L34 : RowFamilyTree := TreeBlock025L34
abbrev F11B025L35 : RowFamilyTree := TreeBlock025L35
abbrev F11B025L36 : RowFamilyTree := TreeBlock025L36
abbrev F11B025L37 : RowFamilyTree := TreeBlock025L37
abbrev F11B025L38 : RowFamilyTree := TreeBlock025L38
abbrev F11B025L39 : RowFamilyTree := TreeBlock025L39
abbrev F11B025L40 : RowFamilyTree := TreeBlock025L40
abbrev F11B025L41 : RowFamilyTree := TreeBlock025L41
abbrev F11B025L42 : RowFamilyTree := TreeBlock025L42
abbrev F11B025L43 : RowFamilyTree := TreeBlock025L43
abbrev F11B025L44 : RowFamilyTree := TreeBlock025L44
abbrev F11B025L45 : RowFamilyTree := TreeBlock025L45
abbrev F11B025L46 : RowFamilyTree := TreeBlock025L46
abbrev F11B025L47 : RowFamilyTree := TreeBlock025L47
abbrev F11B025L48 : RowFamilyTree := TreeBlock025L48
abbrev F11B025L49 : RowFamilyTree := TreeBlock025L49
abbrev F11B025L50 : RowFamilyTree := TreeBlock025L50
abbrev F11B025L51 : RowFamilyTree := TreeBlock025L51
abbrev F11B025L52 : RowFamilyTree := TreeBlock025L52
abbrev F11B025L53 : RowFamilyTree := TreeBlock025L53
abbrev F11B025L54 : RowFamilyTree := TreeBlock025L54
abbrev F11B025L55 : RowFamilyTree := TreeBlock025L55
abbrev F11B025L56 : RowFamilyTree := TreeBlock025L56
abbrev F11B025L57 : RowFamilyTree := TreeBlock025L57
abbrev F11B025L58 : RowFamilyTree := TreeBlock025L58
abbrev F11B025L59 : RowFamilyTree := TreeBlock025L59
abbrev F11B025L60 : RowFamilyTree := TreeBlock025L60
abbrev F11B025L61 : RowFamilyTree := TreeBlock025L61
abbrev F11B025L62 : RowFamilyTree := TreeBlock025L62
abbrev F11B025L63 : RowFamilyTree := TreeBlock025L63
abbrev F11B025 : RowFamilyTree := TreeBlock025
theorem F11B025L0_lift (row : List GridPoint) (h : FamilyMember row F11B025L0) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B025L1_lift (row : List GridPoint) (h : FamilyMember row F11B025L1) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B025L2_lift (row : List GridPoint) (h : FamilyMember row F11B025L2) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B025L3_lift (row : List GridPoint) (h : FamilyMember row F11B025L3) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B025L4_lift (row : List GridPoint) (h : FamilyMember row F11B025L4) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B025L5_lift (row : List GridPoint) (h : FamilyMember row F11B025L5) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B025L6_lift (row : List GridPoint) (h : FamilyMember row F11B025L6) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B025L7_lift (row : List GridPoint) (h : FamilyMember row F11B025L7) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B025L8_lift (row : List GridPoint) (h : FamilyMember row F11B025L8) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B025L9_lift (row : List GridPoint) (h : FamilyMember row F11B025L9) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B025L10_lift (row : List GridPoint) (h : FamilyMember row F11B025L10) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B025L11_lift (row : List GridPoint) (h : FamilyMember row F11B025L11) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B025L12_lift (row : List GridPoint) (h : FamilyMember row F11B025L12) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B025L13_lift (row : List GridPoint) (h : FamilyMember row F11B025L13) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B025L14_lift (row : List GridPoint) (h : FamilyMember row F11B025L14) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B025L15_lift (row : List GridPoint) (h : FamilyMember row F11B025L15) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B025L16_lift (row : List GridPoint) (h : FamilyMember row F11B025L16) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B025L17_lift (row : List GridPoint) (h : FamilyMember row F11B025L17) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B025L18_lift (row : List GridPoint) (h : FamilyMember row F11B025L18) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B025L19_lift (row : List GridPoint) (h : FamilyMember row F11B025L19) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B025L20_lift (row : List GridPoint) (h : FamilyMember row F11B025L20) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B025L21_lift (row : List GridPoint) (h : FamilyMember row F11B025L21) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B025L22_lift (row : List GridPoint) (h : FamilyMember row F11B025L22) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B025L23_lift (row : List GridPoint) (h : FamilyMember row F11B025L23) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B025L24_lift (row : List GridPoint) (h : FamilyMember row F11B025L24) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B025L25_lift (row : List GridPoint) (h : FamilyMember row F11B025L25) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B025L26_lift (row : List GridPoint) (h : FamilyMember row F11B025L26) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B025L27_lift (row : List GridPoint) (h : FamilyMember row F11B025L27) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B025L28_lift (row : List GridPoint) (h : FamilyMember row F11B025L28) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B025L29_lift (row : List GridPoint) (h : FamilyMember row F11B025L29) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B025L30_lift (row : List GridPoint) (h : FamilyMember row F11B025L30) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B025L31_lift (row : List GridPoint) (h : FamilyMember row F11B025L31) : FamilyMember row F11B025 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B025L32_lift (row : List GridPoint) (h : FamilyMember row F11B025L32) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B025L33_lift (row : List GridPoint) (h : FamilyMember row F11B025L33) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B025L34_lift (row : List GridPoint) (h : FamilyMember row F11B025L34) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B025L35_lift (row : List GridPoint) (h : FamilyMember row F11B025L35) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B025L36_lift (row : List GridPoint) (h : FamilyMember row F11B025L36) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B025L37_lift (row : List GridPoint) (h : FamilyMember row F11B025L37) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B025L38_lift (row : List GridPoint) (h : FamilyMember row F11B025L38) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B025L39_lift (row : List GridPoint) (h : FamilyMember row F11B025L39) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B025L40_lift (row : List GridPoint) (h : FamilyMember row F11B025L40) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B025L41_lift (row : List GridPoint) (h : FamilyMember row F11B025L41) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B025L42_lift (row : List GridPoint) (h : FamilyMember row F11B025L42) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B025L43_lift (row : List GridPoint) (h : FamilyMember row F11B025L43) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B025L44_lift (row : List GridPoint) (h : FamilyMember row F11B025L44) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B025L45_lift (row : List GridPoint) (h : FamilyMember row F11B025L45) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B025L46_lift (row : List GridPoint) (h : FamilyMember row F11B025L46) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B025L47_lift (row : List GridPoint) (h : FamilyMember row F11B025L47) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B025L48_lift (row : List GridPoint) (h : FamilyMember row F11B025L48) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B025L49_lift (row : List GridPoint) (h : FamilyMember row F11B025L49) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B025L50_lift (row : List GridPoint) (h : FamilyMember row F11B025L50) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B025L51_lift (row : List GridPoint) (h : FamilyMember row F11B025L51) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B025L52_lift (row : List GridPoint) (h : FamilyMember row F11B025L52) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B025L53_lift (row : List GridPoint) (h : FamilyMember row F11B025L53) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B025L54_lift (row : List GridPoint) (h : FamilyMember row F11B025L54) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B025L55_lift (row : List GridPoint) (h : FamilyMember row F11B025L55) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B025L56_lift (row : List GridPoint) (h : FamilyMember row F11B025L56) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B025L57_lift (row : List GridPoint) (h : FamilyMember row F11B025L57) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B025L58_lift (row : List GridPoint) (h : FamilyMember row F11B025L58) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B025L59_lift (row : List GridPoint) (h : FamilyMember row F11B025L59) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B025L60_lift (row : List GridPoint) (h : FamilyMember row F11B025L60) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B025L61_lift (row : List GridPoint) (h : FamilyMember row F11B025L61) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B025L62_lift (row : List GridPoint) (h : FamilyMember row F11B025L62) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B025L63_lift (row : List GridPoint) (h : FamilyMember row F11B025L63) : FamilyMember row F11B025 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
