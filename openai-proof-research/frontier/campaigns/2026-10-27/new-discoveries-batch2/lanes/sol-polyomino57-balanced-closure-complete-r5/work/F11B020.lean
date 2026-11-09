import TreeBlock020
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B020L0 : RowFamilyTree := TreeBlock020L0
abbrev F11B020L1 : RowFamilyTree := TreeBlock020L1
abbrev F11B020L2 : RowFamilyTree := TreeBlock020L2
abbrev F11B020L3 : RowFamilyTree := TreeBlock020L3
abbrev F11B020L4 : RowFamilyTree := TreeBlock020L4
abbrev F11B020L5 : RowFamilyTree := TreeBlock020L5
abbrev F11B020L6 : RowFamilyTree := TreeBlock020L6
abbrev F11B020L7 : RowFamilyTree := TreeBlock020L7
abbrev F11B020L8 : RowFamilyTree := TreeBlock020L8
abbrev F11B020L9 : RowFamilyTree := TreeBlock020L9
abbrev F11B020L10 : RowFamilyTree := TreeBlock020L10
abbrev F11B020L11 : RowFamilyTree := TreeBlock020L11
abbrev F11B020L12 : RowFamilyTree := TreeBlock020L12
abbrev F11B020L13 : RowFamilyTree := TreeBlock020L13
abbrev F11B020L14 : RowFamilyTree := TreeBlock020L14
abbrev F11B020L15 : RowFamilyTree := TreeBlock020L15
abbrev F11B020L16 : RowFamilyTree := TreeBlock020L16
abbrev F11B020L17 : RowFamilyTree := TreeBlock020L17
abbrev F11B020L18 : RowFamilyTree := TreeBlock020L18
abbrev F11B020L19 : RowFamilyTree := TreeBlock020L19
abbrev F11B020L20 : RowFamilyTree := TreeBlock020L20
abbrev F11B020L21 : RowFamilyTree := TreeBlock020L21
abbrev F11B020L22 : RowFamilyTree := TreeBlock020L22
abbrev F11B020L23 : RowFamilyTree := TreeBlock020L23
abbrev F11B020L24 : RowFamilyTree := TreeBlock020L24
abbrev F11B020L25 : RowFamilyTree := TreeBlock020L25
abbrev F11B020L26 : RowFamilyTree := TreeBlock020L26
abbrev F11B020L27 : RowFamilyTree := TreeBlock020L27
abbrev F11B020L28 : RowFamilyTree := TreeBlock020L28
abbrev F11B020L29 : RowFamilyTree := TreeBlock020L29
abbrev F11B020L30 : RowFamilyTree := TreeBlock020L30
abbrev F11B020L31 : RowFamilyTree := TreeBlock020L31
abbrev F11B020L32 : RowFamilyTree := TreeBlock020L32
abbrev F11B020L33 : RowFamilyTree := TreeBlock020L33
abbrev F11B020L34 : RowFamilyTree := TreeBlock020L34
abbrev F11B020L35 : RowFamilyTree := TreeBlock020L35
abbrev F11B020L36 : RowFamilyTree := TreeBlock020L36
abbrev F11B020L37 : RowFamilyTree := TreeBlock020L37
abbrev F11B020L38 : RowFamilyTree := TreeBlock020L38
abbrev F11B020L39 : RowFamilyTree := TreeBlock020L39
abbrev F11B020L40 : RowFamilyTree := TreeBlock020L40
abbrev F11B020L41 : RowFamilyTree := TreeBlock020L41
abbrev F11B020L42 : RowFamilyTree := TreeBlock020L42
abbrev F11B020L43 : RowFamilyTree := TreeBlock020L43
abbrev F11B020L44 : RowFamilyTree := TreeBlock020L44
abbrev F11B020L45 : RowFamilyTree := TreeBlock020L45
abbrev F11B020L46 : RowFamilyTree := TreeBlock020L46
abbrev F11B020L47 : RowFamilyTree := TreeBlock020L47
abbrev F11B020L48 : RowFamilyTree := TreeBlock020L48
abbrev F11B020L49 : RowFamilyTree := TreeBlock020L49
abbrev F11B020L50 : RowFamilyTree := TreeBlock020L50
abbrev F11B020L51 : RowFamilyTree := TreeBlock020L51
abbrev F11B020L52 : RowFamilyTree := TreeBlock020L52
abbrev F11B020L53 : RowFamilyTree := TreeBlock020L53
abbrev F11B020L54 : RowFamilyTree := TreeBlock020L54
abbrev F11B020L55 : RowFamilyTree := TreeBlock020L55
abbrev F11B020L56 : RowFamilyTree := TreeBlock020L56
abbrev F11B020L57 : RowFamilyTree := TreeBlock020L57
abbrev F11B020L58 : RowFamilyTree := TreeBlock020L58
abbrev F11B020L59 : RowFamilyTree := TreeBlock020L59
abbrev F11B020L60 : RowFamilyTree := TreeBlock020L60
abbrev F11B020L61 : RowFamilyTree := TreeBlock020L61
abbrev F11B020L62 : RowFamilyTree := TreeBlock020L62
abbrev F11B020L63 : RowFamilyTree := TreeBlock020L63
abbrev F11B020 : RowFamilyTree := TreeBlock020
theorem F11B020L0_lift (row : List GridPoint) (h : FamilyMember row F11B020L0) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B020L1_lift (row : List GridPoint) (h : FamilyMember row F11B020L1) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B020L2_lift (row : List GridPoint) (h : FamilyMember row F11B020L2) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B020L3_lift (row : List GridPoint) (h : FamilyMember row F11B020L3) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B020L4_lift (row : List GridPoint) (h : FamilyMember row F11B020L4) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B020L5_lift (row : List GridPoint) (h : FamilyMember row F11B020L5) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B020L6_lift (row : List GridPoint) (h : FamilyMember row F11B020L6) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B020L7_lift (row : List GridPoint) (h : FamilyMember row F11B020L7) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B020L8_lift (row : List GridPoint) (h : FamilyMember row F11B020L8) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B020L9_lift (row : List GridPoint) (h : FamilyMember row F11B020L9) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B020L10_lift (row : List GridPoint) (h : FamilyMember row F11B020L10) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B020L11_lift (row : List GridPoint) (h : FamilyMember row F11B020L11) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B020L12_lift (row : List GridPoint) (h : FamilyMember row F11B020L12) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B020L13_lift (row : List GridPoint) (h : FamilyMember row F11B020L13) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B020L14_lift (row : List GridPoint) (h : FamilyMember row F11B020L14) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B020L15_lift (row : List GridPoint) (h : FamilyMember row F11B020L15) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B020L16_lift (row : List GridPoint) (h : FamilyMember row F11B020L16) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B020L17_lift (row : List GridPoint) (h : FamilyMember row F11B020L17) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B020L18_lift (row : List GridPoint) (h : FamilyMember row F11B020L18) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B020L19_lift (row : List GridPoint) (h : FamilyMember row F11B020L19) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B020L20_lift (row : List GridPoint) (h : FamilyMember row F11B020L20) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B020L21_lift (row : List GridPoint) (h : FamilyMember row F11B020L21) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B020L22_lift (row : List GridPoint) (h : FamilyMember row F11B020L22) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B020L23_lift (row : List GridPoint) (h : FamilyMember row F11B020L23) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B020L24_lift (row : List GridPoint) (h : FamilyMember row F11B020L24) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B020L25_lift (row : List GridPoint) (h : FamilyMember row F11B020L25) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B020L26_lift (row : List GridPoint) (h : FamilyMember row F11B020L26) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B020L27_lift (row : List GridPoint) (h : FamilyMember row F11B020L27) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B020L28_lift (row : List GridPoint) (h : FamilyMember row F11B020L28) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B020L29_lift (row : List GridPoint) (h : FamilyMember row F11B020L29) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B020L30_lift (row : List GridPoint) (h : FamilyMember row F11B020L30) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B020L31_lift (row : List GridPoint) (h : FamilyMember row F11B020L31) : FamilyMember row F11B020 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B020L32_lift (row : List GridPoint) (h : FamilyMember row F11B020L32) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B020L33_lift (row : List GridPoint) (h : FamilyMember row F11B020L33) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B020L34_lift (row : List GridPoint) (h : FamilyMember row F11B020L34) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B020L35_lift (row : List GridPoint) (h : FamilyMember row F11B020L35) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B020L36_lift (row : List GridPoint) (h : FamilyMember row F11B020L36) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B020L37_lift (row : List GridPoint) (h : FamilyMember row F11B020L37) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B020L38_lift (row : List GridPoint) (h : FamilyMember row F11B020L38) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B020L39_lift (row : List GridPoint) (h : FamilyMember row F11B020L39) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B020L40_lift (row : List GridPoint) (h : FamilyMember row F11B020L40) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B020L41_lift (row : List GridPoint) (h : FamilyMember row F11B020L41) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B020L42_lift (row : List GridPoint) (h : FamilyMember row F11B020L42) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B020L43_lift (row : List GridPoint) (h : FamilyMember row F11B020L43) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B020L44_lift (row : List GridPoint) (h : FamilyMember row F11B020L44) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B020L45_lift (row : List GridPoint) (h : FamilyMember row F11B020L45) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B020L46_lift (row : List GridPoint) (h : FamilyMember row F11B020L46) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B020L47_lift (row : List GridPoint) (h : FamilyMember row F11B020L47) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B020L48_lift (row : List GridPoint) (h : FamilyMember row F11B020L48) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B020L49_lift (row : List GridPoint) (h : FamilyMember row F11B020L49) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B020L50_lift (row : List GridPoint) (h : FamilyMember row F11B020L50) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B020L51_lift (row : List GridPoint) (h : FamilyMember row F11B020L51) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B020L52_lift (row : List GridPoint) (h : FamilyMember row F11B020L52) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B020L53_lift (row : List GridPoint) (h : FamilyMember row F11B020L53) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B020L54_lift (row : List GridPoint) (h : FamilyMember row F11B020L54) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B020L55_lift (row : List GridPoint) (h : FamilyMember row F11B020L55) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B020L56_lift (row : List GridPoint) (h : FamilyMember row F11B020L56) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B020L57_lift (row : List GridPoint) (h : FamilyMember row F11B020L57) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B020L58_lift (row : List GridPoint) (h : FamilyMember row F11B020L58) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B020L59_lift (row : List GridPoint) (h : FamilyMember row F11B020L59) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B020L60_lift (row : List GridPoint) (h : FamilyMember row F11B020L60) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B020L61_lift (row : List GridPoint) (h : FamilyMember row F11B020L61) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B020L62_lift (row : List GridPoint) (h : FamilyMember row F11B020L62) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B020L63_lift (row : List GridPoint) (h : FamilyMember row F11B020L63) : FamilyMember row F11B020 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
