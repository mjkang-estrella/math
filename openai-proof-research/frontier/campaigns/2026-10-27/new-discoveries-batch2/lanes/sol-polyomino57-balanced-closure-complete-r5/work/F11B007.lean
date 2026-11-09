import TreeBlock007
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B007L0 : RowFamilyTree := TreeBlock007L0
abbrev F11B007L1 : RowFamilyTree := TreeBlock007L1
abbrev F11B007L2 : RowFamilyTree := TreeBlock007L2
abbrev F11B007L3 : RowFamilyTree := TreeBlock007L3
abbrev F11B007L4 : RowFamilyTree := TreeBlock007L4
abbrev F11B007L5 : RowFamilyTree := TreeBlock007L5
abbrev F11B007L6 : RowFamilyTree := TreeBlock007L6
abbrev F11B007L7 : RowFamilyTree := TreeBlock007L7
abbrev F11B007L8 : RowFamilyTree := TreeBlock007L8
abbrev F11B007L9 : RowFamilyTree := TreeBlock007L9
abbrev F11B007L10 : RowFamilyTree := TreeBlock007L10
abbrev F11B007L11 : RowFamilyTree := TreeBlock007L11
abbrev F11B007L12 : RowFamilyTree := TreeBlock007L12
abbrev F11B007L13 : RowFamilyTree := TreeBlock007L13
abbrev F11B007L14 : RowFamilyTree := TreeBlock007L14
abbrev F11B007L15 : RowFamilyTree := TreeBlock007L15
abbrev F11B007L16 : RowFamilyTree := TreeBlock007L16
abbrev F11B007L17 : RowFamilyTree := TreeBlock007L17
abbrev F11B007L18 : RowFamilyTree := TreeBlock007L18
abbrev F11B007L19 : RowFamilyTree := TreeBlock007L19
abbrev F11B007L20 : RowFamilyTree := TreeBlock007L20
abbrev F11B007L21 : RowFamilyTree := TreeBlock007L21
abbrev F11B007L22 : RowFamilyTree := TreeBlock007L22
abbrev F11B007L23 : RowFamilyTree := TreeBlock007L23
abbrev F11B007L24 : RowFamilyTree := TreeBlock007L24
abbrev F11B007L25 : RowFamilyTree := TreeBlock007L25
abbrev F11B007L26 : RowFamilyTree := TreeBlock007L26
abbrev F11B007L27 : RowFamilyTree := TreeBlock007L27
abbrev F11B007L28 : RowFamilyTree := TreeBlock007L28
abbrev F11B007L29 : RowFamilyTree := TreeBlock007L29
abbrev F11B007L30 : RowFamilyTree := TreeBlock007L30
abbrev F11B007L31 : RowFamilyTree := TreeBlock007L31
abbrev F11B007L32 : RowFamilyTree := TreeBlock007L32
abbrev F11B007L33 : RowFamilyTree := TreeBlock007L33
abbrev F11B007L34 : RowFamilyTree := TreeBlock007L34
abbrev F11B007L35 : RowFamilyTree := TreeBlock007L35
abbrev F11B007L36 : RowFamilyTree := TreeBlock007L36
abbrev F11B007L37 : RowFamilyTree := TreeBlock007L37
abbrev F11B007L38 : RowFamilyTree := TreeBlock007L38
abbrev F11B007L39 : RowFamilyTree := TreeBlock007L39
abbrev F11B007L40 : RowFamilyTree := TreeBlock007L40
abbrev F11B007L41 : RowFamilyTree := TreeBlock007L41
abbrev F11B007L42 : RowFamilyTree := TreeBlock007L42
abbrev F11B007L43 : RowFamilyTree := TreeBlock007L43
abbrev F11B007L44 : RowFamilyTree := TreeBlock007L44
abbrev F11B007L45 : RowFamilyTree := TreeBlock007L45
abbrev F11B007L46 : RowFamilyTree := TreeBlock007L46
abbrev F11B007L47 : RowFamilyTree := TreeBlock007L47
abbrev F11B007L48 : RowFamilyTree := TreeBlock007L48
abbrev F11B007L49 : RowFamilyTree := TreeBlock007L49
abbrev F11B007L50 : RowFamilyTree := TreeBlock007L50
abbrev F11B007L51 : RowFamilyTree := TreeBlock007L51
abbrev F11B007L52 : RowFamilyTree := TreeBlock007L52
abbrev F11B007L53 : RowFamilyTree := TreeBlock007L53
abbrev F11B007L54 : RowFamilyTree := TreeBlock007L54
abbrev F11B007L55 : RowFamilyTree := TreeBlock007L55
abbrev F11B007L56 : RowFamilyTree := TreeBlock007L56
abbrev F11B007L57 : RowFamilyTree := TreeBlock007L57
abbrev F11B007L58 : RowFamilyTree := TreeBlock007L58
abbrev F11B007L59 : RowFamilyTree := TreeBlock007L59
abbrev F11B007L60 : RowFamilyTree := TreeBlock007L60
abbrev F11B007L61 : RowFamilyTree := TreeBlock007L61
abbrev F11B007L62 : RowFamilyTree := TreeBlock007L62
abbrev F11B007L63 : RowFamilyTree := TreeBlock007L63
abbrev F11B007 : RowFamilyTree := TreeBlock007
theorem F11B007L0_lift (row : List GridPoint) (h : FamilyMember row F11B007L0) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B007L1_lift (row : List GridPoint) (h : FamilyMember row F11B007L1) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B007L2_lift (row : List GridPoint) (h : FamilyMember row F11B007L2) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B007L3_lift (row : List GridPoint) (h : FamilyMember row F11B007L3) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B007L4_lift (row : List GridPoint) (h : FamilyMember row F11B007L4) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B007L5_lift (row : List GridPoint) (h : FamilyMember row F11B007L5) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B007L6_lift (row : List GridPoint) (h : FamilyMember row F11B007L6) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B007L7_lift (row : List GridPoint) (h : FamilyMember row F11B007L7) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B007L8_lift (row : List GridPoint) (h : FamilyMember row F11B007L8) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B007L9_lift (row : List GridPoint) (h : FamilyMember row F11B007L9) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B007L10_lift (row : List GridPoint) (h : FamilyMember row F11B007L10) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B007L11_lift (row : List GridPoint) (h : FamilyMember row F11B007L11) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B007L12_lift (row : List GridPoint) (h : FamilyMember row F11B007L12) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B007L13_lift (row : List GridPoint) (h : FamilyMember row F11B007L13) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B007L14_lift (row : List GridPoint) (h : FamilyMember row F11B007L14) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B007L15_lift (row : List GridPoint) (h : FamilyMember row F11B007L15) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B007L16_lift (row : List GridPoint) (h : FamilyMember row F11B007L16) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B007L17_lift (row : List GridPoint) (h : FamilyMember row F11B007L17) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B007L18_lift (row : List GridPoint) (h : FamilyMember row F11B007L18) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B007L19_lift (row : List GridPoint) (h : FamilyMember row F11B007L19) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B007L20_lift (row : List GridPoint) (h : FamilyMember row F11B007L20) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B007L21_lift (row : List GridPoint) (h : FamilyMember row F11B007L21) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B007L22_lift (row : List GridPoint) (h : FamilyMember row F11B007L22) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B007L23_lift (row : List GridPoint) (h : FamilyMember row F11B007L23) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B007L24_lift (row : List GridPoint) (h : FamilyMember row F11B007L24) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B007L25_lift (row : List GridPoint) (h : FamilyMember row F11B007L25) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B007L26_lift (row : List GridPoint) (h : FamilyMember row F11B007L26) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B007L27_lift (row : List GridPoint) (h : FamilyMember row F11B007L27) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B007L28_lift (row : List GridPoint) (h : FamilyMember row F11B007L28) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B007L29_lift (row : List GridPoint) (h : FamilyMember row F11B007L29) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B007L30_lift (row : List GridPoint) (h : FamilyMember row F11B007L30) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B007L31_lift (row : List GridPoint) (h : FamilyMember row F11B007L31) : FamilyMember row F11B007 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B007L32_lift (row : List GridPoint) (h : FamilyMember row F11B007L32) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B007L33_lift (row : List GridPoint) (h : FamilyMember row F11B007L33) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B007L34_lift (row : List GridPoint) (h : FamilyMember row F11B007L34) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B007L35_lift (row : List GridPoint) (h : FamilyMember row F11B007L35) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B007L36_lift (row : List GridPoint) (h : FamilyMember row F11B007L36) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B007L37_lift (row : List GridPoint) (h : FamilyMember row F11B007L37) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B007L38_lift (row : List GridPoint) (h : FamilyMember row F11B007L38) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B007L39_lift (row : List GridPoint) (h : FamilyMember row F11B007L39) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B007L40_lift (row : List GridPoint) (h : FamilyMember row F11B007L40) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B007L41_lift (row : List GridPoint) (h : FamilyMember row F11B007L41) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B007L42_lift (row : List GridPoint) (h : FamilyMember row F11B007L42) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B007L43_lift (row : List GridPoint) (h : FamilyMember row F11B007L43) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B007L44_lift (row : List GridPoint) (h : FamilyMember row F11B007L44) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B007L45_lift (row : List GridPoint) (h : FamilyMember row F11B007L45) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B007L46_lift (row : List GridPoint) (h : FamilyMember row F11B007L46) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B007L47_lift (row : List GridPoint) (h : FamilyMember row F11B007L47) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B007L48_lift (row : List GridPoint) (h : FamilyMember row F11B007L48) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B007L49_lift (row : List GridPoint) (h : FamilyMember row F11B007L49) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B007L50_lift (row : List GridPoint) (h : FamilyMember row F11B007L50) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B007L51_lift (row : List GridPoint) (h : FamilyMember row F11B007L51) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B007L52_lift (row : List GridPoint) (h : FamilyMember row F11B007L52) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B007L53_lift (row : List GridPoint) (h : FamilyMember row F11B007L53) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B007L54_lift (row : List GridPoint) (h : FamilyMember row F11B007L54) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B007L55_lift (row : List GridPoint) (h : FamilyMember row F11B007L55) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B007L56_lift (row : List GridPoint) (h : FamilyMember row F11B007L56) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B007L57_lift (row : List GridPoint) (h : FamilyMember row F11B007L57) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B007L58_lift (row : List GridPoint) (h : FamilyMember row F11B007L58) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B007L59_lift (row : List GridPoint) (h : FamilyMember row F11B007L59) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B007L60_lift (row : List GridPoint) (h : FamilyMember row F11B007L60) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B007L61_lift (row : List GridPoint) (h : FamilyMember row F11B007L61) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B007L62_lift (row : List GridPoint) (h : FamilyMember row F11B007L62) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B007L63_lift (row : List GridPoint) (h : FamilyMember row F11B007L63) : FamilyMember row F11B007 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
