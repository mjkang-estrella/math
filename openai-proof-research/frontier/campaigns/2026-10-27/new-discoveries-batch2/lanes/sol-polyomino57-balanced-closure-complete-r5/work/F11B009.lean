import TreeBlock009
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B009L0 : RowFamilyTree := TreeBlock009L0
abbrev F11B009L1 : RowFamilyTree := TreeBlock009L1
abbrev F11B009L2 : RowFamilyTree := TreeBlock009L2
abbrev F11B009L3 : RowFamilyTree := TreeBlock009L3
abbrev F11B009L4 : RowFamilyTree := TreeBlock009L4
abbrev F11B009L5 : RowFamilyTree := TreeBlock009L5
abbrev F11B009L6 : RowFamilyTree := TreeBlock009L6
abbrev F11B009L7 : RowFamilyTree := TreeBlock009L7
abbrev F11B009L8 : RowFamilyTree := TreeBlock009L8
abbrev F11B009L9 : RowFamilyTree := TreeBlock009L9
abbrev F11B009L10 : RowFamilyTree := TreeBlock009L10
abbrev F11B009L11 : RowFamilyTree := TreeBlock009L11
abbrev F11B009L12 : RowFamilyTree := TreeBlock009L12
abbrev F11B009L13 : RowFamilyTree := TreeBlock009L13
abbrev F11B009L14 : RowFamilyTree := TreeBlock009L14
abbrev F11B009L15 : RowFamilyTree := TreeBlock009L15
abbrev F11B009L16 : RowFamilyTree := TreeBlock009L16
abbrev F11B009L17 : RowFamilyTree := TreeBlock009L17
abbrev F11B009L18 : RowFamilyTree := TreeBlock009L18
abbrev F11B009L19 : RowFamilyTree := TreeBlock009L19
abbrev F11B009L20 : RowFamilyTree := TreeBlock009L20
abbrev F11B009L21 : RowFamilyTree := TreeBlock009L21
abbrev F11B009L22 : RowFamilyTree := TreeBlock009L22
abbrev F11B009L23 : RowFamilyTree := TreeBlock009L23
abbrev F11B009L24 : RowFamilyTree := TreeBlock009L24
abbrev F11B009L25 : RowFamilyTree := TreeBlock009L25
abbrev F11B009L26 : RowFamilyTree := TreeBlock009L26
abbrev F11B009L27 : RowFamilyTree := TreeBlock009L27
abbrev F11B009L28 : RowFamilyTree := TreeBlock009L28
abbrev F11B009L29 : RowFamilyTree := TreeBlock009L29
abbrev F11B009L30 : RowFamilyTree := TreeBlock009L30
abbrev F11B009L31 : RowFamilyTree := TreeBlock009L31
abbrev F11B009L32 : RowFamilyTree := TreeBlock009L32
abbrev F11B009L33 : RowFamilyTree := TreeBlock009L33
abbrev F11B009L34 : RowFamilyTree := TreeBlock009L34
abbrev F11B009L35 : RowFamilyTree := TreeBlock009L35
abbrev F11B009L36 : RowFamilyTree := TreeBlock009L36
abbrev F11B009L37 : RowFamilyTree := TreeBlock009L37
abbrev F11B009L38 : RowFamilyTree := TreeBlock009L38
abbrev F11B009L39 : RowFamilyTree := TreeBlock009L39
abbrev F11B009L40 : RowFamilyTree := TreeBlock009L40
abbrev F11B009L41 : RowFamilyTree := TreeBlock009L41
abbrev F11B009L42 : RowFamilyTree := TreeBlock009L42
abbrev F11B009L43 : RowFamilyTree := TreeBlock009L43
abbrev F11B009L44 : RowFamilyTree := TreeBlock009L44
abbrev F11B009L45 : RowFamilyTree := TreeBlock009L45
abbrev F11B009L46 : RowFamilyTree := TreeBlock009L46
abbrev F11B009L47 : RowFamilyTree := TreeBlock009L47
abbrev F11B009L48 : RowFamilyTree := TreeBlock009L48
abbrev F11B009L49 : RowFamilyTree := TreeBlock009L49
abbrev F11B009L50 : RowFamilyTree := TreeBlock009L50
abbrev F11B009L51 : RowFamilyTree := TreeBlock009L51
abbrev F11B009L52 : RowFamilyTree := TreeBlock009L52
abbrev F11B009L53 : RowFamilyTree := TreeBlock009L53
abbrev F11B009L54 : RowFamilyTree := TreeBlock009L54
abbrev F11B009L55 : RowFamilyTree := TreeBlock009L55
abbrev F11B009L56 : RowFamilyTree := TreeBlock009L56
abbrev F11B009L57 : RowFamilyTree := TreeBlock009L57
abbrev F11B009L58 : RowFamilyTree := TreeBlock009L58
abbrev F11B009L59 : RowFamilyTree := TreeBlock009L59
abbrev F11B009L60 : RowFamilyTree := TreeBlock009L60
abbrev F11B009L61 : RowFamilyTree := TreeBlock009L61
abbrev F11B009L62 : RowFamilyTree := TreeBlock009L62
abbrev F11B009L63 : RowFamilyTree := TreeBlock009L63
abbrev F11B009 : RowFamilyTree := TreeBlock009
theorem F11B009L0_lift (row : List GridPoint) (h : FamilyMember row F11B009L0) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B009L1_lift (row : List GridPoint) (h : FamilyMember row F11B009L1) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B009L2_lift (row : List GridPoint) (h : FamilyMember row F11B009L2) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B009L3_lift (row : List GridPoint) (h : FamilyMember row F11B009L3) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B009L4_lift (row : List GridPoint) (h : FamilyMember row F11B009L4) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B009L5_lift (row : List GridPoint) (h : FamilyMember row F11B009L5) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B009L6_lift (row : List GridPoint) (h : FamilyMember row F11B009L6) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B009L7_lift (row : List GridPoint) (h : FamilyMember row F11B009L7) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B009L8_lift (row : List GridPoint) (h : FamilyMember row F11B009L8) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B009L9_lift (row : List GridPoint) (h : FamilyMember row F11B009L9) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B009L10_lift (row : List GridPoint) (h : FamilyMember row F11B009L10) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B009L11_lift (row : List GridPoint) (h : FamilyMember row F11B009L11) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B009L12_lift (row : List GridPoint) (h : FamilyMember row F11B009L12) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B009L13_lift (row : List GridPoint) (h : FamilyMember row F11B009L13) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B009L14_lift (row : List GridPoint) (h : FamilyMember row F11B009L14) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B009L15_lift (row : List GridPoint) (h : FamilyMember row F11B009L15) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B009L16_lift (row : List GridPoint) (h : FamilyMember row F11B009L16) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B009L17_lift (row : List GridPoint) (h : FamilyMember row F11B009L17) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B009L18_lift (row : List GridPoint) (h : FamilyMember row F11B009L18) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B009L19_lift (row : List GridPoint) (h : FamilyMember row F11B009L19) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B009L20_lift (row : List GridPoint) (h : FamilyMember row F11B009L20) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B009L21_lift (row : List GridPoint) (h : FamilyMember row F11B009L21) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B009L22_lift (row : List GridPoint) (h : FamilyMember row F11B009L22) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B009L23_lift (row : List GridPoint) (h : FamilyMember row F11B009L23) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B009L24_lift (row : List GridPoint) (h : FamilyMember row F11B009L24) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B009L25_lift (row : List GridPoint) (h : FamilyMember row F11B009L25) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B009L26_lift (row : List GridPoint) (h : FamilyMember row F11B009L26) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B009L27_lift (row : List GridPoint) (h : FamilyMember row F11B009L27) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B009L28_lift (row : List GridPoint) (h : FamilyMember row F11B009L28) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B009L29_lift (row : List GridPoint) (h : FamilyMember row F11B009L29) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B009L30_lift (row : List GridPoint) (h : FamilyMember row F11B009L30) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B009L31_lift (row : List GridPoint) (h : FamilyMember row F11B009L31) : FamilyMember row F11B009 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B009L32_lift (row : List GridPoint) (h : FamilyMember row F11B009L32) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B009L33_lift (row : List GridPoint) (h : FamilyMember row F11B009L33) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B009L34_lift (row : List GridPoint) (h : FamilyMember row F11B009L34) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B009L35_lift (row : List GridPoint) (h : FamilyMember row F11B009L35) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B009L36_lift (row : List GridPoint) (h : FamilyMember row F11B009L36) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B009L37_lift (row : List GridPoint) (h : FamilyMember row F11B009L37) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B009L38_lift (row : List GridPoint) (h : FamilyMember row F11B009L38) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B009L39_lift (row : List GridPoint) (h : FamilyMember row F11B009L39) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B009L40_lift (row : List GridPoint) (h : FamilyMember row F11B009L40) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B009L41_lift (row : List GridPoint) (h : FamilyMember row F11B009L41) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B009L42_lift (row : List GridPoint) (h : FamilyMember row F11B009L42) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B009L43_lift (row : List GridPoint) (h : FamilyMember row F11B009L43) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B009L44_lift (row : List GridPoint) (h : FamilyMember row F11B009L44) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B009L45_lift (row : List GridPoint) (h : FamilyMember row F11B009L45) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B009L46_lift (row : List GridPoint) (h : FamilyMember row F11B009L46) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B009L47_lift (row : List GridPoint) (h : FamilyMember row F11B009L47) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B009L48_lift (row : List GridPoint) (h : FamilyMember row F11B009L48) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B009L49_lift (row : List GridPoint) (h : FamilyMember row F11B009L49) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B009L50_lift (row : List GridPoint) (h : FamilyMember row F11B009L50) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B009L51_lift (row : List GridPoint) (h : FamilyMember row F11B009L51) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B009L52_lift (row : List GridPoint) (h : FamilyMember row F11B009L52) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B009L53_lift (row : List GridPoint) (h : FamilyMember row F11B009L53) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B009L54_lift (row : List GridPoint) (h : FamilyMember row F11B009L54) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B009L55_lift (row : List GridPoint) (h : FamilyMember row F11B009L55) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B009L56_lift (row : List GridPoint) (h : FamilyMember row F11B009L56) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B009L57_lift (row : List GridPoint) (h : FamilyMember row F11B009L57) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B009L58_lift (row : List GridPoint) (h : FamilyMember row F11B009L58) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B009L59_lift (row : List GridPoint) (h : FamilyMember row F11B009L59) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B009L60_lift (row : List GridPoint) (h : FamilyMember row F11B009L60) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B009L61_lift (row : List GridPoint) (h : FamilyMember row F11B009L61) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B009L62_lift (row : List GridPoint) (h : FamilyMember row F11B009L62) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B009L63_lift (row : List GridPoint) (h : FamilyMember row F11B009L63) : FamilyMember row F11B009 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
