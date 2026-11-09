import TreeBlock012
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B012L0 : RowFamilyTree := TreeBlock012L0
abbrev F11B012L1 : RowFamilyTree := TreeBlock012L1
abbrev F11B012L2 : RowFamilyTree := TreeBlock012L2
abbrev F11B012L3 : RowFamilyTree := TreeBlock012L3
abbrev F11B012L4 : RowFamilyTree := TreeBlock012L4
abbrev F11B012L5 : RowFamilyTree := TreeBlock012L5
abbrev F11B012L6 : RowFamilyTree := TreeBlock012L6
abbrev F11B012L7 : RowFamilyTree := TreeBlock012L7
abbrev F11B012L8 : RowFamilyTree := TreeBlock012L8
abbrev F11B012L9 : RowFamilyTree := TreeBlock012L9
abbrev F11B012L10 : RowFamilyTree := TreeBlock012L10
abbrev F11B012L11 : RowFamilyTree := TreeBlock012L11
abbrev F11B012L12 : RowFamilyTree := TreeBlock012L12
abbrev F11B012L13 : RowFamilyTree := TreeBlock012L13
abbrev F11B012L14 : RowFamilyTree := TreeBlock012L14
abbrev F11B012L15 : RowFamilyTree := TreeBlock012L15
abbrev F11B012L16 : RowFamilyTree := TreeBlock012L16
abbrev F11B012L17 : RowFamilyTree := TreeBlock012L17
abbrev F11B012L18 : RowFamilyTree := TreeBlock012L18
abbrev F11B012L19 : RowFamilyTree := TreeBlock012L19
abbrev F11B012L20 : RowFamilyTree := TreeBlock012L20
abbrev F11B012L21 : RowFamilyTree := TreeBlock012L21
abbrev F11B012L22 : RowFamilyTree := TreeBlock012L22
abbrev F11B012L23 : RowFamilyTree := TreeBlock012L23
abbrev F11B012L24 : RowFamilyTree := TreeBlock012L24
abbrev F11B012L25 : RowFamilyTree := TreeBlock012L25
abbrev F11B012L26 : RowFamilyTree := TreeBlock012L26
abbrev F11B012L27 : RowFamilyTree := TreeBlock012L27
abbrev F11B012L28 : RowFamilyTree := TreeBlock012L28
abbrev F11B012L29 : RowFamilyTree := TreeBlock012L29
abbrev F11B012L30 : RowFamilyTree := TreeBlock012L30
abbrev F11B012L31 : RowFamilyTree := TreeBlock012L31
abbrev F11B012L32 : RowFamilyTree := TreeBlock012L32
abbrev F11B012L33 : RowFamilyTree := TreeBlock012L33
abbrev F11B012L34 : RowFamilyTree := TreeBlock012L34
abbrev F11B012L35 : RowFamilyTree := TreeBlock012L35
abbrev F11B012L36 : RowFamilyTree := TreeBlock012L36
abbrev F11B012L37 : RowFamilyTree := TreeBlock012L37
abbrev F11B012L38 : RowFamilyTree := TreeBlock012L38
abbrev F11B012L39 : RowFamilyTree := TreeBlock012L39
abbrev F11B012L40 : RowFamilyTree := TreeBlock012L40
abbrev F11B012L41 : RowFamilyTree := TreeBlock012L41
abbrev F11B012L42 : RowFamilyTree := TreeBlock012L42
abbrev F11B012L43 : RowFamilyTree := TreeBlock012L43
abbrev F11B012L44 : RowFamilyTree := TreeBlock012L44
abbrev F11B012L45 : RowFamilyTree := TreeBlock012L45
abbrev F11B012L46 : RowFamilyTree := TreeBlock012L46
abbrev F11B012L47 : RowFamilyTree := TreeBlock012L47
abbrev F11B012L48 : RowFamilyTree := TreeBlock012L48
abbrev F11B012L49 : RowFamilyTree := TreeBlock012L49
abbrev F11B012L50 : RowFamilyTree := TreeBlock012L50
abbrev F11B012L51 : RowFamilyTree := TreeBlock012L51
abbrev F11B012L52 : RowFamilyTree := TreeBlock012L52
abbrev F11B012L53 : RowFamilyTree := TreeBlock012L53
abbrev F11B012L54 : RowFamilyTree := TreeBlock012L54
abbrev F11B012L55 : RowFamilyTree := TreeBlock012L55
abbrev F11B012L56 : RowFamilyTree := TreeBlock012L56
abbrev F11B012L57 : RowFamilyTree := TreeBlock012L57
abbrev F11B012L58 : RowFamilyTree := TreeBlock012L58
abbrev F11B012L59 : RowFamilyTree := TreeBlock012L59
abbrev F11B012L60 : RowFamilyTree := TreeBlock012L60
abbrev F11B012L61 : RowFamilyTree := TreeBlock012L61
abbrev F11B012L62 : RowFamilyTree := TreeBlock012L62
abbrev F11B012L63 : RowFamilyTree := TreeBlock012L63
abbrev F11B012 : RowFamilyTree := TreeBlock012
theorem F11B012L0_lift (row : List GridPoint) (h : FamilyMember row F11B012L0) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B012L1_lift (row : List GridPoint) (h : FamilyMember row F11B012L1) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B012L2_lift (row : List GridPoint) (h : FamilyMember row F11B012L2) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B012L3_lift (row : List GridPoint) (h : FamilyMember row F11B012L3) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B012L4_lift (row : List GridPoint) (h : FamilyMember row F11B012L4) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B012L5_lift (row : List GridPoint) (h : FamilyMember row F11B012L5) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B012L6_lift (row : List GridPoint) (h : FamilyMember row F11B012L6) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B012L7_lift (row : List GridPoint) (h : FamilyMember row F11B012L7) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B012L8_lift (row : List GridPoint) (h : FamilyMember row F11B012L8) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B012L9_lift (row : List GridPoint) (h : FamilyMember row F11B012L9) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B012L10_lift (row : List GridPoint) (h : FamilyMember row F11B012L10) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B012L11_lift (row : List GridPoint) (h : FamilyMember row F11B012L11) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B012L12_lift (row : List GridPoint) (h : FamilyMember row F11B012L12) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B012L13_lift (row : List GridPoint) (h : FamilyMember row F11B012L13) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B012L14_lift (row : List GridPoint) (h : FamilyMember row F11B012L14) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B012L15_lift (row : List GridPoint) (h : FamilyMember row F11B012L15) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B012L16_lift (row : List GridPoint) (h : FamilyMember row F11B012L16) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B012L17_lift (row : List GridPoint) (h : FamilyMember row F11B012L17) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B012L18_lift (row : List GridPoint) (h : FamilyMember row F11B012L18) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B012L19_lift (row : List GridPoint) (h : FamilyMember row F11B012L19) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B012L20_lift (row : List GridPoint) (h : FamilyMember row F11B012L20) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B012L21_lift (row : List GridPoint) (h : FamilyMember row F11B012L21) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B012L22_lift (row : List GridPoint) (h : FamilyMember row F11B012L22) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B012L23_lift (row : List GridPoint) (h : FamilyMember row F11B012L23) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B012L24_lift (row : List GridPoint) (h : FamilyMember row F11B012L24) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B012L25_lift (row : List GridPoint) (h : FamilyMember row F11B012L25) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B012L26_lift (row : List GridPoint) (h : FamilyMember row F11B012L26) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B012L27_lift (row : List GridPoint) (h : FamilyMember row F11B012L27) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B012L28_lift (row : List GridPoint) (h : FamilyMember row F11B012L28) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B012L29_lift (row : List GridPoint) (h : FamilyMember row F11B012L29) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B012L30_lift (row : List GridPoint) (h : FamilyMember row F11B012L30) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B012L31_lift (row : List GridPoint) (h : FamilyMember row F11B012L31) : FamilyMember row F11B012 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B012L32_lift (row : List GridPoint) (h : FamilyMember row F11B012L32) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B012L33_lift (row : List GridPoint) (h : FamilyMember row F11B012L33) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B012L34_lift (row : List GridPoint) (h : FamilyMember row F11B012L34) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B012L35_lift (row : List GridPoint) (h : FamilyMember row F11B012L35) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B012L36_lift (row : List GridPoint) (h : FamilyMember row F11B012L36) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B012L37_lift (row : List GridPoint) (h : FamilyMember row F11B012L37) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B012L38_lift (row : List GridPoint) (h : FamilyMember row F11B012L38) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B012L39_lift (row : List GridPoint) (h : FamilyMember row F11B012L39) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B012L40_lift (row : List GridPoint) (h : FamilyMember row F11B012L40) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B012L41_lift (row : List GridPoint) (h : FamilyMember row F11B012L41) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B012L42_lift (row : List GridPoint) (h : FamilyMember row F11B012L42) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B012L43_lift (row : List GridPoint) (h : FamilyMember row F11B012L43) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B012L44_lift (row : List GridPoint) (h : FamilyMember row F11B012L44) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B012L45_lift (row : List GridPoint) (h : FamilyMember row F11B012L45) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B012L46_lift (row : List GridPoint) (h : FamilyMember row F11B012L46) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B012L47_lift (row : List GridPoint) (h : FamilyMember row F11B012L47) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B012L48_lift (row : List GridPoint) (h : FamilyMember row F11B012L48) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B012L49_lift (row : List GridPoint) (h : FamilyMember row F11B012L49) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B012L50_lift (row : List GridPoint) (h : FamilyMember row F11B012L50) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B012L51_lift (row : List GridPoint) (h : FamilyMember row F11B012L51) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B012L52_lift (row : List GridPoint) (h : FamilyMember row F11B012L52) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B012L53_lift (row : List GridPoint) (h : FamilyMember row F11B012L53) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B012L54_lift (row : List GridPoint) (h : FamilyMember row F11B012L54) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B012L55_lift (row : List GridPoint) (h : FamilyMember row F11B012L55) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B012L56_lift (row : List GridPoint) (h : FamilyMember row F11B012L56) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B012L57_lift (row : List GridPoint) (h : FamilyMember row F11B012L57) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B012L58_lift (row : List GridPoint) (h : FamilyMember row F11B012L58) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B012L59_lift (row : List GridPoint) (h : FamilyMember row F11B012L59) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B012L60_lift (row : List GridPoint) (h : FamilyMember row F11B012L60) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B012L61_lift (row : List GridPoint) (h : FamilyMember row F11B012L61) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B012L62_lift (row : List GridPoint) (h : FamilyMember row F11B012L62) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B012L63_lift (row : List GridPoint) (h : FamilyMember row F11B012L63) : FamilyMember row F11B012 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
