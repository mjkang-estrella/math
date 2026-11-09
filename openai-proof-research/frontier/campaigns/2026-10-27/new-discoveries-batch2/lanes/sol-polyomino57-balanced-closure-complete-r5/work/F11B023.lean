import TreeBlock023
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B023L0 : RowFamilyTree := TreeBlock023L0
abbrev F11B023L1 : RowFamilyTree := TreeBlock023L1
abbrev F11B023L2 : RowFamilyTree := TreeBlock023L2
abbrev F11B023L3 : RowFamilyTree := TreeBlock023L3
abbrev F11B023L4 : RowFamilyTree := TreeBlock023L4
abbrev F11B023L5 : RowFamilyTree := TreeBlock023L5
abbrev F11B023L6 : RowFamilyTree := TreeBlock023L6
abbrev F11B023L7 : RowFamilyTree := TreeBlock023L7
abbrev F11B023L8 : RowFamilyTree := TreeBlock023L8
abbrev F11B023L9 : RowFamilyTree := TreeBlock023L9
abbrev F11B023L10 : RowFamilyTree := TreeBlock023L10
abbrev F11B023L11 : RowFamilyTree := TreeBlock023L11
abbrev F11B023L12 : RowFamilyTree := TreeBlock023L12
abbrev F11B023L13 : RowFamilyTree := TreeBlock023L13
abbrev F11B023L14 : RowFamilyTree := TreeBlock023L14
abbrev F11B023L15 : RowFamilyTree := TreeBlock023L15
abbrev F11B023L16 : RowFamilyTree := TreeBlock023L16
abbrev F11B023L17 : RowFamilyTree := TreeBlock023L17
abbrev F11B023L18 : RowFamilyTree := TreeBlock023L18
abbrev F11B023L19 : RowFamilyTree := TreeBlock023L19
abbrev F11B023L20 : RowFamilyTree := TreeBlock023L20
abbrev F11B023L21 : RowFamilyTree := TreeBlock023L21
abbrev F11B023L22 : RowFamilyTree := TreeBlock023L22
abbrev F11B023L23 : RowFamilyTree := TreeBlock023L23
abbrev F11B023L24 : RowFamilyTree := TreeBlock023L24
abbrev F11B023L25 : RowFamilyTree := TreeBlock023L25
abbrev F11B023L26 : RowFamilyTree := TreeBlock023L26
abbrev F11B023L27 : RowFamilyTree := TreeBlock023L27
abbrev F11B023L28 : RowFamilyTree := TreeBlock023L28
abbrev F11B023L29 : RowFamilyTree := TreeBlock023L29
abbrev F11B023L30 : RowFamilyTree := TreeBlock023L30
abbrev F11B023L31 : RowFamilyTree := TreeBlock023L31
abbrev F11B023L32 : RowFamilyTree := TreeBlock023L32
abbrev F11B023L33 : RowFamilyTree := TreeBlock023L33
abbrev F11B023L34 : RowFamilyTree := TreeBlock023L34
abbrev F11B023L35 : RowFamilyTree := TreeBlock023L35
abbrev F11B023L36 : RowFamilyTree := TreeBlock023L36
abbrev F11B023L37 : RowFamilyTree := TreeBlock023L37
abbrev F11B023L38 : RowFamilyTree := TreeBlock023L38
abbrev F11B023L39 : RowFamilyTree := TreeBlock023L39
abbrev F11B023L40 : RowFamilyTree := TreeBlock023L40
abbrev F11B023L41 : RowFamilyTree := TreeBlock023L41
abbrev F11B023L42 : RowFamilyTree := TreeBlock023L42
abbrev F11B023L43 : RowFamilyTree := TreeBlock023L43
abbrev F11B023L44 : RowFamilyTree := TreeBlock023L44
abbrev F11B023L45 : RowFamilyTree := TreeBlock023L45
abbrev F11B023L46 : RowFamilyTree := TreeBlock023L46
abbrev F11B023L47 : RowFamilyTree := TreeBlock023L47
abbrev F11B023L48 : RowFamilyTree := TreeBlock023L48
abbrev F11B023L49 : RowFamilyTree := TreeBlock023L49
abbrev F11B023L50 : RowFamilyTree := TreeBlock023L50
abbrev F11B023L51 : RowFamilyTree := TreeBlock023L51
abbrev F11B023L52 : RowFamilyTree := TreeBlock023L52
abbrev F11B023L53 : RowFamilyTree := TreeBlock023L53
abbrev F11B023L54 : RowFamilyTree := TreeBlock023L54
abbrev F11B023L55 : RowFamilyTree := TreeBlock023L55
abbrev F11B023L56 : RowFamilyTree := TreeBlock023L56
abbrev F11B023L57 : RowFamilyTree := TreeBlock023L57
abbrev F11B023L58 : RowFamilyTree := TreeBlock023L58
abbrev F11B023L59 : RowFamilyTree := TreeBlock023L59
abbrev F11B023L60 : RowFamilyTree := TreeBlock023L60
abbrev F11B023L61 : RowFamilyTree := TreeBlock023L61
abbrev F11B023L62 : RowFamilyTree := TreeBlock023L62
abbrev F11B023L63 : RowFamilyTree := TreeBlock023L63
abbrev F11B023 : RowFamilyTree := TreeBlock023
theorem F11B023L0_lift (row : List GridPoint) (h : FamilyMember row F11B023L0) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B023L1_lift (row : List GridPoint) (h : FamilyMember row F11B023L1) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B023L2_lift (row : List GridPoint) (h : FamilyMember row F11B023L2) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B023L3_lift (row : List GridPoint) (h : FamilyMember row F11B023L3) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B023L4_lift (row : List GridPoint) (h : FamilyMember row F11B023L4) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B023L5_lift (row : List GridPoint) (h : FamilyMember row F11B023L5) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B023L6_lift (row : List GridPoint) (h : FamilyMember row F11B023L6) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B023L7_lift (row : List GridPoint) (h : FamilyMember row F11B023L7) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B023L8_lift (row : List GridPoint) (h : FamilyMember row F11B023L8) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B023L9_lift (row : List GridPoint) (h : FamilyMember row F11B023L9) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B023L10_lift (row : List GridPoint) (h : FamilyMember row F11B023L10) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B023L11_lift (row : List GridPoint) (h : FamilyMember row F11B023L11) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B023L12_lift (row : List GridPoint) (h : FamilyMember row F11B023L12) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B023L13_lift (row : List GridPoint) (h : FamilyMember row F11B023L13) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B023L14_lift (row : List GridPoint) (h : FamilyMember row F11B023L14) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B023L15_lift (row : List GridPoint) (h : FamilyMember row F11B023L15) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B023L16_lift (row : List GridPoint) (h : FamilyMember row F11B023L16) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B023L17_lift (row : List GridPoint) (h : FamilyMember row F11B023L17) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B023L18_lift (row : List GridPoint) (h : FamilyMember row F11B023L18) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B023L19_lift (row : List GridPoint) (h : FamilyMember row F11B023L19) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B023L20_lift (row : List GridPoint) (h : FamilyMember row F11B023L20) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B023L21_lift (row : List GridPoint) (h : FamilyMember row F11B023L21) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B023L22_lift (row : List GridPoint) (h : FamilyMember row F11B023L22) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B023L23_lift (row : List GridPoint) (h : FamilyMember row F11B023L23) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B023L24_lift (row : List GridPoint) (h : FamilyMember row F11B023L24) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B023L25_lift (row : List GridPoint) (h : FamilyMember row F11B023L25) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B023L26_lift (row : List GridPoint) (h : FamilyMember row F11B023L26) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B023L27_lift (row : List GridPoint) (h : FamilyMember row F11B023L27) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B023L28_lift (row : List GridPoint) (h : FamilyMember row F11B023L28) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B023L29_lift (row : List GridPoint) (h : FamilyMember row F11B023L29) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B023L30_lift (row : List GridPoint) (h : FamilyMember row F11B023L30) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B023L31_lift (row : List GridPoint) (h : FamilyMember row F11B023L31) : FamilyMember row F11B023 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B023L32_lift (row : List GridPoint) (h : FamilyMember row F11B023L32) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B023L33_lift (row : List GridPoint) (h : FamilyMember row F11B023L33) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B023L34_lift (row : List GridPoint) (h : FamilyMember row F11B023L34) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B023L35_lift (row : List GridPoint) (h : FamilyMember row F11B023L35) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B023L36_lift (row : List GridPoint) (h : FamilyMember row F11B023L36) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B023L37_lift (row : List GridPoint) (h : FamilyMember row F11B023L37) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B023L38_lift (row : List GridPoint) (h : FamilyMember row F11B023L38) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B023L39_lift (row : List GridPoint) (h : FamilyMember row F11B023L39) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B023L40_lift (row : List GridPoint) (h : FamilyMember row F11B023L40) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B023L41_lift (row : List GridPoint) (h : FamilyMember row F11B023L41) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B023L42_lift (row : List GridPoint) (h : FamilyMember row F11B023L42) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B023L43_lift (row : List GridPoint) (h : FamilyMember row F11B023L43) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B023L44_lift (row : List GridPoint) (h : FamilyMember row F11B023L44) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B023L45_lift (row : List GridPoint) (h : FamilyMember row F11B023L45) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B023L46_lift (row : List GridPoint) (h : FamilyMember row F11B023L46) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B023L47_lift (row : List GridPoint) (h : FamilyMember row F11B023L47) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B023L48_lift (row : List GridPoint) (h : FamilyMember row F11B023L48) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B023L49_lift (row : List GridPoint) (h : FamilyMember row F11B023L49) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B023L50_lift (row : List GridPoint) (h : FamilyMember row F11B023L50) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B023L51_lift (row : List GridPoint) (h : FamilyMember row F11B023L51) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B023L52_lift (row : List GridPoint) (h : FamilyMember row F11B023L52) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B023L53_lift (row : List GridPoint) (h : FamilyMember row F11B023L53) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B023L54_lift (row : List GridPoint) (h : FamilyMember row F11B023L54) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B023L55_lift (row : List GridPoint) (h : FamilyMember row F11B023L55) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B023L56_lift (row : List GridPoint) (h : FamilyMember row F11B023L56) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B023L57_lift (row : List GridPoint) (h : FamilyMember row F11B023L57) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B023L58_lift (row : List GridPoint) (h : FamilyMember row F11B023L58) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B023L59_lift (row : List GridPoint) (h : FamilyMember row F11B023L59) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B023L60_lift (row : List GridPoint) (h : FamilyMember row F11B023L60) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B023L61_lift (row : List GridPoint) (h : FamilyMember row F11B023L61) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B023L62_lift (row : List GridPoint) (h : FamilyMember row F11B023L62) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B023L63_lift (row : List GridPoint) (h : FamilyMember row F11B023L63) : FamilyMember row F11B023 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
