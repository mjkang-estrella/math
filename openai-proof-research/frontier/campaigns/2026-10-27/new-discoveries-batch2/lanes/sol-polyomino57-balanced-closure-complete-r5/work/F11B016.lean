import TreeBlock016
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B016L0 : RowFamilyTree := TreeBlock016L0
abbrev F11B016L1 : RowFamilyTree := TreeBlock016L1
abbrev F11B016L2 : RowFamilyTree := TreeBlock016L2
abbrev F11B016L3 : RowFamilyTree := TreeBlock016L3
abbrev F11B016L4 : RowFamilyTree := TreeBlock016L4
abbrev F11B016L5 : RowFamilyTree := TreeBlock016L5
abbrev F11B016L6 : RowFamilyTree := TreeBlock016L6
abbrev F11B016L7 : RowFamilyTree := TreeBlock016L7
abbrev F11B016L8 : RowFamilyTree := TreeBlock016L8
abbrev F11B016L9 : RowFamilyTree := TreeBlock016L9
abbrev F11B016L10 : RowFamilyTree := TreeBlock016L10
abbrev F11B016L11 : RowFamilyTree := TreeBlock016L11
abbrev F11B016L12 : RowFamilyTree := TreeBlock016L12
abbrev F11B016L13 : RowFamilyTree := TreeBlock016L13
abbrev F11B016L14 : RowFamilyTree := TreeBlock016L14
abbrev F11B016L15 : RowFamilyTree := TreeBlock016L15
abbrev F11B016L16 : RowFamilyTree := TreeBlock016L16
abbrev F11B016L17 : RowFamilyTree := TreeBlock016L17
abbrev F11B016L18 : RowFamilyTree := TreeBlock016L18
abbrev F11B016L19 : RowFamilyTree := TreeBlock016L19
abbrev F11B016L20 : RowFamilyTree := TreeBlock016L20
abbrev F11B016L21 : RowFamilyTree := TreeBlock016L21
abbrev F11B016L22 : RowFamilyTree := TreeBlock016L22
abbrev F11B016L23 : RowFamilyTree := TreeBlock016L23
abbrev F11B016L24 : RowFamilyTree := TreeBlock016L24
abbrev F11B016L25 : RowFamilyTree := TreeBlock016L25
abbrev F11B016L26 : RowFamilyTree := TreeBlock016L26
abbrev F11B016L27 : RowFamilyTree := TreeBlock016L27
abbrev F11B016L28 : RowFamilyTree := TreeBlock016L28
abbrev F11B016L29 : RowFamilyTree := TreeBlock016L29
abbrev F11B016L30 : RowFamilyTree := TreeBlock016L30
abbrev F11B016L31 : RowFamilyTree := TreeBlock016L31
abbrev F11B016L32 : RowFamilyTree := TreeBlock016L32
abbrev F11B016L33 : RowFamilyTree := TreeBlock016L33
abbrev F11B016L34 : RowFamilyTree := TreeBlock016L34
abbrev F11B016L35 : RowFamilyTree := TreeBlock016L35
abbrev F11B016L36 : RowFamilyTree := TreeBlock016L36
abbrev F11B016L37 : RowFamilyTree := TreeBlock016L37
abbrev F11B016L38 : RowFamilyTree := TreeBlock016L38
abbrev F11B016L39 : RowFamilyTree := TreeBlock016L39
abbrev F11B016L40 : RowFamilyTree := TreeBlock016L40
abbrev F11B016L41 : RowFamilyTree := TreeBlock016L41
abbrev F11B016L42 : RowFamilyTree := TreeBlock016L42
abbrev F11B016L43 : RowFamilyTree := TreeBlock016L43
abbrev F11B016L44 : RowFamilyTree := TreeBlock016L44
abbrev F11B016L45 : RowFamilyTree := TreeBlock016L45
abbrev F11B016L46 : RowFamilyTree := TreeBlock016L46
abbrev F11B016L47 : RowFamilyTree := TreeBlock016L47
abbrev F11B016L48 : RowFamilyTree := TreeBlock016L48
abbrev F11B016L49 : RowFamilyTree := TreeBlock016L49
abbrev F11B016L50 : RowFamilyTree := TreeBlock016L50
abbrev F11B016L51 : RowFamilyTree := TreeBlock016L51
abbrev F11B016L52 : RowFamilyTree := TreeBlock016L52
abbrev F11B016L53 : RowFamilyTree := TreeBlock016L53
abbrev F11B016L54 : RowFamilyTree := TreeBlock016L54
abbrev F11B016L55 : RowFamilyTree := TreeBlock016L55
abbrev F11B016L56 : RowFamilyTree := TreeBlock016L56
abbrev F11B016L57 : RowFamilyTree := TreeBlock016L57
abbrev F11B016L58 : RowFamilyTree := TreeBlock016L58
abbrev F11B016L59 : RowFamilyTree := TreeBlock016L59
abbrev F11B016L60 : RowFamilyTree := TreeBlock016L60
abbrev F11B016L61 : RowFamilyTree := TreeBlock016L61
abbrev F11B016L62 : RowFamilyTree := TreeBlock016L62
abbrev F11B016L63 : RowFamilyTree := TreeBlock016L63
abbrev F11B016 : RowFamilyTree := TreeBlock016
theorem F11B016L0_lift (row : List GridPoint) (h : FamilyMember row F11B016L0) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B016L1_lift (row : List GridPoint) (h : FamilyMember row F11B016L1) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B016L2_lift (row : List GridPoint) (h : FamilyMember row F11B016L2) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B016L3_lift (row : List GridPoint) (h : FamilyMember row F11B016L3) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B016L4_lift (row : List GridPoint) (h : FamilyMember row F11B016L4) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B016L5_lift (row : List GridPoint) (h : FamilyMember row F11B016L5) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B016L6_lift (row : List GridPoint) (h : FamilyMember row F11B016L6) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B016L7_lift (row : List GridPoint) (h : FamilyMember row F11B016L7) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B016L8_lift (row : List GridPoint) (h : FamilyMember row F11B016L8) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B016L9_lift (row : List GridPoint) (h : FamilyMember row F11B016L9) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B016L10_lift (row : List GridPoint) (h : FamilyMember row F11B016L10) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B016L11_lift (row : List GridPoint) (h : FamilyMember row F11B016L11) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B016L12_lift (row : List GridPoint) (h : FamilyMember row F11B016L12) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B016L13_lift (row : List GridPoint) (h : FamilyMember row F11B016L13) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B016L14_lift (row : List GridPoint) (h : FamilyMember row F11B016L14) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B016L15_lift (row : List GridPoint) (h : FamilyMember row F11B016L15) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B016L16_lift (row : List GridPoint) (h : FamilyMember row F11B016L16) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B016L17_lift (row : List GridPoint) (h : FamilyMember row F11B016L17) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B016L18_lift (row : List GridPoint) (h : FamilyMember row F11B016L18) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B016L19_lift (row : List GridPoint) (h : FamilyMember row F11B016L19) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B016L20_lift (row : List GridPoint) (h : FamilyMember row F11B016L20) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B016L21_lift (row : List GridPoint) (h : FamilyMember row F11B016L21) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B016L22_lift (row : List GridPoint) (h : FamilyMember row F11B016L22) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B016L23_lift (row : List GridPoint) (h : FamilyMember row F11B016L23) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B016L24_lift (row : List GridPoint) (h : FamilyMember row F11B016L24) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B016L25_lift (row : List GridPoint) (h : FamilyMember row F11B016L25) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B016L26_lift (row : List GridPoint) (h : FamilyMember row F11B016L26) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B016L27_lift (row : List GridPoint) (h : FamilyMember row F11B016L27) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B016L28_lift (row : List GridPoint) (h : FamilyMember row F11B016L28) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B016L29_lift (row : List GridPoint) (h : FamilyMember row F11B016L29) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B016L30_lift (row : List GridPoint) (h : FamilyMember row F11B016L30) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B016L31_lift (row : List GridPoint) (h : FamilyMember row F11B016L31) : FamilyMember row F11B016 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B016L32_lift (row : List GridPoint) (h : FamilyMember row F11B016L32) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B016L33_lift (row : List GridPoint) (h : FamilyMember row F11B016L33) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B016L34_lift (row : List GridPoint) (h : FamilyMember row F11B016L34) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B016L35_lift (row : List GridPoint) (h : FamilyMember row F11B016L35) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B016L36_lift (row : List GridPoint) (h : FamilyMember row F11B016L36) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B016L37_lift (row : List GridPoint) (h : FamilyMember row F11B016L37) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B016L38_lift (row : List GridPoint) (h : FamilyMember row F11B016L38) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B016L39_lift (row : List GridPoint) (h : FamilyMember row F11B016L39) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B016L40_lift (row : List GridPoint) (h : FamilyMember row F11B016L40) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B016L41_lift (row : List GridPoint) (h : FamilyMember row F11B016L41) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B016L42_lift (row : List GridPoint) (h : FamilyMember row F11B016L42) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B016L43_lift (row : List GridPoint) (h : FamilyMember row F11B016L43) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B016L44_lift (row : List GridPoint) (h : FamilyMember row F11B016L44) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B016L45_lift (row : List GridPoint) (h : FamilyMember row F11B016L45) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B016L46_lift (row : List GridPoint) (h : FamilyMember row F11B016L46) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B016L47_lift (row : List GridPoint) (h : FamilyMember row F11B016L47) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B016L48_lift (row : List GridPoint) (h : FamilyMember row F11B016L48) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B016L49_lift (row : List GridPoint) (h : FamilyMember row F11B016L49) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B016L50_lift (row : List GridPoint) (h : FamilyMember row F11B016L50) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B016L51_lift (row : List GridPoint) (h : FamilyMember row F11B016L51) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B016L52_lift (row : List GridPoint) (h : FamilyMember row F11B016L52) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B016L53_lift (row : List GridPoint) (h : FamilyMember row F11B016L53) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B016L54_lift (row : List GridPoint) (h : FamilyMember row F11B016L54) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B016L55_lift (row : List GridPoint) (h : FamilyMember row F11B016L55) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B016L56_lift (row : List GridPoint) (h : FamilyMember row F11B016L56) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B016L57_lift (row : List GridPoint) (h : FamilyMember row F11B016L57) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B016L58_lift (row : List GridPoint) (h : FamilyMember row F11B016L58) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B016L59_lift (row : List GridPoint) (h : FamilyMember row F11B016L59) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B016L60_lift (row : List GridPoint) (h : FamilyMember row F11B016L60) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B016L61_lift (row : List GridPoint) (h : FamilyMember row F11B016L61) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B016L62_lift (row : List GridPoint) (h : FamilyMember row F11B016L62) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B016L63_lift (row : List GridPoint) (h : FamilyMember row F11B016L63) : FamilyMember row F11B016 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
