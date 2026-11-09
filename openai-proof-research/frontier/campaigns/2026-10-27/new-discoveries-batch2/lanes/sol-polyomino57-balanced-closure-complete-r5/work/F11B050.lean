import TreeBlock050
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B050L0 : RowFamilyTree := TreeBlock050L0
abbrev F11B050L1 : RowFamilyTree := TreeBlock050L1
abbrev F11B050L2 : RowFamilyTree := TreeBlock050L2
abbrev F11B050L3 : RowFamilyTree := TreeBlock050L3
abbrev F11B050L4 : RowFamilyTree := TreeBlock050L4
abbrev F11B050L5 : RowFamilyTree := TreeBlock050L5
abbrev F11B050L6 : RowFamilyTree := TreeBlock050L6
abbrev F11B050L7 : RowFamilyTree := TreeBlock050L7
abbrev F11B050L8 : RowFamilyTree := TreeBlock050L8
abbrev F11B050L9 : RowFamilyTree := TreeBlock050L9
abbrev F11B050L10 : RowFamilyTree := TreeBlock050L10
abbrev F11B050L11 : RowFamilyTree := TreeBlock050L11
abbrev F11B050L12 : RowFamilyTree := TreeBlock050L12
abbrev F11B050L13 : RowFamilyTree := TreeBlock050L13
abbrev F11B050L14 : RowFamilyTree := TreeBlock050L14
abbrev F11B050L15 : RowFamilyTree := TreeBlock050L15
abbrev F11B050L16 : RowFamilyTree := TreeBlock050L16
abbrev F11B050L17 : RowFamilyTree := TreeBlock050L17
abbrev F11B050L18 : RowFamilyTree := TreeBlock050L18
abbrev F11B050L19 : RowFamilyTree := TreeBlock050L19
abbrev F11B050L20 : RowFamilyTree := TreeBlock050L20
abbrev F11B050L21 : RowFamilyTree := TreeBlock050L21
abbrev F11B050L22 : RowFamilyTree := TreeBlock050L22
abbrev F11B050L23 : RowFamilyTree := TreeBlock050L23
abbrev F11B050L24 : RowFamilyTree := TreeBlock050L24
abbrev F11B050L25 : RowFamilyTree := TreeBlock050L25
abbrev F11B050L26 : RowFamilyTree := TreeBlock050L26
abbrev F11B050L27 : RowFamilyTree := TreeBlock050L27
abbrev F11B050L28 : RowFamilyTree := TreeBlock050L28
abbrev F11B050L29 : RowFamilyTree := TreeBlock050L29
abbrev F11B050L30 : RowFamilyTree := TreeBlock050L30
abbrev F11B050L31 : RowFamilyTree := TreeBlock050L31
abbrev F11B050L32 : RowFamilyTree := TreeBlock050L32
abbrev F11B050L33 : RowFamilyTree := TreeBlock050L33
abbrev F11B050L34 : RowFamilyTree := TreeBlock050L34
abbrev F11B050L35 : RowFamilyTree := TreeBlock050L35
abbrev F11B050L36 : RowFamilyTree := TreeBlock050L36
abbrev F11B050L37 : RowFamilyTree := TreeBlock050L37
abbrev F11B050L38 : RowFamilyTree := TreeBlock050L38
abbrev F11B050L39 : RowFamilyTree := TreeBlock050L39
abbrev F11B050L40 : RowFamilyTree := TreeBlock050L40
abbrev F11B050L41 : RowFamilyTree := TreeBlock050L41
abbrev F11B050L42 : RowFamilyTree := TreeBlock050L42
abbrev F11B050L43 : RowFamilyTree := TreeBlock050L43
abbrev F11B050L44 : RowFamilyTree := TreeBlock050L44
abbrev F11B050L45 : RowFamilyTree := TreeBlock050L45
abbrev F11B050L46 : RowFamilyTree := TreeBlock050L46
abbrev F11B050L47 : RowFamilyTree := TreeBlock050L47
abbrev F11B050L48 : RowFamilyTree := TreeBlock050L48
abbrev F11B050L49 : RowFamilyTree := TreeBlock050L49
abbrev F11B050L50 : RowFamilyTree := TreeBlock050L50
abbrev F11B050L51 : RowFamilyTree := TreeBlock050L51
abbrev F11B050L52 : RowFamilyTree := TreeBlock050L52
abbrev F11B050L53 : RowFamilyTree := TreeBlock050L53
abbrev F11B050L54 : RowFamilyTree := TreeBlock050L54
abbrev F11B050L55 : RowFamilyTree := TreeBlock050L55
abbrev F11B050L56 : RowFamilyTree := TreeBlock050L56
abbrev F11B050L57 : RowFamilyTree := TreeBlock050L57
abbrev F11B050L58 : RowFamilyTree := TreeBlock050L58
abbrev F11B050L59 : RowFamilyTree := TreeBlock050L59
abbrev F11B050L60 : RowFamilyTree := TreeBlock050L60
abbrev F11B050L61 : RowFamilyTree := TreeBlock050L61
abbrev F11B050L62 : RowFamilyTree := TreeBlock050L62
abbrev F11B050L63 : RowFamilyTree := TreeBlock050L63
abbrev F11B050 : RowFamilyTree := TreeBlock050
theorem F11B050L0_lift (row : List GridPoint) (h : FamilyMember row F11B050L0) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B050L1_lift (row : List GridPoint) (h : FamilyMember row F11B050L1) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B050L2_lift (row : List GridPoint) (h : FamilyMember row F11B050L2) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B050L3_lift (row : List GridPoint) (h : FamilyMember row F11B050L3) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B050L4_lift (row : List GridPoint) (h : FamilyMember row F11B050L4) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B050L5_lift (row : List GridPoint) (h : FamilyMember row F11B050L5) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B050L6_lift (row : List GridPoint) (h : FamilyMember row F11B050L6) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B050L7_lift (row : List GridPoint) (h : FamilyMember row F11B050L7) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B050L8_lift (row : List GridPoint) (h : FamilyMember row F11B050L8) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B050L9_lift (row : List GridPoint) (h : FamilyMember row F11B050L9) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B050L10_lift (row : List GridPoint) (h : FamilyMember row F11B050L10) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B050L11_lift (row : List GridPoint) (h : FamilyMember row F11B050L11) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B050L12_lift (row : List GridPoint) (h : FamilyMember row F11B050L12) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B050L13_lift (row : List GridPoint) (h : FamilyMember row F11B050L13) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B050L14_lift (row : List GridPoint) (h : FamilyMember row F11B050L14) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B050L15_lift (row : List GridPoint) (h : FamilyMember row F11B050L15) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B050L16_lift (row : List GridPoint) (h : FamilyMember row F11B050L16) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B050L17_lift (row : List GridPoint) (h : FamilyMember row F11B050L17) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B050L18_lift (row : List GridPoint) (h : FamilyMember row F11B050L18) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B050L19_lift (row : List GridPoint) (h : FamilyMember row F11B050L19) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B050L20_lift (row : List GridPoint) (h : FamilyMember row F11B050L20) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B050L21_lift (row : List GridPoint) (h : FamilyMember row F11B050L21) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B050L22_lift (row : List GridPoint) (h : FamilyMember row F11B050L22) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B050L23_lift (row : List GridPoint) (h : FamilyMember row F11B050L23) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B050L24_lift (row : List GridPoint) (h : FamilyMember row F11B050L24) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B050L25_lift (row : List GridPoint) (h : FamilyMember row F11B050L25) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B050L26_lift (row : List GridPoint) (h : FamilyMember row F11B050L26) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B050L27_lift (row : List GridPoint) (h : FamilyMember row F11B050L27) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B050L28_lift (row : List GridPoint) (h : FamilyMember row F11B050L28) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B050L29_lift (row : List GridPoint) (h : FamilyMember row F11B050L29) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B050L30_lift (row : List GridPoint) (h : FamilyMember row F11B050L30) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B050L31_lift (row : List GridPoint) (h : FamilyMember row F11B050L31) : FamilyMember row F11B050 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B050L32_lift (row : List GridPoint) (h : FamilyMember row F11B050L32) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B050L33_lift (row : List GridPoint) (h : FamilyMember row F11B050L33) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B050L34_lift (row : List GridPoint) (h : FamilyMember row F11B050L34) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B050L35_lift (row : List GridPoint) (h : FamilyMember row F11B050L35) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B050L36_lift (row : List GridPoint) (h : FamilyMember row F11B050L36) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B050L37_lift (row : List GridPoint) (h : FamilyMember row F11B050L37) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B050L38_lift (row : List GridPoint) (h : FamilyMember row F11B050L38) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B050L39_lift (row : List GridPoint) (h : FamilyMember row F11B050L39) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B050L40_lift (row : List GridPoint) (h : FamilyMember row F11B050L40) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B050L41_lift (row : List GridPoint) (h : FamilyMember row F11B050L41) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B050L42_lift (row : List GridPoint) (h : FamilyMember row F11B050L42) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B050L43_lift (row : List GridPoint) (h : FamilyMember row F11B050L43) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B050L44_lift (row : List GridPoint) (h : FamilyMember row F11B050L44) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B050L45_lift (row : List GridPoint) (h : FamilyMember row F11B050L45) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B050L46_lift (row : List GridPoint) (h : FamilyMember row F11B050L46) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B050L47_lift (row : List GridPoint) (h : FamilyMember row F11B050L47) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B050L48_lift (row : List GridPoint) (h : FamilyMember row F11B050L48) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B050L49_lift (row : List GridPoint) (h : FamilyMember row F11B050L49) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B050L50_lift (row : List GridPoint) (h : FamilyMember row F11B050L50) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B050L51_lift (row : List GridPoint) (h : FamilyMember row F11B050L51) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B050L52_lift (row : List GridPoint) (h : FamilyMember row F11B050L52) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B050L53_lift (row : List GridPoint) (h : FamilyMember row F11B050L53) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B050L54_lift (row : List GridPoint) (h : FamilyMember row F11B050L54) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B050L55_lift (row : List GridPoint) (h : FamilyMember row F11B050L55) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B050L56_lift (row : List GridPoint) (h : FamilyMember row F11B050L56) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B050L57_lift (row : List GridPoint) (h : FamilyMember row F11B050L57) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B050L58_lift (row : List GridPoint) (h : FamilyMember row F11B050L58) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B050L59_lift (row : List GridPoint) (h : FamilyMember row F11B050L59) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B050L60_lift (row : List GridPoint) (h : FamilyMember row F11B050L60) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B050L61_lift (row : List GridPoint) (h : FamilyMember row F11B050L61) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B050L62_lift (row : List GridPoint) (h : FamilyMember row F11B050L62) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B050L63_lift (row : List GridPoint) (h : FamilyMember row F11B050L63) : FamilyMember row F11B050 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
