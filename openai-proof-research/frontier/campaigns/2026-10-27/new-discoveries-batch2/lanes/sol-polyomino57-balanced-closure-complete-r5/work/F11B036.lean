import TreeBlock036
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B036L0 : RowFamilyTree := TreeBlock036L0
abbrev F11B036L1 : RowFamilyTree := TreeBlock036L1
abbrev F11B036L2 : RowFamilyTree := TreeBlock036L2
abbrev F11B036L3 : RowFamilyTree := TreeBlock036L3
abbrev F11B036L4 : RowFamilyTree := TreeBlock036L4
abbrev F11B036L5 : RowFamilyTree := TreeBlock036L5
abbrev F11B036L6 : RowFamilyTree := TreeBlock036L6
abbrev F11B036L7 : RowFamilyTree := TreeBlock036L7
abbrev F11B036L8 : RowFamilyTree := TreeBlock036L8
abbrev F11B036L9 : RowFamilyTree := TreeBlock036L9
abbrev F11B036L10 : RowFamilyTree := TreeBlock036L10
abbrev F11B036L11 : RowFamilyTree := TreeBlock036L11
abbrev F11B036L12 : RowFamilyTree := TreeBlock036L12
abbrev F11B036L13 : RowFamilyTree := TreeBlock036L13
abbrev F11B036L14 : RowFamilyTree := TreeBlock036L14
abbrev F11B036L15 : RowFamilyTree := TreeBlock036L15
abbrev F11B036L16 : RowFamilyTree := TreeBlock036L16
abbrev F11B036L17 : RowFamilyTree := TreeBlock036L17
abbrev F11B036L18 : RowFamilyTree := TreeBlock036L18
abbrev F11B036L19 : RowFamilyTree := TreeBlock036L19
abbrev F11B036L20 : RowFamilyTree := TreeBlock036L20
abbrev F11B036L21 : RowFamilyTree := TreeBlock036L21
abbrev F11B036L22 : RowFamilyTree := TreeBlock036L22
abbrev F11B036L23 : RowFamilyTree := TreeBlock036L23
abbrev F11B036L24 : RowFamilyTree := TreeBlock036L24
abbrev F11B036L25 : RowFamilyTree := TreeBlock036L25
abbrev F11B036L26 : RowFamilyTree := TreeBlock036L26
abbrev F11B036L27 : RowFamilyTree := TreeBlock036L27
abbrev F11B036L28 : RowFamilyTree := TreeBlock036L28
abbrev F11B036L29 : RowFamilyTree := TreeBlock036L29
abbrev F11B036L30 : RowFamilyTree := TreeBlock036L30
abbrev F11B036L31 : RowFamilyTree := TreeBlock036L31
abbrev F11B036L32 : RowFamilyTree := TreeBlock036L32
abbrev F11B036L33 : RowFamilyTree := TreeBlock036L33
abbrev F11B036L34 : RowFamilyTree := TreeBlock036L34
abbrev F11B036L35 : RowFamilyTree := TreeBlock036L35
abbrev F11B036L36 : RowFamilyTree := TreeBlock036L36
abbrev F11B036L37 : RowFamilyTree := TreeBlock036L37
abbrev F11B036L38 : RowFamilyTree := TreeBlock036L38
abbrev F11B036L39 : RowFamilyTree := TreeBlock036L39
abbrev F11B036L40 : RowFamilyTree := TreeBlock036L40
abbrev F11B036L41 : RowFamilyTree := TreeBlock036L41
abbrev F11B036L42 : RowFamilyTree := TreeBlock036L42
abbrev F11B036L43 : RowFamilyTree := TreeBlock036L43
abbrev F11B036L44 : RowFamilyTree := TreeBlock036L44
abbrev F11B036L45 : RowFamilyTree := TreeBlock036L45
abbrev F11B036L46 : RowFamilyTree := TreeBlock036L46
abbrev F11B036L47 : RowFamilyTree := TreeBlock036L47
abbrev F11B036L48 : RowFamilyTree := TreeBlock036L48
abbrev F11B036L49 : RowFamilyTree := TreeBlock036L49
abbrev F11B036L50 : RowFamilyTree := TreeBlock036L50
abbrev F11B036L51 : RowFamilyTree := TreeBlock036L51
abbrev F11B036L52 : RowFamilyTree := TreeBlock036L52
abbrev F11B036L53 : RowFamilyTree := TreeBlock036L53
abbrev F11B036L54 : RowFamilyTree := TreeBlock036L54
abbrev F11B036L55 : RowFamilyTree := TreeBlock036L55
abbrev F11B036L56 : RowFamilyTree := TreeBlock036L56
abbrev F11B036L57 : RowFamilyTree := TreeBlock036L57
abbrev F11B036L58 : RowFamilyTree := TreeBlock036L58
abbrev F11B036L59 : RowFamilyTree := TreeBlock036L59
abbrev F11B036L60 : RowFamilyTree := TreeBlock036L60
abbrev F11B036L61 : RowFamilyTree := TreeBlock036L61
abbrev F11B036L62 : RowFamilyTree := TreeBlock036L62
abbrev F11B036L63 : RowFamilyTree := TreeBlock036L63
abbrev F11B036 : RowFamilyTree := TreeBlock036
theorem F11B036L0_lift (row : List GridPoint) (h : FamilyMember row F11B036L0) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B036L1_lift (row : List GridPoint) (h : FamilyMember row F11B036L1) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B036L2_lift (row : List GridPoint) (h : FamilyMember row F11B036L2) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B036L3_lift (row : List GridPoint) (h : FamilyMember row F11B036L3) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B036L4_lift (row : List GridPoint) (h : FamilyMember row F11B036L4) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B036L5_lift (row : List GridPoint) (h : FamilyMember row F11B036L5) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B036L6_lift (row : List GridPoint) (h : FamilyMember row F11B036L6) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B036L7_lift (row : List GridPoint) (h : FamilyMember row F11B036L7) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B036L8_lift (row : List GridPoint) (h : FamilyMember row F11B036L8) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B036L9_lift (row : List GridPoint) (h : FamilyMember row F11B036L9) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B036L10_lift (row : List GridPoint) (h : FamilyMember row F11B036L10) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B036L11_lift (row : List GridPoint) (h : FamilyMember row F11B036L11) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B036L12_lift (row : List GridPoint) (h : FamilyMember row F11B036L12) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B036L13_lift (row : List GridPoint) (h : FamilyMember row F11B036L13) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B036L14_lift (row : List GridPoint) (h : FamilyMember row F11B036L14) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B036L15_lift (row : List GridPoint) (h : FamilyMember row F11B036L15) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B036L16_lift (row : List GridPoint) (h : FamilyMember row F11B036L16) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B036L17_lift (row : List GridPoint) (h : FamilyMember row F11B036L17) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B036L18_lift (row : List GridPoint) (h : FamilyMember row F11B036L18) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B036L19_lift (row : List GridPoint) (h : FamilyMember row F11B036L19) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B036L20_lift (row : List GridPoint) (h : FamilyMember row F11B036L20) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B036L21_lift (row : List GridPoint) (h : FamilyMember row F11B036L21) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B036L22_lift (row : List GridPoint) (h : FamilyMember row F11B036L22) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B036L23_lift (row : List GridPoint) (h : FamilyMember row F11B036L23) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B036L24_lift (row : List GridPoint) (h : FamilyMember row F11B036L24) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B036L25_lift (row : List GridPoint) (h : FamilyMember row F11B036L25) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B036L26_lift (row : List GridPoint) (h : FamilyMember row F11B036L26) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B036L27_lift (row : List GridPoint) (h : FamilyMember row F11B036L27) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B036L28_lift (row : List GridPoint) (h : FamilyMember row F11B036L28) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B036L29_lift (row : List GridPoint) (h : FamilyMember row F11B036L29) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B036L30_lift (row : List GridPoint) (h : FamilyMember row F11B036L30) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B036L31_lift (row : List GridPoint) (h : FamilyMember row F11B036L31) : FamilyMember row F11B036 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B036L32_lift (row : List GridPoint) (h : FamilyMember row F11B036L32) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B036L33_lift (row : List GridPoint) (h : FamilyMember row F11B036L33) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B036L34_lift (row : List GridPoint) (h : FamilyMember row F11B036L34) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B036L35_lift (row : List GridPoint) (h : FamilyMember row F11B036L35) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B036L36_lift (row : List GridPoint) (h : FamilyMember row F11B036L36) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B036L37_lift (row : List GridPoint) (h : FamilyMember row F11B036L37) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B036L38_lift (row : List GridPoint) (h : FamilyMember row F11B036L38) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B036L39_lift (row : List GridPoint) (h : FamilyMember row F11B036L39) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B036L40_lift (row : List GridPoint) (h : FamilyMember row F11B036L40) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B036L41_lift (row : List GridPoint) (h : FamilyMember row F11B036L41) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B036L42_lift (row : List GridPoint) (h : FamilyMember row F11B036L42) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B036L43_lift (row : List GridPoint) (h : FamilyMember row F11B036L43) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B036L44_lift (row : List GridPoint) (h : FamilyMember row F11B036L44) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B036L45_lift (row : List GridPoint) (h : FamilyMember row F11B036L45) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B036L46_lift (row : List GridPoint) (h : FamilyMember row F11B036L46) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B036L47_lift (row : List GridPoint) (h : FamilyMember row F11B036L47) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B036L48_lift (row : List GridPoint) (h : FamilyMember row F11B036L48) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B036L49_lift (row : List GridPoint) (h : FamilyMember row F11B036L49) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B036L50_lift (row : List GridPoint) (h : FamilyMember row F11B036L50) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B036L51_lift (row : List GridPoint) (h : FamilyMember row F11B036L51) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B036L52_lift (row : List GridPoint) (h : FamilyMember row F11B036L52) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B036L53_lift (row : List GridPoint) (h : FamilyMember row F11B036L53) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B036L54_lift (row : List GridPoint) (h : FamilyMember row F11B036L54) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B036L55_lift (row : List GridPoint) (h : FamilyMember row F11B036L55) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B036L56_lift (row : List GridPoint) (h : FamilyMember row F11B036L56) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B036L57_lift (row : List GridPoint) (h : FamilyMember row F11B036L57) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B036L58_lift (row : List GridPoint) (h : FamilyMember row F11B036L58) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B036L59_lift (row : List GridPoint) (h : FamilyMember row F11B036L59) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B036L60_lift (row : List GridPoint) (h : FamilyMember row F11B036L60) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B036L61_lift (row : List GridPoint) (h : FamilyMember row F11B036L61) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B036L62_lift (row : List GridPoint) (h : FamilyMember row F11B036L62) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B036L63_lift (row : List GridPoint) (h : FamilyMember row F11B036L63) : FamilyMember row F11B036 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
