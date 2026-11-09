import TreeBlock051
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B051L0 : RowFamilyTree := TreeBlock051L0
abbrev F11B051L1 : RowFamilyTree := TreeBlock051L1
abbrev F11B051L2 : RowFamilyTree := TreeBlock051L2
abbrev F11B051L3 : RowFamilyTree := TreeBlock051L3
abbrev F11B051L4 : RowFamilyTree := TreeBlock051L4
abbrev F11B051L5 : RowFamilyTree := TreeBlock051L5
abbrev F11B051L6 : RowFamilyTree := TreeBlock051L6
abbrev F11B051L7 : RowFamilyTree := TreeBlock051L7
abbrev F11B051L8 : RowFamilyTree := TreeBlock051L8
abbrev F11B051L9 : RowFamilyTree := TreeBlock051L9
abbrev F11B051L10 : RowFamilyTree := TreeBlock051L10
abbrev F11B051L11 : RowFamilyTree := TreeBlock051L11
abbrev F11B051L12 : RowFamilyTree := TreeBlock051L12
abbrev F11B051L13 : RowFamilyTree := TreeBlock051L13
abbrev F11B051L14 : RowFamilyTree := TreeBlock051L14
abbrev F11B051L15 : RowFamilyTree := TreeBlock051L15
abbrev F11B051L16 : RowFamilyTree := TreeBlock051L16
abbrev F11B051L17 : RowFamilyTree := TreeBlock051L17
abbrev F11B051L18 : RowFamilyTree := TreeBlock051L18
abbrev F11B051L19 : RowFamilyTree := TreeBlock051L19
abbrev F11B051L20 : RowFamilyTree := TreeBlock051L20
abbrev F11B051L21 : RowFamilyTree := TreeBlock051L21
abbrev F11B051L22 : RowFamilyTree := TreeBlock051L22
abbrev F11B051L23 : RowFamilyTree := TreeBlock051L23
abbrev F11B051L24 : RowFamilyTree := TreeBlock051L24
abbrev F11B051L25 : RowFamilyTree := TreeBlock051L25
abbrev F11B051L26 : RowFamilyTree := TreeBlock051L26
abbrev F11B051L27 : RowFamilyTree := TreeBlock051L27
abbrev F11B051L28 : RowFamilyTree := TreeBlock051L28
abbrev F11B051L29 : RowFamilyTree := TreeBlock051L29
abbrev F11B051L30 : RowFamilyTree := TreeBlock051L30
abbrev F11B051L31 : RowFamilyTree := TreeBlock051L31
abbrev F11B051L32 : RowFamilyTree := TreeBlock051L32
abbrev F11B051L33 : RowFamilyTree := TreeBlock051L33
abbrev F11B051L34 : RowFamilyTree := TreeBlock051L34
abbrev F11B051L35 : RowFamilyTree := TreeBlock051L35
abbrev F11B051L36 : RowFamilyTree := TreeBlock051L36
abbrev F11B051L37 : RowFamilyTree := TreeBlock051L37
abbrev F11B051L38 : RowFamilyTree := TreeBlock051L38
abbrev F11B051L39 : RowFamilyTree := TreeBlock051L39
abbrev F11B051L40 : RowFamilyTree := TreeBlock051L40
abbrev F11B051L41 : RowFamilyTree := TreeBlock051L41
abbrev F11B051L42 : RowFamilyTree := TreeBlock051L42
abbrev F11B051L43 : RowFamilyTree := TreeBlock051L43
abbrev F11B051L44 : RowFamilyTree := TreeBlock051L44
abbrev F11B051L45 : RowFamilyTree := TreeBlock051L45
abbrev F11B051L46 : RowFamilyTree := TreeBlock051L46
abbrev F11B051L47 : RowFamilyTree := TreeBlock051L47
abbrev F11B051L48 : RowFamilyTree := TreeBlock051L48
abbrev F11B051L49 : RowFamilyTree := TreeBlock051L49
abbrev F11B051L50 : RowFamilyTree := TreeBlock051L50
abbrev F11B051L51 : RowFamilyTree := TreeBlock051L51
abbrev F11B051L52 : RowFamilyTree := TreeBlock051L52
abbrev F11B051L53 : RowFamilyTree := TreeBlock051L53
abbrev F11B051L54 : RowFamilyTree := TreeBlock051L54
abbrev F11B051L55 : RowFamilyTree := TreeBlock051L55
abbrev F11B051L56 : RowFamilyTree := TreeBlock051L56
abbrev F11B051L57 : RowFamilyTree := TreeBlock051L57
abbrev F11B051L58 : RowFamilyTree := TreeBlock051L58
abbrev F11B051L59 : RowFamilyTree := TreeBlock051L59
abbrev F11B051L60 : RowFamilyTree := TreeBlock051L60
abbrev F11B051L61 : RowFamilyTree := TreeBlock051L61
abbrev F11B051L62 : RowFamilyTree := TreeBlock051L62
abbrev F11B051L63 : RowFamilyTree := TreeBlock051L63
abbrev F11B051 : RowFamilyTree := TreeBlock051
theorem F11B051L0_lift (row : List GridPoint) (h : FamilyMember row F11B051L0) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B051L1_lift (row : List GridPoint) (h : FamilyMember row F11B051L1) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B051L2_lift (row : List GridPoint) (h : FamilyMember row F11B051L2) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B051L3_lift (row : List GridPoint) (h : FamilyMember row F11B051L3) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B051L4_lift (row : List GridPoint) (h : FamilyMember row F11B051L4) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B051L5_lift (row : List GridPoint) (h : FamilyMember row F11B051L5) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B051L6_lift (row : List GridPoint) (h : FamilyMember row F11B051L6) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B051L7_lift (row : List GridPoint) (h : FamilyMember row F11B051L7) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B051L8_lift (row : List GridPoint) (h : FamilyMember row F11B051L8) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B051L9_lift (row : List GridPoint) (h : FamilyMember row F11B051L9) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B051L10_lift (row : List GridPoint) (h : FamilyMember row F11B051L10) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B051L11_lift (row : List GridPoint) (h : FamilyMember row F11B051L11) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B051L12_lift (row : List GridPoint) (h : FamilyMember row F11B051L12) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B051L13_lift (row : List GridPoint) (h : FamilyMember row F11B051L13) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B051L14_lift (row : List GridPoint) (h : FamilyMember row F11B051L14) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B051L15_lift (row : List GridPoint) (h : FamilyMember row F11B051L15) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B051L16_lift (row : List GridPoint) (h : FamilyMember row F11B051L16) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B051L17_lift (row : List GridPoint) (h : FamilyMember row F11B051L17) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B051L18_lift (row : List GridPoint) (h : FamilyMember row F11B051L18) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B051L19_lift (row : List GridPoint) (h : FamilyMember row F11B051L19) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B051L20_lift (row : List GridPoint) (h : FamilyMember row F11B051L20) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B051L21_lift (row : List GridPoint) (h : FamilyMember row F11B051L21) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B051L22_lift (row : List GridPoint) (h : FamilyMember row F11B051L22) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B051L23_lift (row : List GridPoint) (h : FamilyMember row F11B051L23) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B051L24_lift (row : List GridPoint) (h : FamilyMember row F11B051L24) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B051L25_lift (row : List GridPoint) (h : FamilyMember row F11B051L25) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B051L26_lift (row : List GridPoint) (h : FamilyMember row F11B051L26) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B051L27_lift (row : List GridPoint) (h : FamilyMember row F11B051L27) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B051L28_lift (row : List GridPoint) (h : FamilyMember row F11B051L28) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B051L29_lift (row : List GridPoint) (h : FamilyMember row F11B051L29) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B051L30_lift (row : List GridPoint) (h : FamilyMember row F11B051L30) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B051L31_lift (row : List GridPoint) (h : FamilyMember row F11B051L31) : FamilyMember row F11B051 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B051L32_lift (row : List GridPoint) (h : FamilyMember row F11B051L32) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B051L33_lift (row : List GridPoint) (h : FamilyMember row F11B051L33) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B051L34_lift (row : List GridPoint) (h : FamilyMember row F11B051L34) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B051L35_lift (row : List GridPoint) (h : FamilyMember row F11B051L35) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B051L36_lift (row : List GridPoint) (h : FamilyMember row F11B051L36) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B051L37_lift (row : List GridPoint) (h : FamilyMember row F11B051L37) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B051L38_lift (row : List GridPoint) (h : FamilyMember row F11B051L38) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B051L39_lift (row : List GridPoint) (h : FamilyMember row F11B051L39) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B051L40_lift (row : List GridPoint) (h : FamilyMember row F11B051L40) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B051L41_lift (row : List GridPoint) (h : FamilyMember row F11B051L41) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B051L42_lift (row : List GridPoint) (h : FamilyMember row F11B051L42) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B051L43_lift (row : List GridPoint) (h : FamilyMember row F11B051L43) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B051L44_lift (row : List GridPoint) (h : FamilyMember row F11B051L44) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B051L45_lift (row : List GridPoint) (h : FamilyMember row F11B051L45) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B051L46_lift (row : List GridPoint) (h : FamilyMember row F11B051L46) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B051L47_lift (row : List GridPoint) (h : FamilyMember row F11B051L47) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B051L48_lift (row : List GridPoint) (h : FamilyMember row F11B051L48) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B051L49_lift (row : List GridPoint) (h : FamilyMember row F11B051L49) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B051L50_lift (row : List GridPoint) (h : FamilyMember row F11B051L50) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B051L51_lift (row : List GridPoint) (h : FamilyMember row F11B051L51) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B051L52_lift (row : List GridPoint) (h : FamilyMember row F11B051L52) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B051L53_lift (row : List GridPoint) (h : FamilyMember row F11B051L53) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B051L54_lift (row : List GridPoint) (h : FamilyMember row F11B051L54) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B051L55_lift (row : List GridPoint) (h : FamilyMember row F11B051L55) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B051L56_lift (row : List GridPoint) (h : FamilyMember row F11B051L56) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B051L57_lift (row : List GridPoint) (h : FamilyMember row F11B051L57) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B051L58_lift (row : List GridPoint) (h : FamilyMember row F11B051L58) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B051L59_lift (row : List GridPoint) (h : FamilyMember row F11B051L59) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B051L60_lift (row : List GridPoint) (h : FamilyMember row F11B051L60) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B051L61_lift (row : List GridPoint) (h : FamilyMember row F11B051L61) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B051L62_lift (row : List GridPoint) (h : FamilyMember row F11B051L62) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B051L63_lift (row : List GridPoint) (h : FamilyMember row F11B051L63) : FamilyMember row F11B051 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
