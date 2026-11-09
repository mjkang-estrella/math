import TreeBlock031
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B031L0 : RowFamilyTree := TreeBlock031L0
abbrev F11B031L1 : RowFamilyTree := TreeBlock031L1
abbrev F11B031L2 : RowFamilyTree := TreeBlock031L2
abbrev F11B031L3 : RowFamilyTree := TreeBlock031L3
abbrev F11B031L4 : RowFamilyTree := TreeBlock031L4
abbrev F11B031L5 : RowFamilyTree := TreeBlock031L5
abbrev F11B031L6 : RowFamilyTree := TreeBlock031L6
abbrev F11B031L7 : RowFamilyTree := TreeBlock031L7
abbrev F11B031L8 : RowFamilyTree := TreeBlock031L8
abbrev F11B031L9 : RowFamilyTree := TreeBlock031L9
abbrev F11B031L10 : RowFamilyTree := TreeBlock031L10
abbrev F11B031L11 : RowFamilyTree := TreeBlock031L11
abbrev F11B031L12 : RowFamilyTree := TreeBlock031L12
abbrev F11B031L13 : RowFamilyTree := TreeBlock031L13
abbrev F11B031L14 : RowFamilyTree := TreeBlock031L14
abbrev F11B031L15 : RowFamilyTree := TreeBlock031L15
abbrev F11B031L16 : RowFamilyTree := TreeBlock031L16
abbrev F11B031L17 : RowFamilyTree := TreeBlock031L17
abbrev F11B031L18 : RowFamilyTree := TreeBlock031L18
abbrev F11B031L19 : RowFamilyTree := TreeBlock031L19
abbrev F11B031L20 : RowFamilyTree := TreeBlock031L20
abbrev F11B031L21 : RowFamilyTree := TreeBlock031L21
abbrev F11B031L22 : RowFamilyTree := TreeBlock031L22
abbrev F11B031L23 : RowFamilyTree := TreeBlock031L23
abbrev F11B031L24 : RowFamilyTree := TreeBlock031L24
abbrev F11B031L25 : RowFamilyTree := TreeBlock031L25
abbrev F11B031L26 : RowFamilyTree := TreeBlock031L26
abbrev F11B031L27 : RowFamilyTree := TreeBlock031L27
abbrev F11B031L28 : RowFamilyTree := TreeBlock031L28
abbrev F11B031L29 : RowFamilyTree := TreeBlock031L29
abbrev F11B031L30 : RowFamilyTree := TreeBlock031L30
abbrev F11B031L31 : RowFamilyTree := TreeBlock031L31
abbrev F11B031L32 : RowFamilyTree := TreeBlock031L32
abbrev F11B031L33 : RowFamilyTree := TreeBlock031L33
abbrev F11B031L34 : RowFamilyTree := TreeBlock031L34
abbrev F11B031L35 : RowFamilyTree := TreeBlock031L35
abbrev F11B031L36 : RowFamilyTree := TreeBlock031L36
abbrev F11B031L37 : RowFamilyTree := TreeBlock031L37
abbrev F11B031L38 : RowFamilyTree := TreeBlock031L38
abbrev F11B031L39 : RowFamilyTree := TreeBlock031L39
abbrev F11B031L40 : RowFamilyTree := TreeBlock031L40
abbrev F11B031L41 : RowFamilyTree := TreeBlock031L41
abbrev F11B031L42 : RowFamilyTree := TreeBlock031L42
abbrev F11B031L43 : RowFamilyTree := TreeBlock031L43
abbrev F11B031L44 : RowFamilyTree := TreeBlock031L44
abbrev F11B031L45 : RowFamilyTree := TreeBlock031L45
abbrev F11B031L46 : RowFamilyTree := TreeBlock031L46
abbrev F11B031L47 : RowFamilyTree := TreeBlock031L47
abbrev F11B031L48 : RowFamilyTree := TreeBlock031L48
abbrev F11B031L49 : RowFamilyTree := TreeBlock031L49
abbrev F11B031L50 : RowFamilyTree := TreeBlock031L50
abbrev F11B031L51 : RowFamilyTree := TreeBlock031L51
abbrev F11B031L52 : RowFamilyTree := TreeBlock031L52
abbrev F11B031L53 : RowFamilyTree := TreeBlock031L53
abbrev F11B031L54 : RowFamilyTree := TreeBlock031L54
abbrev F11B031L55 : RowFamilyTree := TreeBlock031L55
abbrev F11B031L56 : RowFamilyTree := TreeBlock031L56
abbrev F11B031L57 : RowFamilyTree := TreeBlock031L57
abbrev F11B031L58 : RowFamilyTree := TreeBlock031L58
abbrev F11B031L59 : RowFamilyTree := TreeBlock031L59
abbrev F11B031L60 : RowFamilyTree := TreeBlock031L60
abbrev F11B031L61 : RowFamilyTree := TreeBlock031L61
abbrev F11B031L62 : RowFamilyTree := TreeBlock031L62
abbrev F11B031L63 : RowFamilyTree := TreeBlock031L63
abbrev F11B031 : RowFamilyTree := TreeBlock031
theorem F11B031L0_lift (row : List GridPoint) (h : FamilyMember row F11B031L0) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B031L1_lift (row : List GridPoint) (h : FamilyMember row F11B031L1) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B031L2_lift (row : List GridPoint) (h : FamilyMember row F11B031L2) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B031L3_lift (row : List GridPoint) (h : FamilyMember row F11B031L3) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B031L4_lift (row : List GridPoint) (h : FamilyMember row F11B031L4) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B031L5_lift (row : List GridPoint) (h : FamilyMember row F11B031L5) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B031L6_lift (row : List GridPoint) (h : FamilyMember row F11B031L6) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B031L7_lift (row : List GridPoint) (h : FamilyMember row F11B031L7) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B031L8_lift (row : List GridPoint) (h : FamilyMember row F11B031L8) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B031L9_lift (row : List GridPoint) (h : FamilyMember row F11B031L9) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B031L10_lift (row : List GridPoint) (h : FamilyMember row F11B031L10) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B031L11_lift (row : List GridPoint) (h : FamilyMember row F11B031L11) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B031L12_lift (row : List GridPoint) (h : FamilyMember row F11B031L12) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B031L13_lift (row : List GridPoint) (h : FamilyMember row F11B031L13) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B031L14_lift (row : List GridPoint) (h : FamilyMember row F11B031L14) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B031L15_lift (row : List GridPoint) (h : FamilyMember row F11B031L15) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B031L16_lift (row : List GridPoint) (h : FamilyMember row F11B031L16) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B031L17_lift (row : List GridPoint) (h : FamilyMember row F11B031L17) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B031L18_lift (row : List GridPoint) (h : FamilyMember row F11B031L18) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B031L19_lift (row : List GridPoint) (h : FamilyMember row F11B031L19) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B031L20_lift (row : List GridPoint) (h : FamilyMember row F11B031L20) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B031L21_lift (row : List GridPoint) (h : FamilyMember row F11B031L21) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B031L22_lift (row : List GridPoint) (h : FamilyMember row F11B031L22) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B031L23_lift (row : List GridPoint) (h : FamilyMember row F11B031L23) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B031L24_lift (row : List GridPoint) (h : FamilyMember row F11B031L24) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B031L25_lift (row : List GridPoint) (h : FamilyMember row F11B031L25) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B031L26_lift (row : List GridPoint) (h : FamilyMember row F11B031L26) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B031L27_lift (row : List GridPoint) (h : FamilyMember row F11B031L27) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B031L28_lift (row : List GridPoint) (h : FamilyMember row F11B031L28) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B031L29_lift (row : List GridPoint) (h : FamilyMember row F11B031L29) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B031L30_lift (row : List GridPoint) (h : FamilyMember row F11B031L30) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B031L31_lift (row : List GridPoint) (h : FamilyMember row F11B031L31) : FamilyMember row F11B031 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B031L32_lift (row : List GridPoint) (h : FamilyMember row F11B031L32) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B031L33_lift (row : List GridPoint) (h : FamilyMember row F11B031L33) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B031L34_lift (row : List GridPoint) (h : FamilyMember row F11B031L34) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B031L35_lift (row : List GridPoint) (h : FamilyMember row F11B031L35) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B031L36_lift (row : List GridPoint) (h : FamilyMember row F11B031L36) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B031L37_lift (row : List GridPoint) (h : FamilyMember row F11B031L37) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B031L38_lift (row : List GridPoint) (h : FamilyMember row F11B031L38) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B031L39_lift (row : List GridPoint) (h : FamilyMember row F11B031L39) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B031L40_lift (row : List GridPoint) (h : FamilyMember row F11B031L40) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B031L41_lift (row : List GridPoint) (h : FamilyMember row F11B031L41) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B031L42_lift (row : List GridPoint) (h : FamilyMember row F11B031L42) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B031L43_lift (row : List GridPoint) (h : FamilyMember row F11B031L43) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B031L44_lift (row : List GridPoint) (h : FamilyMember row F11B031L44) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B031L45_lift (row : List GridPoint) (h : FamilyMember row F11B031L45) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B031L46_lift (row : List GridPoint) (h : FamilyMember row F11B031L46) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B031L47_lift (row : List GridPoint) (h : FamilyMember row F11B031L47) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B031L48_lift (row : List GridPoint) (h : FamilyMember row F11B031L48) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B031L49_lift (row : List GridPoint) (h : FamilyMember row F11B031L49) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B031L50_lift (row : List GridPoint) (h : FamilyMember row F11B031L50) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B031L51_lift (row : List GridPoint) (h : FamilyMember row F11B031L51) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B031L52_lift (row : List GridPoint) (h : FamilyMember row F11B031L52) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B031L53_lift (row : List GridPoint) (h : FamilyMember row F11B031L53) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B031L54_lift (row : List GridPoint) (h : FamilyMember row F11B031L54) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B031L55_lift (row : List GridPoint) (h : FamilyMember row F11B031L55) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B031L56_lift (row : List GridPoint) (h : FamilyMember row F11B031L56) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B031L57_lift (row : List GridPoint) (h : FamilyMember row F11B031L57) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B031L58_lift (row : List GridPoint) (h : FamilyMember row F11B031L58) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B031L59_lift (row : List GridPoint) (h : FamilyMember row F11B031L59) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B031L60_lift (row : List GridPoint) (h : FamilyMember row F11B031L60) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B031L61_lift (row : List GridPoint) (h : FamilyMember row F11B031L61) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B031L62_lift (row : List GridPoint) (h : FamilyMember row F11B031L62) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B031L63_lift (row : List GridPoint) (h : FamilyMember row F11B031L63) : FamilyMember row F11B031 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
