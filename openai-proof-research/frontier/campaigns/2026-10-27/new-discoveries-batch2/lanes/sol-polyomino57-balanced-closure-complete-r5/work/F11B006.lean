import TreeBlock006
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B006L0 : RowFamilyTree := TreeBlock006L0
abbrev F11B006L1 : RowFamilyTree := TreeBlock006L1
abbrev F11B006L2 : RowFamilyTree := TreeBlock006L2
abbrev F11B006L3 : RowFamilyTree := TreeBlock006L3
abbrev F11B006L4 : RowFamilyTree := TreeBlock006L4
abbrev F11B006L5 : RowFamilyTree := TreeBlock006L5
abbrev F11B006L6 : RowFamilyTree := TreeBlock006L6
abbrev F11B006L7 : RowFamilyTree := TreeBlock006L7
abbrev F11B006L8 : RowFamilyTree := TreeBlock006L8
abbrev F11B006L9 : RowFamilyTree := TreeBlock006L9
abbrev F11B006L10 : RowFamilyTree := TreeBlock006L10
abbrev F11B006L11 : RowFamilyTree := TreeBlock006L11
abbrev F11B006L12 : RowFamilyTree := TreeBlock006L12
abbrev F11B006L13 : RowFamilyTree := TreeBlock006L13
abbrev F11B006L14 : RowFamilyTree := TreeBlock006L14
abbrev F11B006L15 : RowFamilyTree := TreeBlock006L15
abbrev F11B006L16 : RowFamilyTree := TreeBlock006L16
abbrev F11B006L17 : RowFamilyTree := TreeBlock006L17
abbrev F11B006L18 : RowFamilyTree := TreeBlock006L18
abbrev F11B006L19 : RowFamilyTree := TreeBlock006L19
abbrev F11B006L20 : RowFamilyTree := TreeBlock006L20
abbrev F11B006L21 : RowFamilyTree := TreeBlock006L21
abbrev F11B006L22 : RowFamilyTree := TreeBlock006L22
abbrev F11B006L23 : RowFamilyTree := TreeBlock006L23
abbrev F11B006L24 : RowFamilyTree := TreeBlock006L24
abbrev F11B006L25 : RowFamilyTree := TreeBlock006L25
abbrev F11B006L26 : RowFamilyTree := TreeBlock006L26
abbrev F11B006L27 : RowFamilyTree := TreeBlock006L27
abbrev F11B006L28 : RowFamilyTree := TreeBlock006L28
abbrev F11B006L29 : RowFamilyTree := TreeBlock006L29
abbrev F11B006L30 : RowFamilyTree := TreeBlock006L30
abbrev F11B006L31 : RowFamilyTree := TreeBlock006L31
abbrev F11B006L32 : RowFamilyTree := TreeBlock006L32
abbrev F11B006L33 : RowFamilyTree := TreeBlock006L33
abbrev F11B006L34 : RowFamilyTree := TreeBlock006L34
abbrev F11B006L35 : RowFamilyTree := TreeBlock006L35
abbrev F11B006L36 : RowFamilyTree := TreeBlock006L36
abbrev F11B006L37 : RowFamilyTree := TreeBlock006L37
abbrev F11B006L38 : RowFamilyTree := TreeBlock006L38
abbrev F11B006L39 : RowFamilyTree := TreeBlock006L39
abbrev F11B006L40 : RowFamilyTree := TreeBlock006L40
abbrev F11B006L41 : RowFamilyTree := TreeBlock006L41
abbrev F11B006L42 : RowFamilyTree := TreeBlock006L42
abbrev F11B006L43 : RowFamilyTree := TreeBlock006L43
abbrev F11B006L44 : RowFamilyTree := TreeBlock006L44
abbrev F11B006L45 : RowFamilyTree := TreeBlock006L45
abbrev F11B006L46 : RowFamilyTree := TreeBlock006L46
abbrev F11B006L47 : RowFamilyTree := TreeBlock006L47
abbrev F11B006L48 : RowFamilyTree := TreeBlock006L48
abbrev F11B006L49 : RowFamilyTree := TreeBlock006L49
abbrev F11B006L50 : RowFamilyTree := TreeBlock006L50
abbrev F11B006L51 : RowFamilyTree := TreeBlock006L51
abbrev F11B006L52 : RowFamilyTree := TreeBlock006L52
abbrev F11B006L53 : RowFamilyTree := TreeBlock006L53
abbrev F11B006L54 : RowFamilyTree := TreeBlock006L54
abbrev F11B006L55 : RowFamilyTree := TreeBlock006L55
abbrev F11B006L56 : RowFamilyTree := TreeBlock006L56
abbrev F11B006L57 : RowFamilyTree := TreeBlock006L57
abbrev F11B006L58 : RowFamilyTree := TreeBlock006L58
abbrev F11B006L59 : RowFamilyTree := TreeBlock006L59
abbrev F11B006L60 : RowFamilyTree := TreeBlock006L60
abbrev F11B006L61 : RowFamilyTree := TreeBlock006L61
abbrev F11B006L62 : RowFamilyTree := TreeBlock006L62
abbrev F11B006L63 : RowFamilyTree := TreeBlock006L63
abbrev F11B006 : RowFamilyTree := TreeBlock006
theorem F11B006L0_lift (row : List GridPoint) (h : FamilyMember row F11B006L0) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B006L1_lift (row : List GridPoint) (h : FamilyMember row F11B006L1) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B006L2_lift (row : List GridPoint) (h : FamilyMember row F11B006L2) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B006L3_lift (row : List GridPoint) (h : FamilyMember row F11B006L3) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B006L4_lift (row : List GridPoint) (h : FamilyMember row F11B006L4) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B006L5_lift (row : List GridPoint) (h : FamilyMember row F11B006L5) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B006L6_lift (row : List GridPoint) (h : FamilyMember row F11B006L6) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B006L7_lift (row : List GridPoint) (h : FamilyMember row F11B006L7) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B006L8_lift (row : List GridPoint) (h : FamilyMember row F11B006L8) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B006L9_lift (row : List GridPoint) (h : FamilyMember row F11B006L9) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B006L10_lift (row : List GridPoint) (h : FamilyMember row F11B006L10) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B006L11_lift (row : List GridPoint) (h : FamilyMember row F11B006L11) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B006L12_lift (row : List GridPoint) (h : FamilyMember row F11B006L12) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B006L13_lift (row : List GridPoint) (h : FamilyMember row F11B006L13) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B006L14_lift (row : List GridPoint) (h : FamilyMember row F11B006L14) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B006L15_lift (row : List GridPoint) (h : FamilyMember row F11B006L15) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B006L16_lift (row : List GridPoint) (h : FamilyMember row F11B006L16) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B006L17_lift (row : List GridPoint) (h : FamilyMember row F11B006L17) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B006L18_lift (row : List GridPoint) (h : FamilyMember row F11B006L18) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B006L19_lift (row : List GridPoint) (h : FamilyMember row F11B006L19) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B006L20_lift (row : List GridPoint) (h : FamilyMember row F11B006L20) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B006L21_lift (row : List GridPoint) (h : FamilyMember row F11B006L21) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B006L22_lift (row : List GridPoint) (h : FamilyMember row F11B006L22) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B006L23_lift (row : List GridPoint) (h : FamilyMember row F11B006L23) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B006L24_lift (row : List GridPoint) (h : FamilyMember row F11B006L24) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B006L25_lift (row : List GridPoint) (h : FamilyMember row F11B006L25) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B006L26_lift (row : List GridPoint) (h : FamilyMember row F11B006L26) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B006L27_lift (row : List GridPoint) (h : FamilyMember row F11B006L27) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B006L28_lift (row : List GridPoint) (h : FamilyMember row F11B006L28) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B006L29_lift (row : List GridPoint) (h : FamilyMember row F11B006L29) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B006L30_lift (row : List GridPoint) (h : FamilyMember row F11B006L30) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B006L31_lift (row : List GridPoint) (h : FamilyMember row F11B006L31) : FamilyMember row F11B006 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B006L32_lift (row : List GridPoint) (h : FamilyMember row F11B006L32) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B006L33_lift (row : List GridPoint) (h : FamilyMember row F11B006L33) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B006L34_lift (row : List GridPoint) (h : FamilyMember row F11B006L34) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B006L35_lift (row : List GridPoint) (h : FamilyMember row F11B006L35) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B006L36_lift (row : List GridPoint) (h : FamilyMember row F11B006L36) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B006L37_lift (row : List GridPoint) (h : FamilyMember row F11B006L37) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B006L38_lift (row : List GridPoint) (h : FamilyMember row F11B006L38) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B006L39_lift (row : List GridPoint) (h : FamilyMember row F11B006L39) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B006L40_lift (row : List GridPoint) (h : FamilyMember row F11B006L40) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B006L41_lift (row : List GridPoint) (h : FamilyMember row F11B006L41) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B006L42_lift (row : List GridPoint) (h : FamilyMember row F11B006L42) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B006L43_lift (row : List GridPoint) (h : FamilyMember row F11B006L43) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B006L44_lift (row : List GridPoint) (h : FamilyMember row F11B006L44) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B006L45_lift (row : List GridPoint) (h : FamilyMember row F11B006L45) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B006L46_lift (row : List GridPoint) (h : FamilyMember row F11B006L46) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B006L47_lift (row : List GridPoint) (h : FamilyMember row F11B006L47) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B006L48_lift (row : List GridPoint) (h : FamilyMember row F11B006L48) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B006L49_lift (row : List GridPoint) (h : FamilyMember row F11B006L49) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B006L50_lift (row : List GridPoint) (h : FamilyMember row F11B006L50) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B006L51_lift (row : List GridPoint) (h : FamilyMember row F11B006L51) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B006L52_lift (row : List GridPoint) (h : FamilyMember row F11B006L52) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B006L53_lift (row : List GridPoint) (h : FamilyMember row F11B006L53) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B006L54_lift (row : List GridPoint) (h : FamilyMember row F11B006L54) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B006L55_lift (row : List GridPoint) (h : FamilyMember row F11B006L55) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B006L56_lift (row : List GridPoint) (h : FamilyMember row F11B006L56) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B006L57_lift (row : List GridPoint) (h : FamilyMember row F11B006L57) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B006L58_lift (row : List GridPoint) (h : FamilyMember row F11B006L58) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B006L59_lift (row : List GridPoint) (h : FamilyMember row F11B006L59) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B006L60_lift (row : List GridPoint) (h : FamilyMember row F11B006L60) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B006L61_lift (row : List GridPoint) (h : FamilyMember row F11B006L61) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B006L62_lift (row : List GridPoint) (h : FamilyMember row F11B006L62) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B006L63_lift (row : List GridPoint) (h : FamilyMember row F11B006L63) : FamilyMember row F11B006 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
