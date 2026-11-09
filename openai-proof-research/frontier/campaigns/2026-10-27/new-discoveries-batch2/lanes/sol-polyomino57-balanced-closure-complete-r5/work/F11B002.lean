import TreeBlock002
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B002L0 : RowFamilyTree := TreeBlock002L0
abbrev F11B002L1 : RowFamilyTree := TreeBlock002L1
abbrev F11B002L2 : RowFamilyTree := TreeBlock002L2
abbrev F11B002L3 : RowFamilyTree := TreeBlock002L3
abbrev F11B002L4 : RowFamilyTree := TreeBlock002L4
abbrev F11B002L5 : RowFamilyTree := TreeBlock002L5
abbrev F11B002L6 : RowFamilyTree := TreeBlock002L6
abbrev F11B002L7 : RowFamilyTree := TreeBlock002L7
abbrev F11B002L8 : RowFamilyTree := TreeBlock002L8
abbrev F11B002L9 : RowFamilyTree := TreeBlock002L9
abbrev F11B002L10 : RowFamilyTree := TreeBlock002L10
abbrev F11B002L11 : RowFamilyTree := TreeBlock002L11
abbrev F11B002L12 : RowFamilyTree := TreeBlock002L12
abbrev F11B002L13 : RowFamilyTree := TreeBlock002L13
abbrev F11B002L14 : RowFamilyTree := TreeBlock002L14
abbrev F11B002L15 : RowFamilyTree := TreeBlock002L15
abbrev F11B002L16 : RowFamilyTree := TreeBlock002L16
abbrev F11B002L17 : RowFamilyTree := TreeBlock002L17
abbrev F11B002L18 : RowFamilyTree := TreeBlock002L18
abbrev F11B002L19 : RowFamilyTree := TreeBlock002L19
abbrev F11B002L20 : RowFamilyTree := TreeBlock002L20
abbrev F11B002L21 : RowFamilyTree := TreeBlock002L21
abbrev F11B002L22 : RowFamilyTree := TreeBlock002L22
abbrev F11B002L23 : RowFamilyTree := TreeBlock002L23
abbrev F11B002L24 : RowFamilyTree := TreeBlock002L24
abbrev F11B002L25 : RowFamilyTree := TreeBlock002L25
abbrev F11B002L26 : RowFamilyTree := TreeBlock002L26
abbrev F11B002L27 : RowFamilyTree := TreeBlock002L27
abbrev F11B002L28 : RowFamilyTree := TreeBlock002L28
abbrev F11B002L29 : RowFamilyTree := TreeBlock002L29
abbrev F11B002L30 : RowFamilyTree := TreeBlock002L30
abbrev F11B002L31 : RowFamilyTree := TreeBlock002L31
abbrev F11B002L32 : RowFamilyTree := TreeBlock002L32
abbrev F11B002L33 : RowFamilyTree := TreeBlock002L33
abbrev F11B002L34 : RowFamilyTree := TreeBlock002L34
abbrev F11B002L35 : RowFamilyTree := TreeBlock002L35
abbrev F11B002L36 : RowFamilyTree := TreeBlock002L36
abbrev F11B002L37 : RowFamilyTree := TreeBlock002L37
abbrev F11B002L38 : RowFamilyTree := TreeBlock002L38
abbrev F11B002L39 : RowFamilyTree := TreeBlock002L39
abbrev F11B002L40 : RowFamilyTree := TreeBlock002L40
abbrev F11B002L41 : RowFamilyTree := TreeBlock002L41
abbrev F11B002L42 : RowFamilyTree := TreeBlock002L42
abbrev F11B002L43 : RowFamilyTree := TreeBlock002L43
abbrev F11B002L44 : RowFamilyTree := TreeBlock002L44
abbrev F11B002L45 : RowFamilyTree := TreeBlock002L45
abbrev F11B002L46 : RowFamilyTree := TreeBlock002L46
abbrev F11B002L47 : RowFamilyTree := TreeBlock002L47
abbrev F11B002L48 : RowFamilyTree := TreeBlock002L48
abbrev F11B002L49 : RowFamilyTree := TreeBlock002L49
abbrev F11B002L50 : RowFamilyTree := TreeBlock002L50
abbrev F11B002L51 : RowFamilyTree := TreeBlock002L51
abbrev F11B002L52 : RowFamilyTree := TreeBlock002L52
abbrev F11B002L53 : RowFamilyTree := TreeBlock002L53
abbrev F11B002L54 : RowFamilyTree := TreeBlock002L54
abbrev F11B002L55 : RowFamilyTree := TreeBlock002L55
abbrev F11B002L56 : RowFamilyTree := TreeBlock002L56
abbrev F11B002L57 : RowFamilyTree := TreeBlock002L57
abbrev F11B002L58 : RowFamilyTree := TreeBlock002L58
abbrev F11B002L59 : RowFamilyTree := TreeBlock002L59
abbrev F11B002L60 : RowFamilyTree := TreeBlock002L60
abbrev F11B002L61 : RowFamilyTree := TreeBlock002L61
abbrev F11B002L62 : RowFamilyTree := TreeBlock002L62
abbrev F11B002L63 : RowFamilyTree := TreeBlock002L63
abbrev F11B002 : RowFamilyTree := TreeBlock002
theorem F11B002L0_lift (row : List GridPoint) (h : FamilyMember row F11B002L0) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B002L1_lift (row : List GridPoint) (h : FamilyMember row F11B002L1) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B002L2_lift (row : List GridPoint) (h : FamilyMember row F11B002L2) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B002L3_lift (row : List GridPoint) (h : FamilyMember row F11B002L3) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B002L4_lift (row : List GridPoint) (h : FamilyMember row F11B002L4) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B002L5_lift (row : List GridPoint) (h : FamilyMember row F11B002L5) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B002L6_lift (row : List GridPoint) (h : FamilyMember row F11B002L6) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B002L7_lift (row : List GridPoint) (h : FamilyMember row F11B002L7) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B002L8_lift (row : List GridPoint) (h : FamilyMember row F11B002L8) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B002L9_lift (row : List GridPoint) (h : FamilyMember row F11B002L9) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B002L10_lift (row : List GridPoint) (h : FamilyMember row F11B002L10) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B002L11_lift (row : List GridPoint) (h : FamilyMember row F11B002L11) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B002L12_lift (row : List GridPoint) (h : FamilyMember row F11B002L12) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B002L13_lift (row : List GridPoint) (h : FamilyMember row F11B002L13) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B002L14_lift (row : List GridPoint) (h : FamilyMember row F11B002L14) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B002L15_lift (row : List GridPoint) (h : FamilyMember row F11B002L15) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B002L16_lift (row : List GridPoint) (h : FamilyMember row F11B002L16) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B002L17_lift (row : List GridPoint) (h : FamilyMember row F11B002L17) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B002L18_lift (row : List GridPoint) (h : FamilyMember row F11B002L18) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B002L19_lift (row : List GridPoint) (h : FamilyMember row F11B002L19) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B002L20_lift (row : List GridPoint) (h : FamilyMember row F11B002L20) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B002L21_lift (row : List GridPoint) (h : FamilyMember row F11B002L21) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B002L22_lift (row : List GridPoint) (h : FamilyMember row F11B002L22) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B002L23_lift (row : List GridPoint) (h : FamilyMember row F11B002L23) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B002L24_lift (row : List GridPoint) (h : FamilyMember row F11B002L24) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B002L25_lift (row : List GridPoint) (h : FamilyMember row F11B002L25) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B002L26_lift (row : List GridPoint) (h : FamilyMember row F11B002L26) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B002L27_lift (row : List GridPoint) (h : FamilyMember row F11B002L27) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B002L28_lift (row : List GridPoint) (h : FamilyMember row F11B002L28) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B002L29_lift (row : List GridPoint) (h : FamilyMember row F11B002L29) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B002L30_lift (row : List GridPoint) (h : FamilyMember row F11B002L30) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B002L31_lift (row : List GridPoint) (h : FamilyMember row F11B002L31) : FamilyMember row F11B002 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B002L32_lift (row : List GridPoint) (h : FamilyMember row F11B002L32) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B002L33_lift (row : List GridPoint) (h : FamilyMember row F11B002L33) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B002L34_lift (row : List GridPoint) (h : FamilyMember row F11B002L34) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B002L35_lift (row : List GridPoint) (h : FamilyMember row F11B002L35) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B002L36_lift (row : List GridPoint) (h : FamilyMember row F11B002L36) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B002L37_lift (row : List GridPoint) (h : FamilyMember row F11B002L37) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B002L38_lift (row : List GridPoint) (h : FamilyMember row F11B002L38) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B002L39_lift (row : List GridPoint) (h : FamilyMember row F11B002L39) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B002L40_lift (row : List GridPoint) (h : FamilyMember row F11B002L40) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B002L41_lift (row : List GridPoint) (h : FamilyMember row F11B002L41) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B002L42_lift (row : List GridPoint) (h : FamilyMember row F11B002L42) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B002L43_lift (row : List GridPoint) (h : FamilyMember row F11B002L43) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B002L44_lift (row : List GridPoint) (h : FamilyMember row F11B002L44) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B002L45_lift (row : List GridPoint) (h : FamilyMember row F11B002L45) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B002L46_lift (row : List GridPoint) (h : FamilyMember row F11B002L46) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B002L47_lift (row : List GridPoint) (h : FamilyMember row F11B002L47) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B002L48_lift (row : List GridPoint) (h : FamilyMember row F11B002L48) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B002L49_lift (row : List GridPoint) (h : FamilyMember row F11B002L49) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B002L50_lift (row : List GridPoint) (h : FamilyMember row F11B002L50) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B002L51_lift (row : List GridPoint) (h : FamilyMember row F11B002L51) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B002L52_lift (row : List GridPoint) (h : FamilyMember row F11B002L52) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B002L53_lift (row : List GridPoint) (h : FamilyMember row F11B002L53) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B002L54_lift (row : List GridPoint) (h : FamilyMember row F11B002L54) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B002L55_lift (row : List GridPoint) (h : FamilyMember row F11B002L55) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B002L56_lift (row : List GridPoint) (h : FamilyMember row F11B002L56) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B002L57_lift (row : List GridPoint) (h : FamilyMember row F11B002L57) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B002L58_lift (row : List GridPoint) (h : FamilyMember row F11B002L58) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B002L59_lift (row : List GridPoint) (h : FamilyMember row F11B002L59) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B002L60_lift (row : List GridPoint) (h : FamilyMember row F11B002L60) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B002L61_lift (row : List GridPoint) (h : FamilyMember row F11B002L61) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B002L62_lift (row : List GridPoint) (h : FamilyMember row F11B002L62) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B002L63_lift (row : List GridPoint) (h : FamilyMember row F11B002L63) : FamilyMember row F11B002 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
