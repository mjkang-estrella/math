import TreeBlock013
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B013L0 : RowFamilyTree := TreeBlock013L0
abbrev F11B013L1 : RowFamilyTree := TreeBlock013L1
abbrev F11B013L2 : RowFamilyTree := TreeBlock013L2
abbrev F11B013L3 : RowFamilyTree := TreeBlock013L3
abbrev F11B013L4 : RowFamilyTree := TreeBlock013L4
abbrev F11B013L5 : RowFamilyTree := TreeBlock013L5
abbrev F11B013L6 : RowFamilyTree := TreeBlock013L6
abbrev F11B013L7 : RowFamilyTree := TreeBlock013L7
abbrev F11B013L8 : RowFamilyTree := TreeBlock013L8
abbrev F11B013L9 : RowFamilyTree := TreeBlock013L9
abbrev F11B013L10 : RowFamilyTree := TreeBlock013L10
abbrev F11B013L11 : RowFamilyTree := TreeBlock013L11
abbrev F11B013L12 : RowFamilyTree := TreeBlock013L12
abbrev F11B013L13 : RowFamilyTree := TreeBlock013L13
abbrev F11B013L14 : RowFamilyTree := TreeBlock013L14
abbrev F11B013L15 : RowFamilyTree := TreeBlock013L15
abbrev F11B013L16 : RowFamilyTree := TreeBlock013L16
abbrev F11B013L17 : RowFamilyTree := TreeBlock013L17
abbrev F11B013L18 : RowFamilyTree := TreeBlock013L18
abbrev F11B013L19 : RowFamilyTree := TreeBlock013L19
abbrev F11B013L20 : RowFamilyTree := TreeBlock013L20
abbrev F11B013L21 : RowFamilyTree := TreeBlock013L21
abbrev F11B013L22 : RowFamilyTree := TreeBlock013L22
abbrev F11B013L23 : RowFamilyTree := TreeBlock013L23
abbrev F11B013L24 : RowFamilyTree := TreeBlock013L24
abbrev F11B013L25 : RowFamilyTree := TreeBlock013L25
abbrev F11B013L26 : RowFamilyTree := TreeBlock013L26
abbrev F11B013L27 : RowFamilyTree := TreeBlock013L27
abbrev F11B013L28 : RowFamilyTree := TreeBlock013L28
abbrev F11B013L29 : RowFamilyTree := TreeBlock013L29
abbrev F11B013L30 : RowFamilyTree := TreeBlock013L30
abbrev F11B013L31 : RowFamilyTree := TreeBlock013L31
abbrev F11B013L32 : RowFamilyTree := TreeBlock013L32
abbrev F11B013L33 : RowFamilyTree := TreeBlock013L33
abbrev F11B013L34 : RowFamilyTree := TreeBlock013L34
abbrev F11B013L35 : RowFamilyTree := TreeBlock013L35
abbrev F11B013L36 : RowFamilyTree := TreeBlock013L36
abbrev F11B013L37 : RowFamilyTree := TreeBlock013L37
abbrev F11B013L38 : RowFamilyTree := TreeBlock013L38
abbrev F11B013L39 : RowFamilyTree := TreeBlock013L39
abbrev F11B013L40 : RowFamilyTree := TreeBlock013L40
abbrev F11B013L41 : RowFamilyTree := TreeBlock013L41
abbrev F11B013L42 : RowFamilyTree := TreeBlock013L42
abbrev F11B013L43 : RowFamilyTree := TreeBlock013L43
abbrev F11B013L44 : RowFamilyTree := TreeBlock013L44
abbrev F11B013L45 : RowFamilyTree := TreeBlock013L45
abbrev F11B013L46 : RowFamilyTree := TreeBlock013L46
abbrev F11B013L47 : RowFamilyTree := TreeBlock013L47
abbrev F11B013L48 : RowFamilyTree := TreeBlock013L48
abbrev F11B013L49 : RowFamilyTree := TreeBlock013L49
abbrev F11B013L50 : RowFamilyTree := TreeBlock013L50
abbrev F11B013L51 : RowFamilyTree := TreeBlock013L51
abbrev F11B013L52 : RowFamilyTree := TreeBlock013L52
abbrev F11B013L53 : RowFamilyTree := TreeBlock013L53
abbrev F11B013L54 : RowFamilyTree := TreeBlock013L54
abbrev F11B013L55 : RowFamilyTree := TreeBlock013L55
abbrev F11B013L56 : RowFamilyTree := TreeBlock013L56
abbrev F11B013L57 : RowFamilyTree := TreeBlock013L57
abbrev F11B013L58 : RowFamilyTree := TreeBlock013L58
abbrev F11B013L59 : RowFamilyTree := TreeBlock013L59
abbrev F11B013L60 : RowFamilyTree := TreeBlock013L60
abbrev F11B013L61 : RowFamilyTree := TreeBlock013L61
abbrev F11B013L62 : RowFamilyTree := TreeBlock013L62
abbrev F11B013L63 : RowFamilyTree := TreeBlock013L63
abbrev F11B013 : RowFamilyTree := TreeBlock013
theorem F11B013L0_lift (row : List GridPoint) (h : FamilyMember row F11B013L0) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B013L1_lift (row : List GridPoint) (h : FamilyMember row F11B013L1) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B013L2_lift (row : List GridPoint) (h : FamilyMember row F11B013L2) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B013L3_lift (row : List GridPoint) (h : FamilyMember row F11B013L3) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B013L4_lift (row : List GridPoint) (h : FamilyMember row F11B013L4) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B013L5_lift (row : List GridPoint) (h : FamilyMember row F11B013L5) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B013L6_lift (row : List GridPoint) (h : FamilyMember row F11B013L6) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B013L7_lift (row : List GridPoint) (h : FamilyMember row F11B013L7) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B013L8_lift (row : List GridPoint) (h : FamilyMember row F11B013L8) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B013L9_lift (row : List GridPoint) (h : FamilyMember row F11B013L9) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B013L10_lift (row : List GridPoint) (h : FamilyMember row F11B013L10) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B013L11_lift (row : List GridPoint) (h : FamilyMember row F11B013L11) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B013L12_lift (row : List GridPoint) (h : FamilyMember row F11B013L12) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B013L13_lift (row : List GridPoint) (h : FamilyMember row F11B013L13) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B013L14_lift (row : List GridPoint) (h : FamilyMember row F11B013L14) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B013L15_lift (row : List GridPoint) (h : FamilyMember row F11B013L15) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B013L16_lift (row : List GridPoint) (h : FamilyMember row F11B013L16) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B013L17_lift (row : List GridPoint) (h : FamilyMember row F11B013L17) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B013L18_lift (row : List GridPoint) (h : FamilyMember row F11B013L18) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B013L19_lift (row : List GridPoint) (h : FamilyMember row F11B013L19) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B013L20_lift (row : List GridPoint) (h : FamilyMember row F11B013L20) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B013L21_lift (row : List GridPoint) (h : FamilyMember row F11B013L21) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B013L22_lift (row : List GridPoint) (h : FamilyMember row F11B013L22) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B013L23_lift (row : List GridPoint) (h : FamilyMember row F11B013L23) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B013L24_lift (row : List GridPoint) (h : FamilyMember row F11B013L24) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B013L25_lift (row : List GridPoint) (h : FamilyMember row F11B013L25) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B013L26_lift (row : List GridPoint) (h : FamilyMember row F11B013L26) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B013L27_lift (row : List GridPoint) (h : FamilyMember row F11B013L27) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B013L28_lift (row : List GridPoint) (h : FamilyMember row F11B013L28) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B013L29_lift (row : List GridPoint) (h : FamilyMember row F11B013L29) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B013L30_lift (row : List GridPoint) (h : FamilyMember row F11B013L30) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B013L31_lift (row : List GridPoint) (h : FamilyMember row F11B013L31) : FamilyMember row F11B013 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B013L32_lift (row : List GridPoint) (h : FamilyMember row F11B013L32) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B013L33_lift (row : List GridPoint) (h : FamilyMember row F11B013L33) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B013L34_lift (row : List GridPoint) (h : FamilyMember row F11B013L34) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B013L35_lift (row : List GridPoint) (h : FamilyMember row F11B013L35) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B013L36_lift (row : List GridPoint) (h : FamilyMember row F11B013L36) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B013L37_lift (row : List GridPoint) (h : FamilyMember row F11B013L37) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B013L38_lift (row : List GridPoint) (h : FamilyMember row F11B013L38) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B013L39_lift (row : List GridPoint) (h : FamilyMember row F11B013L39) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B013L40_lift (row : List GridPoint) (h : FamilyMember row F11B013L40) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B013L41_lift (row : List GridPoint) (h : FamilyMember row F11B013L41) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B013L42_lift (row : List GridPoint) (h : FamilyMember row F11B013L42) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B013L43_lift (row : List GridPoint) (h : FamilyMember row F11B013L43) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B013L44_lift (row : List GridPoint) (h : FamilyMember row F11B013L44) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B013L45_lift (row : List GridPoint) (h : FamilyMember row F11B013L45) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B013L46_lift (row : List GridPoint) (h : FamilyMember row F11B013L46) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B013L47_lift (row : List GridPoint) (h : FamilyMember row F11B013L47) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B013L48_lift (row : List GridPoint) (h : FamilyMember row F11B013L48) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B013L49_lift (row : List GridPoint) (h : FamilyMember row F11B013L49) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B013L50_lift (row : List GridPoint) (h : FamilyMember row F11B013L50) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B013L51_lift (row : List GridPoint) (h : FamilyMember row F11B013L51) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B013L52_lift (row : List GridPoint) (h : FamilyMember row F11B013L52) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B013L53_lift (row : List GridPoint) (h : FamilyMember row F11B013L53) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B013L54_lift (row : List GridPoint) (h : FamilyMember row F11B013L54) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B013L55_lift (row : List GridPoint) (h : FamilyMember row F11B013L55) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B013L56_lift (row : List GridPoint) (h : FamilyMember row F11B013L56) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B013L57_lift (row : List GridPoint) (h : FamilyMember row F11B013L57) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B013L58_lift (row : List GridPoint) (h : FamilyMember row F11B013L58) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B013L59_lift (row : List GridPoint) (h : FamilyMember row F11B013L59) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B013L60_lift (row : List GridPoint) (h : FamilyMember row F11B013L60) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B013L61_lift (row : List GridPoint) (h : FamilyMember row F11B013L61) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B013L62_lift (row : List GridPoint) (h : FamilyMember row F11B013L62) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B013L63_lift (row : List GridPoint) (h : FamilyMember row F11B013L63) : FamilyMember row F11B013 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
