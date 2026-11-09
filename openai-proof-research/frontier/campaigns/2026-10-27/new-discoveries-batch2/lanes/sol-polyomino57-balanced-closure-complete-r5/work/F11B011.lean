import TreeBlock011
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
namespace Polyomino57

abbrev F11B011L0 : RowFamilyTree := TreeBlock011L0
abbrev F11B011L1 : RowFamilyTree := TreeBlock011L1
abbrev F11B011L2 : RowFamilyTree := TreeBlock011L2
abbrev F11B011L3 : RowFamilyTree := TreeBlock011L3
abbrev F11B011L4 : RowFamilyTree := TreeBlock011L4
abbrev F11B011L5 : RowFamilyTree := TreeBlock011L5
abbrev F11B011L6 : RowFamilyTree := TreeBlock011L6
abbrev F11B011L7 : RowFamilyTree := TreeBlock011L7
abbrev F11B011L8 : RowFamilyTree := TreeBlock011L8
abbrev F11B011L9 : RowFamilyTree := TreeBlock011L9
abbrev F11B011L10 : RowFamilyTree := TreeBlock011L10
abbrev F11B011L11 : RowFamilyTree := TreeBlock011L11
abbrev F11B011L12 : RowFamilyTree := TreeBlock011L12
abbrev F11B011L13 : RowFamilyTree := TreeBlock011L13
abbrev F11B011L14 : RowFamilyTree := TreeBlock011L14
abbrev F11B011L15 : RowFamilyTree := TreeBlock011L15
abbrev F11B011L16 : RowFamilyTree := TreeBlock011L16
abbrev F11B011L17 : RowFamilyTree := TreeBlock011L17
abbrev F11B011L18 : RowFamilyTree := TreeBlock011L18
abbrev F11B011L19 : RowFamilyTree := TreeBlock011L19
abbrev F11B011L20 : RowFamilyTree := TreeBlock011L20
abbrev F11B011L21 : RowFamilyTree := TreeBlock011L21
abbrev F11B011L22 : RowFamilyTree := TreeBlock011L22
abbrev F11B011L23 : RowFamilyTree := TreeBlock011L23
abbrev F11B011L24 : RowFamilyTree := TreeBlock011L24
abbrev F11B011L25 : RowFamilyTree := TreeBlock011L25
abbrev F11B011L26 : RowFamilyTree := TreeBlock011L26
abbrev F11B011L27 : RowFamilyTree := TreeBlock011L27
abbrev F11B011L28 : RowFamilyTree := TreeBlock011L28
abbrev F11B011L29 : RowFamilyTree := TreeBlock011L29
abbrev F11B011L30 : RowFamilyTree := TreeBlock011L30
abbrev F11B011L31 : RowFamilyTree := TreeBlock011L31
abbrev F11B011L32 : RowFamilyTree := TreeBlock011L32
abbrev F11B011L33 : RowFamilyTree := TreeBlock011L33
abbrev F11B011L34 : RowFamilyTree := TreeBlock011L34
abbrev F11B011L35 : RowFamilyTree := TreeBlock011L35
abbrev F11B011L36 : RowFamilyTree := TreeBlock011L36
abbrev F11B011L37 : RowFamilyTree := TreeBlock011L37
abbrev F11B011L38 : RowFamilyTree := TreeBlock011L38
abbrev F11B011L39 : RowFamilyTree := TreeBlock011L39
abbrev F11B011L40 : RowFamilyTree := TreeBlock011L40
abbrev F11B011L41 : RowFamilyTree := TreeBlock011L41
abbrev F11B011L42 : RowFamilyTree := TreeBlock011L42
abbrev F11B011L43 : RowFamilyTree := TreeBlock011L43
abbrev F11B011L44 : RowFamilyTree := TreeBlock011L44
abbrev F11B011L45 : RowFamilyTree := TreeBlock011L45
abbrev F11B011L46 : RowFamilyTree := TreeBlock011L46
abbrev F11B011L47 : RowFamilyTree := TreeBlock011L47
abbrev F11B011L48 : RowFamilyTree := TreeBlock011L48
abbrev F11B011L49 : RowFamilyTree := TreeBlock011L49
abbrev F11B011L50 : RowFamilyTree := TreeBlock011L50
abbrev F11B011L51 : RowFamilyTree := TreeBlock011L51
abbrev F11B011L52 : RowFamilyTree := TreeBlock011L52
abbrev F11B011L53 : RowFamilyTree := TreeBlock011L53
abbrev F11B011L54 : RowFamilyTree := TreeBlock011L54
abbrev F11B011L55 : RowFamilyTree := TreeBlock011L55
abbrev F11B011L56 : RowFamilyTree := TreeBlock011L56
abbrev F11B011L57 : RowFamilyTree := TreeBlock011L57
abbrev F11B011L58 : RowFamilyTree := TreeBlock011L58
abbrev F11B011L59 : RowFamilyTree := TreeBlock011L59
abbrev F11B011L60 : RowFamilyTree := TreeBlock011L60
abbrev F11B011L61 : RowFamilyTree := TreeBlock011L61
abbrev F11B011L62 : RowFamilyTree := TreeBlock011L62
abbrev F11B011L63 : RowFamilyTree := TreeBlock011L63
abbrev F11B011 : RowFamilyTree := TreeBlock011
theorem F11B011L0_lift (row : List GridPoint) (h : FamilyMember row F11B011L0) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B011L1_lift (row : List GridPoint) (h : FamilyMember row F11B011L1) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B011L2_lift (row : List GridPoint) (h : FamilyMember row F11B011L2) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B011L3_lift (row : List GridPoint) (h : FamilyMember row F11B011L3) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B011L4_lift (row : List GridPoint) (h : FamilyMember row F11B011L4) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B011L5_lift (row : List GridPoint) (h : FamilyMember row F11B011L5) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B011L6_lift (row : List GridPoint) (h : FamilyMember row F11B011L6) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B011L7_lift (row : List GridPoint) (h : FamilyMember row F11B011L7) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B011L8_lift (row : List GridPoint) (h : FamilyMember row F11B011L8) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B011L9_lift (row : List GridPoint) (h : FamilyMember row F11B011L9) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B011L10_lift (row : List GridPoint) (h : FamilyMember row F11B011L10) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B011L11_lift (row : List GridPoint) (h : FamilyMember row F11B011L11) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B011L12_lift (row : List GridPoint) (h : FamilyMember row F11B011L12) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B011L13_lift (row : List GridPoint) (h : FamilyMember row F11B011L13) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B011L14_lift (row : List GridPoint) (h : FamilyMember row F11B011L14) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B011L15_lift (row : List GridPoint) (h : FamilyMember row F11B011L15) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B011L16_lift (row : List GridPoint) (h : FamilyMember row F11B011L16) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B011L17_lift (row : List GridPoint) (h : FamilyMember row F11B011L17) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B011L18_lift (row : List GridPoint) (h : FamilyMember row F11B011L18) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B011L19_lift (row : List GridPoint) (h : FamilyMember row F11B011L19) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B011L20_lift (row : List GridPoint) (h : FamilyMember row F11B011L20) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B011L21_lift (row : List GridPoint) (h : FamilyMember row F11B011L21) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B011L22_lift (row : List GridPoint) (h : FamilyMember row F11B011L22) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B011L23_lift (row : List GridPoint) (h : FamilyMember row F11B011L23) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B011L24_lift (row : List GridPoint) (h : FamilyMember row F11B011L24) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B011L25_lift (row : List GridPoint) (h : FamilyMember row F11B011L25) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B011L26_lift (row : List GridPoint) (h : FamilyMember row F11B011L26) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B011L27_lift (row : List GridPoint) (h : FamilyMember row F11B011L27) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B011L28_lift (row : List GridPoint) (h : FamilyMember row F11B011L28) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B011L29_lift (row : List GridPoint) (h : FamilyMember row F11B011L29) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B011L30_lift (row : List GridPoint) (h : FamilyMember row F11B011L30) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B011L31_lift (row : List GridPoint) (h : FamilyMember row F11B011L31) : FamilyMember row F11B011 := by
  exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B011L32_lift (row : List GridPoint) (h : FamilyMember row F11B011L32) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B011L33_lift (row : List GridPoint) (h : FamilyMember row F11B011L33) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B011L34_lift (row : List GridPoint) (h : FamilyMember row F11B011L34) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B011L35_lift (row : List GridPoint) (h : FamilyMember row F11B011L35) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B011L36_lift (row : List GridPoint) (h : FamilyMember row F11B011L36) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B011L37_lift (row : List GridPoint) (h : FamilyMember row F11B011L37) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B011L38_lift (row : List GridPoint) (h : FamilyMember row F11B011L38) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B011L39_lift (row : List GridPoint) (h : FamilyMember row F11B011L39) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B011L40_lift (row : List GridPoint) (h : FamilyMember row F11B011L40) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B011L41_lift (row : List GridPoint) (h : FamilyMember row F11B011L41) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B011L42_lift (row : List GridPoint) (h : FamilyMember row F11B011L42) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B011L43_lift (row : List GridPoint) (h : FamilyMember row F11B011L43) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B011L44_lift (row : List GridPoint) (h : FamilyMember row F11B011L44) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B011L45_lift (row : List GridPoint) (h : FamilyMember row F11B011L45) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B011L46_lift (row : List GridPoint) (h : FamilyMember row F11B011L46) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B011L47_lift (row : List GridPoint) (h : FamilyMember row F11B011L47) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B011L48_lift (row : List GridPoint) (h : FamilyMember row F11B011L48) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B011L49_lift (row : List GridPoint) (h : FamilyMember row F11B011L49) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B011L50_lift (row : List GridPoint) (h : FamilyMember row F11B011L50) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B011L51_lift (row : List GridPoint) (h : FamilyMember row F11B011L51) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B011L52_lift (row : List GridPoint) (h : FamilyMember row F11B011L52) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B011L53_lift (row : List GridPoint) (h : FamilyMember row F11B011L53) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B011L54_lift (row : List GridPoint) (h : FamilyMember row F11B011L54) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B011L55_lift (row : List GridPoint) (h : FamilyMember row F11B011L55) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (h))))))
theorem F11B011L56_lift (row : List GridPoint) (h : FamilyMember row F11B011L56) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inl (h))))))
theorem F11B011L57_lift (row : List GridPoint) (h : FamilyMember row F11B011L57) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (Or.inr (h))))))
theorem F11B011L58_lift (row : List GridPoint) (h : FamilyMember row F11B011L58) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl (h))))))
theorem F11B011L59_lift (row : List GridPoint) (h : FamilyMember row F11B011L59) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (h))))))
theorem F11B011L60_lift (row : List GridPoint) (h : FamilyMember row F11B011L60) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (h))))))
theorem F11B011L61_lift (row : List GridPoint) (h : FamilyMember row F11B011L61) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (h))))))
theorem F11B011L62_lift (row : List GridPoint) (h : FamilyMember row F11B011L62) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (h))))))
theorem F11B011L63_lift (row : List GridPoint) (h : FamilyMember row F11B011L63) : FamilyMember row F11B011 := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))
end Polyomino57
