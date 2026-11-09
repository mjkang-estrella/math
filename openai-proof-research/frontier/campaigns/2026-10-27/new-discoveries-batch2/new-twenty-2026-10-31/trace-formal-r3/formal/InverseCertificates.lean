import Mathlib.Data.List.Basic
import Mathlib.Data.Int.Basic
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
namespace TraceInverse
abbrev Data := List (List ℤ)
def entry (a : Data) (i j : ℕ) : ℤ := (a[i]?.getD [])[j]?.getD 0
def dot (a b : Data) (n i j : ℕ) : ℤ :=
  ((List.range n).map (fun k => entry a i k * entry b k j)).sum
def checker (a b : Data) (n : ℕ) (d : ℤ) : Bool :=
  (List.range n).all (fun i => (List.range n).all (fun j =>
    decide (dot a b n i j = if i = j then d else 0)))
/-- Soundness: checker truth implies the literal scaled inverse product entrywise. -/
theorem checker_sound (a b : Data) (n : ℕ) (d : ℤ)
    (h : checker a b n d = true) (i j : ℕ) (hi : i < n) (hj : j < n) :
    dot a b n i j = if i = j then d else 0 := by
  simp only [checker, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h i hi j hj
/-- Multidegree [0, 0, 2]; 1 by 1. Matrix entries still require linkage to generator evaluation. -/
def a0 : Data := [[-8]]
def b0 : Data := [[-1]]
def d0 : ℤ := 8
theorem checked0 : checker a0 b0 1 d0 = true := by decide
theorem product0 (i j : ℕ) (hi : i < 1) (hj : j < 1) :
    dot a0 b0 1 i j = if i = j then d0 else 0 :=
  checker_sound _ _ _ _ checked0 i j hi hj
/-- Multidegree [0, 0, 3]; 1 by 1. Matrix entries still require linkage to generator evaluation. -/
def a1 : Data := [[-12]]
def b1 : Data := [[-1]]
def d1 : ℤ := 12
theorem checked1 : checker a1 b1 1 d1 = true := by decide
theorem product1 (i j : ℕ) (hi : i < 1) (hj : j < 1) :
    dot a1 b1 1 i j = if i = j then d1 else 0 :=
  checker_sound _ _ _ _ checked1 i j hi hj
/-- Multidegree [0, 0, 4]; 1 by 1. Matrix entries still require linkage to generator evaluation. -/
def a2 : Data := [[64]]
def b2 : Data := [[1]]
def d2 : ℤ := 64
theorem checked2 : checker a2 b2 1 d2 = true := by decide
theorem product2 (i j : ℕ) (hi : i < 1) (hj : j < 1) :
    dot a2 b2 1 i j = if i = j then d2 else 0 :=
  checker_sound _ _ _ _ checked2 i j hi hj
/-- Multidegree [0, 0, 5]; 1 by 1. Matrix entries still require linkage to generator evaluation. -/
def a3 : Data := [[96]]
def b3 : Data := [[1]]
def d3 : ℤ := 96
theorem checked3 : checker a3 b3 1 d3 = true := by decide
theorem product3 (i j : ℕ) (hi : i < 1) (hj : j < 1) :
    dot a3 b3 1 i j = if i = j then d3 else 0 :=
  checker_sound _ _ _ _ checked3 i j hi hj
/-- Multidegree [0, 0, 6]; 2 by 2. Matrix entries still require linkage to generator evaluation. -/
def a4 : Data := [[-512, 144], [8, 36]]
def b4 : Data := [[-9, 36], [2, 128]]
def d4 : ℤ := 4896
theorem checked4 : checker a4 b4 2 d4 = true := by decide
theorem product4 (i j : ℕ) (hi : i < 2) (hj : j < 2) :
    dot a4 b4 2 i j = if i = j then d4 else 0 :=
  checker_sound _ _ _ _ checked4 i j hi hj
/-- Multidegree [0, 1, 1]; 1 by 1. Matrix entries still require linkage to generator evaluation. -/
def a5 : Data := [[10]]
def b5 : Data := [[1]]
def d5 : ℤ := 10
theorem checked5 : checker a5 b5 1 d5 = true := by decide
theorem product5 (i j : ℕ) (hi : i < 1) (hj : j < 1) :
    dot a5 b5 1 i j = if i = j then d5 else 0 :=
  checker_sound _ _ _ _ checked5 i j hi hj
/-- Multidegree [0, 1, 2]; 1 by 1. Matrix entries still require linkage to generator evaluation. -/
def a6 : Data := [[-24]]
def b6 : Data := [[-1]]
def d6 : ℤ := 24
theorem checked6 : checker a6 b6 1 d6 = true := by decide
theorem product6 (i j : ℕ) (hi : i < 1) (hj : j < 1) :
    dot a6 b6 1 i j = if i = j then d6 else 0 :=
  checker_sound _ _ _ _ checked6 i j hi hj
/-- Multidegree [0, 1, 3]; 1 by 1. Matrix entries still require linkage to generator evaluation. -/
def a7 : Data := [[-80]]
def b7 : Data := [[-1]]
def d7 : ℤ := 80
theorem checked7 : checker a7 b7 1 d7 = true := by decide
theorem product7 (i j : ℕ) (hi : i < 1) (hj : j < 1) :
    dot a7 b7 1 i j = if i = j then d7 else 0 :=
  checker_sound _ _ _ _ checked7 i j hi hj
/-- Multidegree [0, 1, 4]; 2 by 2. Matrix entries still require linkage to generator evaluation. -/
def a8 : Data := [[192, -120], [-18, -36]]
def b8 : Data := [[6, -20], [-3, -32]]
def d8 : ℤ := 1512
theorem checked8 : checker a8 b8 2 d8 = true := by decide
theorem product8 (i j : ℕ) (hi : i < 2) (hj : j < 2) :
    dot a8 b8 2 i j = if i = j then d8 else 0 :=
  checker_sound _ _ _ _ checked8 i j hi hj
/-- Multidegree [0, 1, 5]; 2 by 2. Matrix entries still require linkage to generator evaluation. -/
def a9 : Data := [[640, 288], [24, 54]]
def b9 : Data := [[27, -144], [-12, 320]]
def d9 : ℤ := 13824
theorem checked9 : checker a9 b9 2 d9 = true := by decide
theorem product9 (i j : ℕ) (hi : i < 2) (hj : j < 2) :
    dot a9 b9 2 i j = if i = j then d9 else 0 :=
  checker_sound _ _ _ _ checked9 i j hi hj
/-- Multidegree [0, 2, 0]; 1 by 1. Matrix entries still require linkage to generator evaluation. -/
def a10 : Data := [[14]]
def b10 : Data := [[1]]
def d10 : ℤ := 14
theorem checked10 : checker a10 b10 1 d10 = true := by decide
theorem product10 (i j : ℕ) (hi : i < 1) (hj : j < 1) :
    dot a10 b10 1 i j = if i = j then d10 else 0 :=
  checker_sound _ _ _ _ checked10 i j hi hj
/-- Multidegree [0, 2, 1]; 1 by 1. Matrix entries still require linkage to generator evaluation. -/
def a11 : Data := [[-26]]
def b11 : Data := [[-1]]
def d11 : ℤ := 26
theorem checked11 : checker a11 b11 1 d11 = true := by decide
theorem product11 (i j : ℕ) (hi : i < 1) (hj : j < 1) :
    dot a11 b11 1 i j = if i = j then d11 else 0 :=
  checker_sound _ _ _ _ checked11 i j hi hj
/-- Multidegree [0, 2, 2]; 3 by 3. Matrix entries still require linkage to generator evaluation. -/
def a12 : Data := [[-112, 100, -200], [4, 36, 22], [40, 121, -99]]
def b12 : Data := [[-3113, -7150, 4700], [638, 9544, 832], [-478, 8776, -2216]]
def d12 : ℤ := 508056
theorem checked12 : checker a12 b12 3 d12 = true := by decide
theorem product12 (i j : ℕ) (hi : i < 3) (hj : j < 3) :
    dot a12 b12 3 i j = if i = j then d12 else 0 :=
  checker_sound _ _ _ _ checked12 i j hi hj
/-- Multidegree [0, 2, 3]; 3 by 3. Matrix entries still require linkage to generator evaluation. -/
def a13 : Data := [[-168, 208, -240], [-12, 10, -54], [0, -36, -33]]
def b13 : Data := [[-379, 2584, -1472], [-66, 924, -1032], [72, -1008, 136]]
def d13 : ℤ := 32664
theorem checked13 : checker a13 b13 3 d13 = true := by decide
theorem product13 (i j : ℕ) (hi : i < 3) (hj : j < 3) :
    dot a13 b13 3 i j = if i = j then d13 else 0 :=
  checker_sound _ _ _ _ checked13 i j hi hj
/-- Multidegree [0, 2, 4]; 5 by 5. Matrix entries still require linkage to generator evaluation. -/
def a14 : Data := [[896, -800, 1600, 312, 576], [8, 72, 44, -30, 81], [80, 242, -198, 0, 9], [8, 8, -6, 336, 324], [0, -360, 120, 0, 16]]
def b14 : Data := [[18414869, -68638156, 170140828, -23227928, 59206707], [3369316, 11159440, -38639056, -2132272, -112877064], [11189644, -1998800, -124067248, -10568848, -108901260], [7504124, -255242752, -64289024, 57671104, -109659312], [-8112720, 266078400, 61125600, 31290240, 113029272]]
def d14 : ℤ := 29376060192
theorem checked14 : checker a14 b14 5 d14 = true := by decide
theorem product14 (i j : ℕ) (hi : i < 5) (hj : j < 5) :
    dot a14 b14 5 i j = if i = j then d14 else 0 :=
  checker_sound _ _ _ _ checked14 i j hi hj
/-- Multidegree [0, 3, 0]; 1 by 1. Matrix entries still require linkage to generator evaluation. -/
def a15 : Data := [[-18]]
def b15 : Data := [[-1]]
def d15 : ℤ := 18
theorem checked15 : checker a15 b15 1 d15 = true := by decide
theorem product15 (i j : ℕ) (hi : i < 1) (hj : j < 1) :
    dot a15 b15 1 i j = if i = j then d15 else 0 :=
  checker_sound _ _ _ _ checked15 i j hi hj
/-- Multidegree [0, 3, 1]; 1 by 1. Matrix entries still require linkage to generator evaluation. -/
def a16 : Data := [[140]]
def b16 : Data := [[1]]
def d16 : ℤ := 140
theorem checked16 : checker a16 b16 1 d16 = true := by decide
theorem product16 (i j : ℕ) (hi : i < 1) (hj : j < 1) :
    dot a16 b16 1 i j = if i = j then d16 else 0 :=
  checker_sound _ _ _ _ checked16 i j hi hj
/-- Multidegree [0, 3, 2]; 3 by 3. Matrix entries still require linkage to generator evaluation. -/
def a17 : Data := [[-336, 144, -260], [-18, 60, 30], [-60, -72, -198]]
def b17 : Data := [[-810, 3936, 1660], [-447, 4244, 1230], [408, -2736, -1464]]
def d17 : ℤ := 101712
theorem checked17 : checker a17 b17 3 d17 = true := by decide
theorem product17 (i j : ℕ) (hi : i < 3) (hj : j < 3) :
    dot a17 b17 3 i j = if i = j then d17 else 0 :=
  checker_sound _ _ _ _ checked17 i j hi hj
/-- Multidegree [0, 3, 3]; 6 by 6. Matrix entries still require linkage to generator evaluation. -/
def a18 : Data := [[-1120, 1000, -2000, 216, 624, 456], [24, 216, 132, -180, -45, 165], [440, 1331, -1089, 0, 54, 60], [-8, -8, 6, -144, -126, 6], [0, -216, 72, 0, 80, 88], [-32, 64, -72, -324, -64, 8]]
def b18 : Data := [[-10151767575, -16001452776, 21327177984, 8329372908, 67641813027, -1580092578], [440561988, 34510003104, -1384042560, -53026783728, -62856307620, 4688943480], [-3351602844, 38637722784, -11435440128, -65555451312, -43305930324, 5435952696], [2363722080, 591188096, 830716032, 47784583488, -9653048976, -82810682160], [-1976762016, 2412917568, -2373644736, -210945058560, 13438648296, 91095008256], [5620656312, 50900127552, 8116932672, 115247862432, 100225042992, -75752016624]]
def d18 : ℤ := 20353831109568
theorem checked18 : checker a18 b18 6 d18 = true := by decide
theorem product18 (i j : ℕ) (hi : i < 6) (hj : j < 6) :
    dot a18 b18 6 i j = if i = j then d18 else 0 :=
  checker_sound _ _ _ _ checked18 i j hi hj
/-- Multidegree [0, 4, 0]; 1 by 1. Matrix entries still require linkage to generator evaluation. -/
def a19 : Data := [[196]]
def b19 : Data := [[1]]
def d19 : ℤ := 196
theorem checked19 : checker a19 b19 1 d19 = true := by decide
theorem product19 (i j : ℕ) (hi : i < 1) (hj : j < 1) :
    dot a19 b19 1 i j = if i = j then d19 else 0 :=
  checker_sound _ _ _ _ checked19 i j hi hj
/-- Multidegree [0, 4, 1]; 2 by 2. Matrix entries still require linkage to generator evaluation. -/
def a20 : Data := [[-364, -180], [10, 180]]
def b20 : Data := [[-90, -90], [5, 182]]
def d20 : ℤ := 31860
theorem checked20 : checker a20 b20 2 d20 = true := by decide
theorem product20 (i j : ℕ) (hi : i < 2) (hj : j < 2) :
    dot a20 b20 2 i j = if i = j then d20 else 0 :=
  checker_sound _ _ _ _ checked20 i j hi hj
/-- Multidegree [0, 4, 2]; 5 by 5. Matrix entries still require linkage to generator evaluation. -/
def a21 : Data := [[-1568, 1400, -2800, 432, 676], [8, 72, 44, -270, 25], [800, 2420, -1980, 108, 324], [8, 8, -6, 54, 49], [0, 0, 0, 144, 400]]
def b21 : Data := [[-9823071, -152036880, 13883394, -1112357340, 151121520], [5145240, 204883872, -7400928, 1543675968, -204606252], [2313552, 188899296, -11701344, 1434691296, -181987704], [1411000, 19544000, -3357200, 592732000, -73496428], [-507960, -7035840, 1208592, -213383520, 67444056]]
def d21 : ℤ := 16394136768
theorem checked21 : checker a21 b21 5 d21 = true := by decide
theorem product21 (i j : ℕ) (hi : i < 5) (hj : j < 5) :
    dot a21 b21 5 i j = if i = j then d21 else 0 :=
  checker_sound _ _ _ _ checked21 i j hi hj
/-- Multidegree [0, 5, 0]; 1 by 1. Matrix entries still require linkage to generator evaluation. -/
def a22 : Data := [[-252]]
def b22 : Data := [[-1]]
def d22 : ℤ := 252
theorem checked22 : checker a22 b22 1 d22 = true := by decide
theorem product22 (i j : ℕ) (hi : i < 1) (hj : j < 1) :
    dot a22 b22 1 i j = if i = j then d22 else 0 :=
  checker_sound _ _ _ _ checked22 i j hi hj
/-- Multidegree [0, 5, 1]; 2 by 2. Matrix entries still require linkage to generator evaluation. -/
def a23 : Data := [[1960, 468], [24, 150]]
def b23 : Data := [[75, -234], [-12, 980]]
def d23 : ℤ := 141384
theorem checked23 : checker a23 b23 2 d23 = true := by decide
theorem product23 (i j : ℕ) (hi : i < 2) (hj : j < 2) :
    dot a23 b23 2 i j = if i = j then d23 else 0 :=
  checker_sound _ _ _ _ checked23 i j hi hj
/-- Multidegree [0, 6, 0]; 2 by 2. Matrix entries still require linkage to generator evaluation. -/
def a24 : Data := [[2744, 324], [8, 900]]
def b24 : Data := [[225, -81], [-2, 686]]
def d24 : ℤ := 616752
theorem checked24 : checker a24 b24 2 d24 = true := by decide
theorem product24 (i j : ℕ) (hi : i < 2) (hj : j < 2) :
    dot a24 b24 2 i j = if i = j then d24 else 0 :=
  checker_sound _ _ _ _ checked24 i j hi hj
/-- Multidegree [1, 0, 1]; 1 by 1. Matrix entries still require linkage to generator evaluation. -/
def a25 : Data := [[3]]
def b25 : Data := [[1]]
def d25 : ℤ := 3
theorem checked25 : checker a25 b25 1 d25 = true := by decide
theorem product25 (i j : ℕ) (hi : i < 1) (hj : j < 1) :
    dot a25 b25 1 i j = if i = j then d25 else 0 :=
  checker_sound _ _ _ _ checked25 i j hi hj
/-- Multidegree [1, 0, 2]; 1 by 1. Matrix entries still require linkage to generator evaluation. -/
def a26 : Data := [[-7]]
def b26 : Data := [[-1]]
def d26 : ℤ := 7
theorem checked26 : checker a26 b26 1 d26 = true := by decide
theorem product26 (i j : ℕ) (hi : i < 1) (hj : j < 1) :
    dot a26 b26 1 i j = if i = j then d26 else 0 :=
  checker_sound _ _ _ _ checked26 i j hi hj
/-- Multidegree [1, 0, 3]; 1 by 1. Matrix entries still require linkage to generator evaluation. -/
def a27 : Data := [[-24]]
def b27 : Data := [[-1]]
def d27 : ℤ := 24
theorem checked27 : checker a27 b27 1 d27 = true := by decide
theorem product27 (i j : ℕ) (hi : i < 1) (hj : j < 1) :
    dot a27 b27 1 i j = if i = j then d27 else 0 :=
  checker_sound _ _ _ _ checked27 i j hi hj
/-- Multidegree [1, 0, 4]; 2 by 2. Matrix entries still require linkage to generator evaluation. -/
def a28 : Data := [[0, -36], [-14, -12]]
def b28 : Data := [[6, -18], [-7, 0]]
def d28 : ℤ := 252
theorem checked28 : checker a28 b28 2 d28 = true := by decide
theorem product28 (i j : ℕ) (hi : i < 2) (hj : j < 2) :
    dot a28 b28 2 i j = if i = j then d28 else 0 :=
  checker_sound _ _ _ _ checked28 i j hi hj
/-- Multidegree [1, 0, 5]; 2 by 2. Matrix entries still require linkage to generator evaluation. -/
def a29 : Data := [[192, 0], [8, 42]]
def b29 : Data := [[21, 0], [-4, 96]]
def d29 : ℤ := 4032
theorem checked29 : checker a29 b29 2 d29 = true := by decide
theorem product29 (i j : ℕ) (hi : i < 2) (hj : j < 2) :
    dot a29 b29 2 i j = if i = j then d29 else 0 :=
  checker_sound _ _ _ _ checked29 i j hi hj
/-- Multidegree [1, 1, 0]; 1 by 1. Matrix entries still require linkage to generator evaluation. -/
def a30 : Data := [[8]]
def b30 : Data := [[1]]
def d30 : ℤ := 8
theorem checked30 : checker a30 b30 1 d30 = true := by decide
theorem product30 (i j : ℕ) (hi : i < 1) (hj : j < 1) :
    dot a30 b30 1 i j = if i = j then d30 else 0 :=
  checker_sound _ _ _ _ checked30 i j hi hj
/-- Multidegree [1, 1, 1]; 2 by 2. Matrix entries still require linkage to generator evaluation. -/
def a31 : Data := [[-3, -23], [-5, 7]]
def b31 : Data := [[-7, -23], [-5, 3]]
def d31 : ℤ := 136
theorem checked31 : checker a31 b31 2 d31 = true := by decide
theorem product31 (i j : ℕ) (hi : i < 2) (hj : j < 2) :
    dot a31 b31 2 i j = if i = j then d31 else 0 :=
  checker_sound _ _ _ _ checked31 i j hi hj
/-- Multidegree [1, 1, 2]; 4 by 4. Matrix entries still require linkage to generator evaluation. -/
def a32 : Data := [[-64, 30, -26, 58], [14, 12, 85, 7], [-34, -99, 172, 44], [8, 2, 15, -39]]
def b32 : Data := [[-210962, 114512, -57276, -357804], [99572, 193744, -87984, 83592], [23101, 114350, 22482, 80244], [-29283, 77406, -7614, -402084]]
def d32 : ℤ := 14189688
theorem checked32 : checker a32 b32 4 d32 = true := by decide
theorem product32 (i j : ℕ) (hi : i < 4) (hj : j < 4) :
    dot a32 b32 4 i j = if i = j then d32 else 0 :=
  checker_sound _ _ _ _ checked32 i j hi hj
/-- Multidegree [1, 1, 3]; 6 by 6. Matrix entries still require linkage to generator evaluation. -/
def a33 : Data := [[24, 184, -96, -72, 0, -248], [-10, 14, -42, -18, -42, 26], [52, 52, 0, 27, -143, 204], [-58, 30, -192, -18, -46, -74], [-160, 140, 0, -32, -66, -20], [-60, 124, -36, 120, 64, 36]]
def b33 : Data := [[82594854, 57429588, 60467880, -54323304, -127302840, 2470158], [87200487, 487279936, -37304608, -170113196, -7673820, 106242488], [-1049690, -525929168, 82552624, -15705264, 93549432, -75502804], [-50654100, -1694962360, 315690496, 404252864, 70700376, -43481588], [16812900, 1394152520, -334710992, -351592768, -142372200, 203815756], [-24791433, 1062759308, -145433816, -242754388, -74751708, 120914698]]
def d33 : ℤ := 27923306928
theorem checked33 : checker a33 b33 6 d33 = true := by decide
theorem product33 (i j : ℕ) (hi : i < 6) (hj : j < 6) :
    dot a33 b33 6 i j = if i = j then d33 else 0 :=
  checker_sound _ _ _ _ checked33 i j hi hj
/-- Multidegree [1, 1, 4]; 7 by 7. Matrix entries still require linkage to generator evaluation. -/
def a34 : Data := [[512, -240, 208, -464, 36, 276, 0], [28, 24, 170, 14, 30, -42, 63], [-68, -198, 344, 88, 0, 0, 39], [16, 4, 30, -78, 1392, -720, 414], [-500, -480, -100, 20, 0, 0, 44], [32, 240, 208, -112, 270, -558, 128], [1280, 96, 1792, 256, 54, 810, -39]]
def b34 : Data := [[1403030794356, -981959306424, 12416753119136, 839751889008, -8316940621940, -3911874338872, -2477386803848], [-1238085928992, 2476317140544, -10775035981448, -659291084592, 5517970092776, 2896960520680, 1959915340664], [-550071860895, -311540489430, -5186174345404, -518824069602, 3928834229842, 2496765797630, 1430095207426], [-96798328551, -854564345190, 10789498104372, 844727030982, -6753701892462, -3862869672882, -1921547134542], [-741632842918, -3019602200656, -6363777716784, 159184859616, 4149908749152, 1969591275468, 1594459756608], [-714145424822, 3166911316944, -9526227719088, -340741788288, 5370559810944, 1143282921828, 1783853262752], [1230975721440, 15536132095680, 6862542996480, 787256280000, -5902233139776, -5419594233840, -2647581249360]]
def d34 : ℤ := 722188947453936
theorem checked34 : checker a34 b34 7 d34 = true := by decide
theorem product34 (i j : ℕ) (hi : i < 7) (hj : j < 7) :
    dot a34 b34 7 i j = if i = j then d34 else 0 :=
  checker_sound _ _ _ _ checked34 i j hi hj
/-- Multidegree [1, 2, 0]; 1 by 1. Matrix entries still require linkage to generator evaluation. -/
def a35 : Data := [[-8]]
def b35 : Data := [[-1]]
def d35 : ℤ := 8
theorem checked35 : checker a35 b35 1 d35 = true := by decide
theorem product35 (i j : ℕ) (hi : i < 1) (hj : j < 1) :
    dot a35 b35 1 i j = if i = j then d35 else 0 :=
  checker_sound _ _ _ _ checked35 i j hi hj
/-- Multidegree [1, 2, 1]; 4 by 4. Matrix entries still require linkage to generator evaluation. -/
def a36 : Data := [[42, 80, -295, -49], [4, 42, -49, 49], [-180, -187, -25, 11], [-2, -8, -3, -17]]
def b36 : Data := [[98504, -491358, 4396, -1697346], [-88430, 452208, -27700, 1540386], [-32071, 80790, -9236, 319329], [35685, -169254, 14148, -862443]]
def d36 : ℤ := 4775148
theorem checked36 : checker a36 b36 4 d36 = true := by decide
theorem product36 (i j : ℕ) (hi : i < 4) (hj : j < 4) :
    dot a36 b36 4 i j = if i = j then d36 else 0 :=
  checker_sound _ _ _ _ checked36 i j hi hj
/-- Multidegree [1, 2, 2]; 8 by 8. Matrix entries still require linkage to generator evaluation. -/
def a37 : Data := [[0, 64, -192, -78, -30, -230, -150, 266], [-14, 16, -63, 10, -30, 42, 24, -160], [-260, 64, 51, 162, 286, 286, 129, 146], [46, 18, 72, 7, 58, -30, 57, -2], [0, -120, -20, -160, -96, 84, -52, 96], [-32, 72, 16, -120, -60, 124, -76, -372], [0, 192, 15, -2, 12, 180, -124, -110], [0, -144, -32, -55, -40, -220, 14, -22]]
def b37 : Data := [[-42730089687340, 226525475447128, -8742341972328, 198716447107016, 109316223355276, -198266034094158, 276698837368848, 205834330182416], [71315414206400, -140427240320576, -22023632464704, -50008002676672, -97749756089792, 168492427568256, -252333145925376, -271985876932672], [-10860907099340, -237303014912296, -18966599588904, -95351153294072, -76236263514772, 120856407823746, -153368569527216, -132075567986672], [-50895603911420, 9779895100472, -8732808278472, -103129163717336, -40464907512676, -81572809687542, 81006351439632, 62636813020624], [-33073061848970, 244504360657268, 56305703529972, 248482742404636, 126800197220186, -207260556761913, 374466380768088, 358544510802616], [-24939384209640, 82740792914640, 8725544992080, 30515930022000, 59502813055560, -63227500554180, 87790503961440, 41656339382880], [53147413637700, -47343402213960, -13831225039560, 6653195131560, -54076293289380, 142655409916650, -297324736748400, -266996566664880], [19592653981490, -62210529348932, -4856657860548, -28871648812684, -8118165658274, 25174456538877, -75758841262392, -85631327562904]]
def d37 : ℤ := 14587121914481280
theorem checked37 : checker a37 b37 8 d37 = true := by decide
theorem product37 (i j : ℕ) (hi : i < 8) (hj : j < 8) :
    dot a37 b37 8 i j = if i = j then d37 else 0 :=
  checker_sound _ _ _ _ checked37 i j hi hj
/-- Multidegree [1, 2, 3]; 13 by 13. Matrix entries still require linkage to generator evaluation. -/
def a38 : Data := [[-336, -640, 2360, 392, 300, -600, -260, 580, 96, 0, 72, 552, -672], [8, 84, -98, 98, 72, 44, 510, 42, -48, -35, 45, -63, 142], [-360, -374, -50, 22, -1089, 891, 1892, 484, 0, 234, -78, -78, 10], [-4, -16, -6, -34, -4, 3, -30, 78, -432, -161, -522, 270, 82], [0, -300, 960, 40, -288, 96, -60, 12, 0, 220, 64, -56, 48], [-120, 32, 572, -132, 240, -270, 208, -112, -324, -128, -120, 248, -18], [0, -480, 576, 384, -36, 24, -672, -96, -324, -26, -6, -90, -24], [0, -640, 1664, 288, -275, 275, -1000, 10, 0, 0, -32, -176, -90], [-64, 12, -14, 50, 4, 4, -26, 14, 0, 0, 306, -126, -190], [-64, -120, 340, 252, -144, 452, 516, -156, 504, -64, -132, -36, 108], [384, 48, 168, 336, 128, 184, 44, -148, 0, 126, 54, -90, 28], [192, 40, 520, -88, 50, 22, -35, -15, 90, 36, 126, -72, -101], [352, 160, 1536, 768, 50, 320, 250, 50, 72, 0, 36, -36, -176]]
def b38 : Data := [[4586998073196872680441909, 29788473908110124452294784, -24734017750351925507186180, 84611520911953344916555064, 79318276647035102951302434, -53452728752835638851330308, 12920838837027613870883188, -45667135905292314951226548, 95899336564988667712454984, 42483249814569073430309156, -18392355796693018691338568, 42587447021068556919773400, -11598451453257667013621854], [-1901982679995847660651304, -7768384962029091780733864, 4859735226779353835618848, -18273538136934763988183104, -16240016876389339928229996, 11847205642810661668512696, -5493937721345717043503648, 10263506793765256641786816, -20123328174575785102063936, -10574500098085666504414804, 2715738353342703872373172, -11768292812558792264178144, 5037397125923558438280896], [-430537154209621819664152, -1823451175901584144349492, 1759182782493208847774072, -6439678755729304119075848, -5450246327307300481291404, 4470784752063504887310696, -1238496714213297961068496, 3745490834966117362907208, -7627149998784289380655328, -3288920222515391361527018, 823220532204916087563554, -2426688820249993563922680, 1321441640548777602546496], [-122600803532380894761616, -1804708431250541534799620, 610428312049933455762536, -3638647388764160739933656, -2031819641552134278520140, 246415314493784956860816, 3178626514356558188238752, -1308091592499187995459768, -4771285517612195094708080, -1013437593556847631712214, -1652935200908614724192638, -2423101377991431278617368, 2664072558504949070085736], [-2719541142881294012297708, -21036276245461593675352792, 20904493635105337310296288, -70461033687434858623884304, -70452520501478110362820896, 45813638742098657744346168, -14657772866450557198537592, 42334097006037579778932096, -80585995932184931867108776, -36557616788954715800965576, 23205615080818429051844164, -34809566743692856543091232, 6452340961640378231284256], [3125621293024319374685836, 21811821302090845346784584, -15370285402556401413844112, 54973034852790745530202160, 47329068272691337405333032, -27352935623953922640383688, -9842973379080382584483272, -14367840803033998904215296, 72061197210916702174956632, 24976902557022525695507072, 2878901577498997219501636, 7694756062249146357106464, -11626425229850875414012336], [-1283856141555400482917172, -8865189301119036476776848, 7846885903212410473661112, -25235598502124600580997344, -23473566229213730041830756, 14632225892462947352446512, 1447410895406750626674192, 9246402687837055023465624, -31442702458499187835833360, -11496259166881964430802860, 2589857852874485157262584, -5464577609241902440041168, 4050992700386676145102248], [2244550065765846142457984, 13255341366760654931889592, -6260818619310803780034424, 22558679321257514020453936, 18601764686018638714806324, -14722303287260087095821528, -3931269828982344675681112, -5752333137476187321558168, 26237778771267222711476008, 7908853153495152679837780, -1474210803952158333371476, 4827138093126107190595632, -4140736962933586498164848], [431192976337836510518094, -545974249855662556596744, -664432445149767072363072, -147214910936936732140320, 893402809811519916010608, -2504203248793560743453148, 1509397353518440087735260, -2183849908088909970521880, -1588782165310810239495864, 2231628753974926631901528, -2572588270279501586056416, 2827626451562007818307432, 270089497322141314880136], [-6960665552361573332052288, -52405922615476915792541592, 41630957447477684744640096, -140050254225872311376531904, -129288501735071292277023168, 85414108870069817928167160, -17891140318483963880765736, 71209390935376621790245008, -164646244868443798517277192, -71750414839110183184154472, 34185848524663556973182724, -62774725051583239247269344, 18616748974650293549991624], [10534194240698566832467050, 72547536387963655491193368, -57193186807019326694831856, 190827930244531605153827040, 181547504018893328332303080, -112406639288520559955560308, 8832500509077716019781824, -88503278354369265575107080, 234666697393603950198543360, 94185977142825634062247884, -30432380549992254534315780, 66922028954987782748671080, -29750987296106319108775464], [14045571124751033515955734, 87184855980949130163257456, -72428636332847501110929872, 244179413223759761694536960, 230447208659753783131316904, -141882595870345294631138052, 9241404584030921372459224, -112534370284175335527359784, 295651732969728851413324808, 120469868808602805336431828, -36022230184336249812602768, 81734648329349372789449656, -37870464363464420751103840], [6335029306708585394660132, 50363347934443407046465000, -36828704372849156752024288, 120055468431478844951208592, 115783653241467523427335296, -71152952433083548037049144, 3321389862170163667613456, -53598575270936381712748608, 143913791621959310200578664, 58708212502677628435985344, -19166404474399439239498420, 38561985950691346678508304, -18940331389993918183812008]]
def d38 : ℤ := 1852188957766537769261003472
theorem checked38 : checker a38 b38 13 d38 = true := by decide
theorem product38 (i j : ℕ) (hi : i < 13) (hj : j < 13) :
    dot a38 b38 13 i j = if i = j then d38 else 0 :=
  checker_sound _ _ _ _ checked38 i j hi hj
/-- Multidegree [1, 3, 0]; 1 by 1. Matrix entries still require linkage to generator evaluation. -/
def a39 : Data := [[112]]
def b39 : Data := [[1]]
def d39 : ℤ := 112
theorem checked39 : checker a39 b39 1 d39 = true := by decide
theorem product39 (i j : ℕ) (hi : i < 1) (hj : j < 1) :
    dot a39 b39 1 i j = if i = j then d39 else 0 :=
  checker_sound _ _ _ _ checked39 i j hi hj
/-- Multidegree [1, 3, 1]; 6 by 6. Matrix entries still require linkage to generator evaluation. -/
def a40 : Data := [[-42, -322, -208, -54, -80, -342], [-10, 14, 35, 60, 48, 95], [520, 520, 306, 324, 352, 286], [-58, 30, -28, -3, -18, -19], [0, 0, -100, -288, -72, 52], [30, -62, -16, 270, 72, 38]]
def b40 : Data := [[-520215330, -3790206936, 117733944, -3040388928, 749098170, 1362200358], [-301773510, -1471888596, 317551806, 3353696760, 134566128, 66469986], [-564676686, 72900786, -353484999, -3709238736, -1935188808, -1810368672], [-754098338, -2627284058, -201171061, 55524952, -248205594, 1662814272], [3141199290, 10276396506, 1067179527, 3885356520, -253215069, -3162944688], [-913108482, -182061186, -316323837, -1445904192, 1056687612, 1348492800]]
def d40 : ℤ := 338181332664
theorem checked40 : checker a40 b40 6 d40 = true := by decide
theorem product40 (i j : ℕ) (hi : i < 6) (hj : j < 6) :
    dot a40 b40 6 i j = if i = j then d40 else 0 :=
  checker_sound _ _ _ _ checked40 i j hi hj
/-- Multidegree [1, 3, 2]; 13 by 13. Matrix entries still require linkage to generator evaluation. -/
def a41 : Data := [[-896, 420, -364, 812, 800, -1600, -2950, -490, 0, 192, 78, 598, -1186], [28, 24, 170, 14, 252, 154, -294, 294, -210, -72, -25, 35, 97], [-680, -1980, 3440, 880, -2057, 1683, -275, 121, 468, -96, -468, -468, -760], [16, 4, 30, -78, 16, -12, 6, 34, 69, 162, 203, -105, 146], [0, 0, 0, 0, -180, 60, 576, 24, 396, 48, 320, -280, -132], [-16, -120, -104, 56, 32, -36, 572, -132, 288, 144, 120, -248, -148], [0, 0, 0, 0, 180, -120, -216, -144, 0, 36, -4, -60, -32], [0, 0, 0, 0, -200, 200, 520, 90, 0, -36, -40, -220, 159], [96, 32, -208, 112, -6, -6, 7, -25, -12, -63, 0, 0, 32], [-160, -192, 688, -208, -360, 1130, 1020, 756, -144, -168, -352, -96, 1276], [-48, -128, -44, 148, -16, -23, -56, -112, -126, 0, -54, 90, 26], [96, 120, -84, -36, 25, 11, 325, -55, 84, 90, 126, -72, -24], [704, 220, 1100, 220, 100, 640, 960, 480, 0, 24, 204, -204, -8]]
def b41 : Data := [[-2467816841956799219652300, -9257256096057782662821780, -34144164684949592247320, 12063169737104759032727500, -12437879162880610699553325, 6163839243187553025275515, -5307254119550308872804260, -5961296144538191110608980, 21109736252148286470516800, -3536267184580832508535800, -14758781933501383715021340, -20544056424668268442986900, 5018852854767634906156510], [3565833996286218454201648, -3546102797829493509980800, 520998901065640908760768, -7781516773361720148725760, -1310555344415166485720068, -12974975473614849309655040, 7249442312953443758209884, 9092797614488986554292528, 2999251176946272584208752, 2985389437626851807897644, -11219454567090998468958888, 34005050649960520972033504, -67929590981335957413448], [476020461702545360208480, -9281075558580279917671300, -850803143048292422149480, -1399536566723147156782900, 6696995298805500786659275, -6559318165501513085595875, 11509059555513728348397770, 1066819036213344594989020, -17167614813879107103124840, 898960431599457642873160, 7654738505554176798860900, -15824672664646481264282700, 5261083127462224390618030], [3575536171119825549088512, -2524878369521334927933660, 286595434257322919661672, 2966341216505832360690900, -1579626071278484311186527, 5203212510451637661424635, -3057923147768103228277254, 3601582246470217893032052, 20326799109844013468245368, 2584218811254373811592156, 8010328887694505731384548, -1388945304361143342537684, 3529813452772377973068738], [-262171928206340467876504, 10355342333752102888704400, -744918212647816600793504, -10615639651250968793405920, 4671214272222690120061444, 6860030735978809401749980, 14540922202422573941997308, -10647605159739559819294304, -4199452496964449296920976, 2810444499251780735725388, 5707930664874013517211624, 5996939136716225771976608, -285079853756692830371136], [-562634304499125473796816, 22994959796707920311120480, 4166752307104832485131904, -12805896137226321662048960, -3465270147265602444705704, -4049594716083403459409880, 5049858811105577924987272, -12211477487405686238113536, 20786940823531833548247456, 3429009403684876547521912, -7849038164810873495393104, 72086671462479176028464832, -9827366372653215925626624], [-233397471969845404044764, -3209963662969666662798320, -1425219196397198827809744, -5543637833556031931732440, 4161516461612369703505524, 2354766396898635426132380, -3293252260333809484981102, 2438391148329439647995096, -14063433380993023191641816, 117896257041781395305858, 11638742361582490447576964, -7571602594026025128314552, 2404072087925883327837924], [1073468589032848632570372, 3870836963387795034707520, -1003002095068913924312688, 13068789447388045799859000, -9800390868232600882489872, 16003089387258615326515200, -32816394541026345714235974, 5145054105070295955809352, 2233287158213704207240968, -2325347586378875631390774, -16465322575779546046852092, -32500975474579454681315304, 2786447125145902687421628], [1389780569275165559730056, -11667521988647192229553360, 565412305381536518322176, -2169966937018102161933760, -1021789894583242137961036, 11256104775523420707574020, 1601931126544339709990188, -21963301760042707471575584, 23463130820307781487962864, 6568812571183062862298428, -25953118056238717176664376, -6112506367147786805104992, 441522610794390719105584], [2476305585596371204787928, 813513284385362219884080, 2599247861590208249502208, 26126428442314356709417760, -37896199128164140608833348, 23148481546589758908866980, -30980390725502937439152236, 1897267552910248278874848, 11072842688481583926324272, -682051191479559311992876, -22893118947276910849956168, 31451477983857128653542304, -1952414568706294199144928], [-1649775414672909342193200, 10744380976833972547815120, -810170925844524286502160, 1837022534681540304116880, 29100498845638293352283220, -20579061681385831595314860, 8390695422865868730685920, -5225983856082980708203440, -13338074839972354431181920, -1757316718857104943617280, 32859533254786427375090640, 7605813683472608765392800, -1196350885927620966214440], [-94276047416370683767176, -5970851070666094421400720, -641874706519893303670416, -7298599501966133635254240, 2485233086614290625641036, -781878027752204711677380, -17224546157379777068006628, -25996229161046036419579776, -4609885834831960240975344, 3840400499084914236321012, 10992003598765296007674456, 8021929386132627997272432, 802598446472918052557376], [548819130395419330892232, -12966309640170737131015680, -1452806809551535690700448, 9766618586523975535785840, 4351267712370609788484288, -4054476594413900681796480, 12547880242153014442326516, -2181018513808029826741968, 6073178045920086182730768, 4869835511804315207050356, 6601236538063490189252808, -19838459772578408312657424, 2930756447221538292152568]]
def d41 : ℤ := 6931369995127611529360666080
theorem checked41 : checker a41 b41 13 d41 = true := by decide
theorem product41 (i j : ℕ) (hi : i < 13) (hj : j < 13) :
    dot a41 b41 13 i j = if i = j then d41 else 0 :=
  checker_sound _ _ _ _ checked41 i j hi hj
/-- Multidegree [1, 4, 0]; 2 by 2. Matrix entries still require linkage to generator evaluation. -/
def a42 : Data := [[-112, -144], [16, 210]]
def b42 : Data := [[-105, -72], [8, 56]]
def d42 : ℤ := 10608
theorem checked42 : checker a42 b42 2 d42 = true := by decide
theorem product42 (i j : ℕ) (hi : i < 2) (hj : j < 2) :
    dot a42 b42 2 i j = if i = j then d42 else 0 :=
  checker_sound _ _ _ _ checked42 i j hi hj
/-- Multidegree [1, 4, 1]; 7 by 7. Matrix entries still require linkage to generator evaluation. -/
def a43 : Data := [[588, 1120, -4130, -686, 54, 414, 208], [8, 84, -98, 98, -150, 210, 40], [-3600, -3740, -500, 220, -936, -936, -576], [-4, -16, -6, -34, -87, 45, -63], [0, 0, 0, 0, 576, -504, 240], [60, -16, -286, 66, -270, 558, -144], [0, 0, 0, 0, 0, 0, 24]]
def b43 : Data := [[-2823321270, 71751093030, -488791086, 282197054160, 65990943954, 11118611700, 40722141056], [1819909740, -45328151340, 272473242, -180064481400, -42220198998, -7447266180, -28837145147], [540983850, -15147260280, 81687072, -58469828760, -13762129203, -2278771290, -7017239377], [-2000418750, 51957250740, -304660188, 196465981680, 46410639417, 7494591150, 20014054728], [1319684520, -34786820880, 209828976, -134620771320, -31000911819, -4679645040, -19871612381], [1508210880, -39756366720, 239804544, -153852310080, -35849994921, -5348165760, -18506600014], [0, 0, 0, 0, 0, 0, 8828009685]]
def d43 : ℤ := 211872232440
theorem checked43 : checker a43 b43 7 d43 = true := by decide
theorem product43 (i j : ℕ) (hi : i < 7) (hj : j < 7) :
    dot a43 b43 7 i j = if i = j then d43 else 0 :=
  checker_sound _ _ _ _ checked43 i j hi hj
/-- Multidegree [1, 5, 0]; 2 by 2. Matrix entries still require linkage to generator evaluation. -/
def a44 : Data := [[1568, 144], [28, 240]]
def b44 : Data := [[60, -36], [-7, 392]]
def d44 : ℤ := 93072
theorem checked44 : checker a44 b44 2 d44 = true := by decide
theorem product44 (i j : ℕ) (hi : i < 2) (hj : j < 2) :
    dot a44 b44 2 i j = if i = j then d44 else 0 :=
  checker_sound _ _ _ _ checked44 i j hi hj
/-- Multidegree [2, 0, 0]; 1 by 1. Matrix entries still require linkage to generator evaluation. -/
def a45 : Data := [[8]]
def b45 : Data := [[1]]
def d45 : ℤ := 8
theorem checked45 : checker a45 b45 1 d45 = true := by decide
theorem product45 (i j : ℕ) (hi : i < 1) (hj : j < 1) :
    dot a45 b45 1 i j = if i = j then d45 else 0 :=
  checker_sound _ _ _ _ checked45 i j hi hj
/-- Multidegree [2, 0, 1]; 1 by 1. Matrix entries still require linkage to generator evaluation. -/
def a46 : Data := [[18]]
def b46 : Data := [[1]]
def d46 : ℤ := 18
theorem checked46 : checker a46 b46 1 d46 = true := by decide
theorem product46 (i j : ℕ) (hi : i < 1) (hj : j < 1) :
    dot a46 b46 1 i j = if i = j then d46 else 0 :=
  checker_sound _ _ _ _ checked46 i j hi hj
/-- Multidegree [2, 0, 2]; 3 by 3. Matrix entries still require linkage to generator evaluation. -/
def a47 : Data := [[-64, 9, -25], [16, 4, 33], [44, 81, 53]]
def b47 : Data := [[-2461, -2502, 397], [604, -2292, 1712], [1120, 5580, -400]]
def d47 : ℤ := 134940
theorem checked47 : checker a47 b47 3 d47 = true := by decide
theorem product47 (i j : ℕ) (hi : i < 3) (hj : j < 3) :
    dot a47 b47 3 i j = if i = j then d47 else 0 :=
  checker_sound _ _ _ _ checked47 i j hi hj
/-- Multidegree [2, 0, 3]; 3 by 3. Matrix entries still require linkage to generator evaluation. -/
def a48 : Data := [[-96, -144, 0], [-48, -12, -14], [0, -12, 117]]
def b48 : Data := [[131, -1404, -168], [-468, 936, 112], [-48, 96, 480]]
def d48 : ℤ := 54816
theorem checked48 : checker a48 b48 3 d48 = true := by decide
theorem product48 (i j : ℕ) (hi : i < 3) (hj : j < 3) :
    dot a48 b48 3 i j = if i = j then d48 else 0 :=
  checker_sound _ _ _ _ checked48 i j hi hj
/-- Multidegree [2, 0, 4]; 5 by 5. Matrix entries still require linkage to generator evaluation. -/
def a49 : Data := [[512, -72, 200, -216, 0], [32, 8, 66, 36, 49], [88, 162, 106, 0, 169], [8, 2, -180, 432, 529], [400, -640, 170, 0, 121]]
def b49 : Data := [[90039165, 110730366, -116792856, 35792052, -38196618], [35818860, 82796616, -24620256, 11009712, -47275608], [-34684440, 268608240, 35015040, -39726240, 15998640], [56531780, 483584440, -236214240, 44386960, -59968040], [-59464800, -305501760, 206674560, -4273920, 55172160]]
def d49 : ℤ := 24373342080
theorem checked49 : checker a49 b49 5 d49 = true := by decide
theorem product49 (i j : ℕ) (hi : i < 5) (hj : j < 5) :
    dot a49 b49 5 i j = if i = j then d49 else 0 :=
  checker_sound _ _ _ _ checked49 i j hi hj
/-- Multidegree [2, 1, 0]; 1 by 1. Matrix entries still require linkage to generator evaluation. -/
def a50 : Data := [[5]]
def b50 : Data := [[1]]
def d50 : ℤ := 5
theorem checked50 : checker a50 b50 1 d50 = true := by decide
theorem product50 (i j : ℕ) (hi : i < 1) (hj : j < 1) :
    dot a50 b50 1 i j = if i = j then d50 else 0 :=
  checker_sound _ _ _ _ checked50 i j hi hj
/-- Multidegree [2, 1, 1]; 4 by 4. Matrix entries still require linkage to generator evaluation. -/
def a51 : Data := [[80, 24, 52, 84], [48, 14, -1, 1], [242, 153, 202, 74], [-4, -4, 114, 4]]
def b51 : Data := [[43817, 651356, -63888, 98932], [-168242, -854648, 219840, -320296], [-12766, 6200, 5664, 161752], [239406, -379992, -5472, -102840]]
def d51 : ℤ := 18913824
theorem checked51 : checker a51 b51 4 d51 = true := by decide
theorem product51 (i j : ℕ) (hi : i < 4) (hj : j < 4) :
    dot a51 b51 4 i j = if i = j then d51 else 0 :=
  checker_sound _ _ _ _ checked51 i j hi hj
/-- Multidegree [2, 1, 2]; 8 by 8. Matrix entries still require linkage to generator evaluation. -/
def a52 : Data := [[-192, -40, 0, -9, -69, 180, -241, -437], [-72, 12, -49, -10, 14, -36, 114, 52], [-66, -46, 221, -234, -234, -66, -218, 48], [36, 6, 92, 29, -15, 18, -91, -71], [16, -70, -55, -128, 112, -72, 36, 30], [64, -32, 32, -225, 465, 88, 553, -161], [54, -32, -65, 2, 30, -96, 42, 140], [24, 64, 0, 88, 484, 5, 468, -10]]
def b52 : Data := [[-35006499197966, 42528742204758, -41228893249892, 103431591357022, 41057355526502, 14892635841400, -53251962745324, -43456360720052], [-129807454968026, 232275347031642, -106100330845532, 230908409451418, 249023686237094, -36083426694368, -437493289986808, -65205539821052], [26085975922994, -54568289116734, 44828321937572, -30899004359866, -74606980739714, 6302941199696, 96122532085120, 31263778670972], [41903588791799, -45493455697593, 23116545800438, -32084680723879, -95471754089627, 3638988846284, 150054452961424, 26767211918426], [1583222657961, -68744834930709, 11415502666272, -60018509155569, 33224682744969, -21385827221640, -32955136361958, 36879813445962], [39393225890354, -241812732597918, 57095322853148, -277157799815194, -115240322380730, 848659653584, 82057653918472, 52390514759060], [10015399773819, 45027311454945, 899081721828, 30182096580561, -52673579300853, 25304994972540, 68860282850946, -14895441054594], [19013570502565, -152589408698739, 48569156888398, -187248173691089, -62531218421497, -13544445963008, 61378884020924, 48481292372638]]
def d52 : ℤ := 7795310387357448
theorem checked52 : checker a52 b52 8 d52 = true := by decide
theorem product52 (i j : ℕ) (hi : i < 8) (hj : j < 8) :
    dot a52 b52 8 i j = if i = j then d52 else 0 :=
  checker_sound _ _ _ _ checked52 i j hi hj
/-- Multidegree [2, 1, 3]; 13 by 13. Matrix entries still require linkage to generator evaluation. -/
def a53 : Data := [[-640, -192, -416, -672, 90, -78, 174, -250, -60, -432, 0, 0, -246], [96, 28, -2, 2, 24, 170, 14, 198, -36, 54, 35, -49, 19], [484, 306, 404, 148, 891, -1548, -396, 583, 0, 18, -338, -338, -950], [-8, -8, 228, 8, -2, -15, 39, 180, -144, -162, -667, 345, 136], [240, -400, 380, 280, -384, -80, 16, 102, 0, 48, 176, -154, -74], [128, 120, -296, 136, 900, 780, -420, -556, 144, 176, -240, 496, -980], [-1728, -80, -800, -160, -6, -112, -16, -120, 54, 48, 26, 390, -246], [480, 1408, -2624, 32, 605, 2200, -22, -35, 0, 4, 0, 0, 24], [-40, -48, -44, -84, -16, 104, -56, 6, 0, 198, 136, -56, -252], [0, 80, -208, 176, 96, -344, 104, -240, -144, 144, 88, 24, -576], [-96, -96, -72, 168, -256, -88, 296, 88, 18, -36, -84, 140, 78], [80, 16, -400, 64, 20, -14, -6, -45, -9, -9, 56, -32, -5], [720, 64, 592, -144, 20, 100, 20, 355, -54, 21, 0, 0, -112]]
def b53 : Data := [[-4516031417762018119294338, -74770399869755123496166776, -4601271587650202587370796, 5613018872265870163315288, -18980246105587037930974888, 5609368466034356432980293, -21629123453166401470978420, -6041444290161637941559332, 34965420402688828778128170, -14239769701138231494462396, 17595809654857805104843160, 143403523442382610558431784, 53163289910712670527453076], [-36118827583392132995897820, -261235767606081592737661680, 11450693444763161680002440, -17177637886545312955797440, 11958082357833822580410160, -43464206137600125711018850, 38802805469715198404207880, 48606053989845855870745400, -58211631512028705305395580, 48832193821686325686508850, -42950993572734666730201640, -213877460013937539203213280, 74104561139418073115056440], [-3756202878913975682314434, 17135105743453324437551192, -3346051073927322314941108, -16146865015182214424796016, 11494374026354371461921256, 2515835570170220481723529, -1624319619978417517267140, -101796702666228690779756, -58875928084576675173594170, 22956628258148068853912167, -20890085659247553746343840, -172240253096505583492271848, 1418708474281616867154028], [-29690472687811708408418814, 114000445490033095245813432, 6382676009366534224508052, -17012025466753606323841856, 86316947970941871933466296, 16751197560810987581846779, 14053878055654656803137700, 10102081249759266825593884, -183009520510918255855052790, 47001647493479061328959027, -5713870071563579040336260, -79346493232155248951788368, -52939677901066073112696532], [17448826042674548264756448, 421810642506341485322764656, -1527923911254605742912944, -51536736162715699476948608, -121102896863582974762527552, 53000883983136757961833132, -42342569408794257237968960, -46154128678899101803031648, -114953362696398935644921960, 9723366841038920012353216, 32442303046570468421430540, 53278027123668669870150056, -88164810263801045670280216], [16021805283134867253580152, 89291259557953825295604224, -9411783893268838006450496, 4345938629652587588227248, 42841915182253578704677952, 14932026126711481657602828, -10354274949840723397074960, 15043912325120389444170528, -6634154148864329388815920, -4147574136853185161621106, -7367379680285042768709800, -115116857719648306384348816, -31663673108347878007643024], [43536887385235438164701784, 257931775146262603395694608, -2086653977349392853714192, -55861873179225223794943504, -120835046490423977100044736, 19061398044540535465963136, -82871094862953160121268080, -18882543663332144294007424, 33385552985189081529862200, 34672168249801898197866798, 231594610209971149132645580, -127393877855287234506631032, -97433139967614608715750968], [-4059141369291918914237328, 130634266780968368397209264, 20775046120604525983815824, -2541506318578071161670752, 30866053046619804568797632, -4901752323392145768074012, 48844058097284241660044320, 3338684021578724282646688, -34621153019821525220749160, -40168480855127401537235516, 22826780848006849743852460, 54223979460174762427999144, 65658260627105045069894376], [-4125376324647411391876304, -380045581297334076788368848, 58386878004067735734896912, -103404367199324279841198816, -22622298927368160504036224, 35718537983132663930174324, -27205207313464271487431360, 22323991380126124751818784, 190806513463143054221118040, -219452349774267133099066788, 276084373702562030463761420, -109282774172959602497577368, -12822363619978650602240472], [-54488142264569524026560208, 110077300619769480561201744, -11766188338570197248346576, 26417399739397210582436448, -166072079145264289044059328, -1390387445662584285678132, -59832271328572585245647520, -36293593228178164344072672, 325621008980115024555977160, -12618514953667115512302756, 82758063565770801250197300, 71768033524133445695834904, -97554801796931886627231144], [-17732616544394668801017540, 87567204207704049440686560, -29216029151509858479053400, -104410118247895938363943200, 9648146915074585088112240, 5478946085243467360214670, 75661072178000304973930680, -15999159606907728995388600, -233753054591105202730571580, 53193257156786999974685550, -79210350970609535725934820, 111864216477111625167804600, 143127176044965203243250720], [-50626176559360856628156420, -102857653356342707578020720, -37574598496405072699647240, -6974602387503444447687200, -43251438939107255139337680, 24790099777139280381000250, 98421010085026920865880600, -25326596510889730403001560, -145474175080647132084379620, 15594608031451723588703550, -16359216941821641803482280, 255154692890984417424471360, 218385482836838841972785960], [-27249756059373943756702992, 133101474425974337700703536, -22485256119384358699855344, -5751959840720960498056928, -92754098630469323800760832, -3834238370582847642354668, -18414300447460702129669120, -29757019290184619598482528, -45557247043800215765596200, -22379521715395034267995764, -19170923250349986756997940, 113267438044946313749595816, -37346675594991867525649816]]
def d53 : ℤ := 70740390354705667960262800320
theorem checked53 : checker a53 b53 13 d53 = true := by decide
theorem product53 (i j : ℕ) (hi : i < 13) (hj : j < 13) :
    dot a53 b53 13 i j = if i = j then d53 else 0 :=
  checker_sound _ _ _ _ checked53 i j hi hj
/-- Multidegree [2, 2, 0]; 3 by 3. Matrix entries still require linkage to generator evaluation. -/
def a54 : Data := [[112, 64, -51], [16, 49, -45], [440, 289, 97]]
def b54 : Data := [[17758, -20947, -381], [-21352, 33304, 4224], [-16936, -4208, 4464]]
def d54 : ℤ := 1486104
theorem checked54 : checker a54 b54 3 d54 = true := by decide
theorem product54 (i j : ℕ) (hi : i < 3) (hj : j < 3) :
    dot a54 b54 3 i j = if i = j then d54 else 0 :=
  checker_sound _ _ _ _ checked54 i j hi hj
/-- Multidegree [2, 2, 1]; 8 by 8. Matrix entries still require linkage to generator evaluation. -/
def a55 : Data := [[-208, 252, -24, -184, -24, 50, 316, 336], [40, -12, -35, 49, 16, 36, -197, 241], [-396, -120, -442, -442, -288, -253, 236, -206], [-14, -18, -116, 60, -9, -6, -76, -42], [80, 0, -80, 70, -96, -42, -42, -232], [-64, -44, -30, 62, 270, -32, 38, -182], [36, 0, -10, -150, -12, 12, 18, -94], [30, 0, 64, 352, 99, 20, -436, -54]]
def b55 : Data := [[-3943358946137, 287933635140096, -31141350854894, -287426772437896, 329578488061732, 101402589326403, -18100944967647, -123368731100138], [180490062042118, 179591835086976, 9147605592916, -358391741946016, 361900450654312, 101463661412958, 101311342818378, 95255228848492], [-27641976577873, -97887397568736, 12492425957474, -280868612706224, -77010818329612, -50786032113273, -10630581411723, 82468840592198], [-10882016362104, -94104980705808, -27627341211888, 153595614009048, -3161475571776, -24146555943564, -223289294924484, -18113187207696], [26696611131452, 158129807348544, -4193006085496, -151693491633584, 77872195284368, 183264361286532, 40989558301212, -17763902352712], [-57208453847224, -586780202441568, -134604017945008, 1215788142781648, -678561074439616, -297883462656144, 299731144128816, -9342808443376], [-10430603936052, -81380612223504, -30767083165464, 100606102784664, -9706226454528, 5208983739288, -145804540028472, -111026136919848], [6086698377025, 160175114990400, 8290943107870, -131460960839920, 41034508259740, 22343880302265, -114774977147925, -47302148744870]]
def d55 : ℤ := 44217331195278240
theorem checked55 : checker a55 b55 8 d55 = true := by decide
theorem product55 (i j : ℕ) (hi : i < 8) (hj : j < 8) :
    dot a55 b55 8 i j = if i = j then d55 else 0 :=
  checker_sound _ _ _ _ checked55 i j hi hj
/-- Multidegree [2, 2, 2]; 21 by 21. Matrix entries still require linkage to generator evaluation. -/
def a56 : Data := [[-896, 800, -1600, 126, -350, -512, 408, 240, -208, 464, -885, -147, 520, 840, -120, -468, 0, 9, 69, 529, -1634], [32, 288, 176, 8, 66, 98, -90, 84, 595, 49, -98, 98, -6, 6, -54, -30, -56, 25, -35, 49, 326], [880, 2662, -2178, 1620, 1060, 578, 194, 1683, -2924, -748, 225, -99, 2222, 814, 69, 108, -416, 676, 676, 676, 1177], [8, 8, -6, 2, -180, 32, -84, 8, 60, -156, 3, 17, -228, -8, 54, 63, 207, 841, -435, 225, 178], [0, 144, -48, 0, 0, -250, 430, -240, -50, 10, 768, 32, 228, 168, 28, 240, 132, 256, -224, 196, 146], [-64, 128, -144, -450, 278, 16, 352, 120, 104, -56, 2145, -495, -296, 136, -64, -176, 288, 225, -465, 961, -632], [0, 648, -432, 0, 0, 400, 464, 30, 560, 80, -36, -24, 300, 60, -6, 32, -156, 4, 60, 900, 808], [0, 150, -150, 0, 0, 1024, -2032, 440, 1600, -16, -1144, -198, -820, 10, 16, 5, 0, 64, 352, 1936, 76], [-320, 20, 20, -128, 48, 72, -104, 24, -156, 84, -28, 100, 22, 42, 198, 0, -28, 1156, -476, 196, -850], [0, 0, 0, 128, -320, 200, -392, 240, -860, 260, -680, -504, -624, 528, 48, 384, 112, 484, 132, 36, 1384], [96, 32, 46, 256, -88, 12, 12, 32, 11, -37, 112, 224, 24, -56, -9, 36, 0, 36, -60, 100, 95], [192, 50, 22, 48, -108, 8, -56, 10, -7, -3, 130, -22, -250, 40, -9, -9, 40, 196, -112, 64, 135], [3168, 450, 2880, 88, 1562, 128, 1216, 40, 200, 40, 384, 192, 370, -90, -18, 119, 0, 144, -144, 144, -778], [0, 144, 240, 0, 0, 896, 196, 72, 1144, -264, -135, 189, -117, 21, -98, -16, -50, 100, -20, 4, 436], [2880, 360, 1320, 576, 3816, 200, -344, -120, 1780, 420, 1200, 128, -192, 408, -84, -132, -480, 256, 448, 784, 1308], [0, 0, -288, 0, 0, 0, 0, 0, 240, 80, 144, -80, 0, 0, 64, 48, 0, 0, 0, 64, -1216], [-160, 72, -232, -648, 680, 250, -290, -270, 1100, 140, -432, 144, 612, 0, 7, 6, 0, 36, 180, 900, 196], [0, 2106, -3510, 0, 0, 1764, -5220, 1449, 420, 84, -7452, 966, 936, -36, 315, -396, -156, 961, -837, 729, -261], [576, 1024, -208, 108, 36, 192, -768, 192, 24, -168, -330, 174, 128, -64, -416, -36, -140, 144, -192, 256, 670], [0, 0, 576, 0, 0, 0, -216, 0, 0, 0, 288, -96, 0, 0, 48, 72, 0, 484, -220, 100, 668], [4368, 350, 322, 2106, 1014, 300, 1872, -225, 75, 135, 1125, 297, 535, -85, -133, -195, -260, 49, 49, 49, -700]]
def b56 : Data := [[10431986842753835009944075789931507876778999258720, -88424246893539716070958856133685094610274310537040, 219517103708865578867904658555891029580731072768, 15260823014003105274110982362826032803153701189696, -57873746952614900469162935651973636929516823939264, -7370728248891230293123217950224172990576958153280, 22102341173592332587918780624260820849247906658576, -26902953290304566807449833672893302838557485368400, -50394692284038651579936306480959387437953364029528, 333392568260467322235079606017769762753491069324, 86882998546188153225144263421741350698641046779072, 113958236385219379164323903994216841150127873408112, 5732652695991683084716104931099418634538694768976, 14393531729507250025159476049251602071928814024144, 6836647539532635860749048477667811357164052750744, 88730080769670505164850482696737320878412172710227, 22359955522093687094389372092200508616181112797856, 1528937256616708852002935119600685819194457727552, 717731036510541743599806826967839127440621083120, 70545993927522540325868015734572283933601716092312, -13554552451153640952658266721324899389682588409920], [-27906761109240570085459021828951366917011415453696, 219080120331353580557982474972701350170361392381312, 2081814747092348058534855720984066965425405198080, -47119477550789494179706989115859680690195217785344, 142177367182096879297770451379430579139311484925952, 13477073450086035651745401078543975226538068902144, -53670670936502774274019179056345253040452305679744, 62947817170364529859691053915554792600386417071488, 115439204607134959867543792341177470226230026348224, -5136806764442739553284613000709611029691895224800, -226661088208405169428716976072732130665186779899136, -191773180949119376189693908452142216249368163704960, -10357099759992131353026598238206009305050195423616, -38161177257052224193587381533794415544128899990656, -19206174649936946911106381985287520243677017403328, -204491799989316223037537344912856072952450221093160, -45207210594002904774391038303741758960158655767296, -2754141052961410050709813152076097873108794889472, -3296720651546290591849650452104407366110439857280, -169679372910304233506656476706370736105421606479936, 33357088565827008257275987942460938299662347336704], [-5140573551117790661626783854386707893044730036480, 50186014980625843132254107622243623010385325981824, -9327740492456017828259357445805251545029323776, -14006667691910982557457686531101284192381837186816, 35229052765539318930431124243708434718851562395648, 2952906636080162096887972403574774436028179556480, -15148600699138714379668095132275457978194668986240, 17303823182028982031651467351977916428298071782400, 28960186499323893909929257625318107857555962314752, -1636338637796501086108977110557023997706677400896, -52558966726888938785882872870458179298980166823168, -55810954994961689265646855907980339496762636292992, -653303143835823106315625080574599104810527009408, -7606193994594791117017853830673956501160973256832, -5067736453794017453882513278653836762227060302912, -54002188378417543473344245576363262172877592698152, -12635049185573005564884911785424024073487654273664, -1001739753531107990100264110764795014895759382912, -1037015131363613048617121501458610728790518080640, -34450212733463443853188462435865343644383951111168, 7867770932661689268438040144263122465220124208512], [-12995272337637631514088222192389780401848978521088, 116638906049621118492334144308582719506563166740480, -442996759053581847631773428005587462046740642816, -17037721012963217091687003015041795684146439616000, 80451909995066359808548497671146307505053829689856, 8396423892214249208631789523539702056551893486336, -31134060415803899130334594927675242384571483299456, 38084041705075308140414295577006518844599602265600, 62414952104996894722133178135840417097509228978048, -1226803105367736844330957964202860027568251547264, -116926579932411810458746326241473566467717100021760, -156530391852108335585561652368685445655481618638592, -8466800918422840792517918264828705483886210765312, -19989134847439408797037487313699869879192286110976, -8959300427412566826219454372481243055340322937024, -116828036912990302532353082400113298093298134925248, -32984331847976507274735326928610191815680688378112, -1464410670980211835553707129537449422826608236800, -1984148272001034929837116273034889076124717630976, -87428745086137238594873721795822030016071878554368, 21847495299744694065249902327350661127988497483264], [-7769030993807099831111742492764901473799156539904, 53689741295734883433579534268303712368805649966592, -490027856185528970710280963401928807405028968192, -3302093051136582180218124216718843147242778611456, 36826204243089572535985568799281463415797990944000, 6302380355130018627906858117982616187903492500096, -13124179046766171908205318255252193723287766690176, 16257632137191958184311775375643950311469181766272, 31787952815944767430392936802156591931162436689856, 748620496018093453545589294678818239062122897056, -57948737753833665791735073067731191924881487194624, -88377813105773696387574787166619731095805304768512, -3234932455576608340504878688947003494115452876288, -10350919112250922464723715563940761345321477744896, -1567918215558591153212660920831831957122301182528, -57740326333339757567637435305145372802452898221072, -16359933663044581708995230983248198444407932153472, -373666943801385684522714462794339608890362393984, 189545102024090075859908234896444043905428422144, -52251383664405066175136878361430231133818174587200, 8453007569978786083398856629147957146067942630784], [-18724094133522946744151912536738511872023672560640, 125801225449958765236219607586970023163952478993408, 223071803855219876841591250322869369710745541376, -39506880766676363993784920236230118429607916005376, 84799408540208830977041921729450162817788762932992, 14498389552264449730214257923062036629143364856064, -37293948351802830997531750565528318639743488405888, 38120330618259309217021447161371373939586128817152, 77220110474812762851917715734342002695267079024896, 3321986597303432903098651909530201172199253065088, -130746000878932306409582158859390629208291136509952, -134626063416342288856208037176533388049356426744064, -7873068713781803864120606494231324458429352571904, -14095061391420075715548232226139125768639385347328, -13196538225439836323583591577725004186893664689408, -131501662096982673436808549109024395891278027168992, -23925335760998409202866400023772937223822530579712, -861263390889998092614333852842775898732539258624, -2176561957537809515513228414555056850223181674240, -103685400845234219080971649312688589361075371587520, 23747489602704973095925267993800178885579128203520], [3514434008932514313917780728675526481241793199360, -23422387636141190709274357625933371526632098585728, -564787548373363021633639816400715297261223010816, 13229291915243424656378757887009202306857788307712, -20019739836966054826528187948932727045812931107840, -1625204959300542830669376333455332035491178167680, 12643430564709197106661526700012258179618794502784, -8879256992248184472804062245684548800427435058944, -12841926755237601779615472919268811777414264989568, 1724991977813702232725677446671201472946738963520, 26618121695480156389707477948498306961560416987648, 11748366092921092778840495619099067854871762991488, 2363311977347345577925412014753233671670862244992, 4018539931582905969362482665846710268012140423296, 2575245440345474789770814615228055263320019527872, 22982694280225581412585992703307051416281336408648, 2799689923448299637090243232252648721183061459584, -311186118067897278744738069987460696272930442112, -203077099016119874088867683952714833855046255232, 11586344720390738917839779749732246838733318044864, -4366663022829188265529630302346195042773452902016], [30923681222533819739085904734148528811871881324544, -225765348229273815649838010594021391912132003233792, 580820371196354580584492190993742555019707026432, 61855471178633896933466655920336292827383825024512, -182718894960921507618124910364737784603466657350144, -12055454323882226383451450294608366684966622308608, 65690780688534573657059747087168698254029541598464, -78748167004354532807373659086833483521668222199040, -140437914449209416942261216612957816672068236861056, 9870117319141966565280554940678141075654905989824, 282875950875991933419927031446438885657322577998848, 236554570921761559109970219094612087910083227588096, 15156115662167242890985618299237718593840919464960, 38473068588415422315344060890879612607629344900096, 21542487356835741492142024942213150075899018918144, 255549696637722511768306817240339540047673937428448, 54864124611782872423075285460016738867428747334912, 3080504468969403288560576376323817269287350031104, 1626205810017730359291689681624256992157642891264, 193425441724279462258249914484664117984016902486400, -42714166527706372152502174176563270758177893750528], [7596289621506271566887068580871322257737128780032, -45717666207625499324808386082388464048047261348608, -191740828656885681617147211146932229185472843776, 16873854621634919019234473208250660136788916496384, -36101213446891739086484311663771074197878527012608, -5371764024331897110525644094713963298016327569152, 14395562514144999700912322168061123122207558006784, -16456237765413264314332598390134752628869747773952, -34504661281552968083305043786047678515745121521536, -710046592028476505493513353964032997547998368960, 53471758210086663195654126480599089561533040047616, 55248926910194200591252056448881265399640049135104, 2371214871853367327276353691492610786768698683904, 10099423746946152992378485033620127145906863387136, 5175520312627261702007912844838102041478221792960, 60523054959249657463782502715295862203061539546528, 11944143666260207184652385324047649758181514372608, 604891670825216226813799364048462607281325795584, -674033280623223926752175382220408273250203950464, 47072350364995011082483094010894501830890795711360, -8915198353703881248919687148913686214040754814208], [-20387324454605405470546525329727657029241725179904, 171670666482930324334435923204844892950299553821696, -996961826876044686892124912838472370482757160192, -41471330415427298027429555037310580182873251822336, 76004242475305293063303993742783741103837727420672, 19410431038233696483164669265868156419214864233600, -40929631293468892111953925816683585010815570034560, 34969440716527838506722231228664343829437738565504, 83690699166224780241508105329309526084395333653568, 13647843987885305488866188610982548941786736068640, -116348466432650287013944291523222255925731277127680, -148114863233131109816438051377822841789814673396992, -9744223543329743660088210935854928936839404681984, -32099994581470319652277488805828957667492007882240, -15177152208592399869899228592869808825839195200320, -131519783263861266490722877928788532612491884772896, -15495727310960755254471000427339646285361163253376, -1652977641524180483745695669747189369893292532096, -3235860146069504617221586777952504382226245579264, -113250492847269116001345033775248846570470674327488, 27253623734094703360335683384329445744976457497984], [-3084127070860845232473429506839071853840686898176, 17611934743490294698143179835462539352024586270208, 1048960053530970425078140786993085726593833991424, -10428698187027526617216036982810790197776309496320, 8098233848389679840000307355596651915319727607808, 3122173061935296057292187509666891359390588951040, -6935297527343148288936979279094027087962786604160, 2781956289991700070221832305198636873230005296640, 7963846888866761677501006705669562892575397813888, -77506957940371958747992298687189207119003341056, -8136954734686445384578217723559535481820079377920, 4366417121879779206889567866433208084483688456704, -1864715842589060259091811857330218095171957693440, -1783925052215386201238601972371010158707602292480, -1909342378682957024044704557097674070738676969728, -9822539248984835444196250836677929468642413317664, 1449194565479784766916400358123268308065920283392, -483200619710008981609789290857438430388850808832, -1061231723709601346147337529237602387567529639424, -7497480399966036829738838198134308541200934317056, 2466551525159962999550142717625791213895186523648], [1274182664573399059062013510101542644250255223552, -12913374330526675014239502278938671509685765826560, 896525452175044998852692912257623154800302412288, -8586432795180281247201699796784717799076210121472, -10752804138873550227347181717978311933701674373632, -1890319607101508462326352478438223919339080920960, -923660900185704806501528249692684127591270661888, -7211727092204683268962070172258387267321683164800, -2631678899242013710509285059822329002580153424832, 382541772472810394704968013237644094870231917408, 49344773748334491103199664643185348660335030492160, 56252062788244068328279807044953539871693596563456, 2154461835688747413905815737499080403038771340800, 4404351857541684154981554521873358053105373358080, 935369697921435526829358316854780418390932480000, 10022258400666164100969191397398911003154872440144, 12175183502910477653773137526899013536547460545920, 145825134079222977008241727100583234055909713024, -1788357282171583973980839574176163875071542124928, -902667556029594757073245412132446473686488656960, -5084030219274741006509108775752064431913479440512], [6532842856703462553494344206951938116122352783104, -40406048661087120752343736784139506310420600366208, 579868631553058205181441974917240580678210459648, 6369508624080532545435758001017355089615946267648, -27992965369174736961735821486163950908971182287616, -1801939236559801960495393215478019719508082947840, 6416516499563299981786317664630174094129095082880, -13813264346733265567399738035264380239060850333568, -26155651283494538277381053862358228215786347714112, 781798283422473789312167237482363900679055562912, 44925397735935798382561465923699127875488692729600, 30835843979529353144408319183734112710163815392640, 1877691248453993492895086523173709061626856388480, 8406148023580142646835610181074954143640387982464, 1608424713087947304538398709528402074623385080064, 43779827911989797045472961368156516594778786909656, 15359105065975822893043608963697442613934922095616, 972339797878123960083412375584834876242843788544, 378970229066354000795564136305428399932810719104, 47508342866929759194546627297268946586171706202176, -4687475170960948959646669717556695564907079352576], [28520251634461269446679827922676300604387479266816, -185251826269714992825667508309045244394588211308416, -514763332726862697276900741708940420434791473920, 17963913460809413062985292216382765911176138489088, -86439344451146680112476206084232003630375220080896, -15549451098026970606429256874570575670693340372864, 37789559320829908296088705504665323217240717014016, -45671396531337894281013504848881066536722210542080, -91182656944554183656407813688511190316282670513024, -1710787567538843320043091006302650032913142683776, 161805503771685243875347449575287687811813405938944, 196233379678853309160750651917105929406058607558272, 10883354691057906198353548335016313995135875931776, 41142562551623844464141769945350426877146173083264, 16288206992601165150397419482552580155258997954432, 152547888990596186194571187373983181655079876451608, 29619069229853957135657322626953189435657330970496, 3472945589069836865943892200102112052250002481792, -469213756620121297926128769797233860637631691264, 138864463885001547416388922416921708140484146525184, -29297493961104469335217757369824915793380237327488], [-16454357505895158778490646024890608573259670732288, 101359997417705361101853192121695088637471408235264, 3586181467468132163827839836365007679807402487296, -36844408941851380334657494893733329178069545481728, 82594110866370059654984537345093978489531836826112, 1346996945485225059843846702359006655673855172352, -19509200539196592434297207754367815558081596273664, 32972354465658186385428137103160220162180739217920, 53123225508614534640470409384855654796528950309120, -14995574581725922269943053928902276926227595388288, -126261773818497299624602322793683294419787047437312, -28744493506073007629029960407533087401848210798336, -3511919437484689564695124785295904145321813265152, -20036199257088293484811442126022574487614327156992, -8956610235851234276656085422861248379889097748608, -101806650834841659885040113373282378767157305022320, -26958610737912497592477044001367096622104247529216, 2150898969964643366761555274268528424958398501632, -24398710996492593927380667407743319185146469843200, -71769862336162346768163362671629379873888514722560, 13859680040668605856304160077792216763056064321792], [14848593091229483807490945642901764609177182281728, -151191993187584973200771364812745319207536544989440, -1751742154719326290591234389285965049522650262528, 40144331206697100444615891670304704033533329189376, -88260510852133416469074543945433959360875118638592, -13144669759771287339542008422145909537263411865344, 45917998514116312940046747597604362508824514905600, -45254445379604656342426157313250352741240668792320, -83660371109613081045085263512615690654040317236224, 10371131383113016766438691239826891076937577937920, 166579166703323757234603828319825255895065167573504, 110301865052501548064799853192924446887265316673280, 9409970143104978418905295915373786209902001807104, 24685210897264495311071808888680823215293320378624, 14927368498416648617741702415550730041750246841856, 166862725349333006246948859684519948414450909402576, 25760524131747855746413639215417335917097276627712, 1735426584529929914015553552157215266357077560576, 8927075624909994393963077681888735710590198464256, 109962010825119771625407656231616093503399874636288, -27298807798242257047322850957539704653836540541696], [-52254291801781626105160452924862541193708971036928, 428845757680289992814634576986675231299272550275456, 3503969274123790517817455101488292156790967335424, -68102810449130540710105425202067190751338141221376, 253355605982567467816913812453761210414101188950528, 38471069641292230557520878389317438946205354472704, -124381046119238787619259994165249610386940983675264, 115711171385841337666005612666060127170539665140864, 207140452494924552281204562443446925320890414256320, 4880947408011298601580465069614455358483728404000, -393172710164890973774419891916498554075661893203456, -405630268022560051586988816786144804854868626154624, -21282930453562843462472897625985919345570487455616, -72111545578381731111475853116957230007538617858944, -39842638303495124695838565882832464950282194922304, -392053483619834191190951250836290310249662583172360, -64947763230766370440420377307403353044693876103680, -5115631223461297685142524150684073596118855804672, -13970142353775898945070843398820382360762152215680, -325544316001262832521786425047341344658827683127488, 68937130628109766601979195083337062118077631082752], [-3320607515195926423654543167650868465964263851136, 30800645371009983166309833203712258156210546297408, 1666370023911779823960062946725327282080146312576, 2176423484193411360122109845747170538096682893184, 4167618921765302184238623753318498980890663302912, -598096511546483038386337138462626758767953225408, -9923432166603438942581114786343080510749819408512, 4913477639567616943850530926949083885853900561536, 16489706567240872799929954041745278407924573228736, 2229175597096326354870884241395456125579241421024, -22263393031232779709238577374794825294209386169344, -10318873250822529343660322436473670117289481065536, -2560313489891536418213680478998771413924228528192, -5400851405579182978064825652397713070682387532480, -3008578806883720527537349219531629748015941025248, -16646358820079184774457383475540505763675313628196, 4525408757964620563318508008086367714600248770880, -2307742578408145695590217558452419082462360850624, 1260411325529708222887910240433619729129668020544, -17486265795729221755114952181802062454124938132224, 4735825069391328672313268757368394797082324383424], [-21360536821739465231658775145582311871531650765824, 168980995159752741706935961327439630409134364985344, 5087336057926653383337116087819658900582173151744, -34261605062414659249955498127351359523785953567488, 85607915215598586829612599130308958917599569943040, 5823904911069460796021268518388336092368756639104, -50269070627324826657978257066539191837134707504128, 45472692809584102199275795343122595468788030209408, 84167310220632220255027246303159435452108533909568, 408508032275970693215463643475430370722679700064, -154546671319400162971011880146325916024136884333568, -106559931510123063102307948319822738204560207905792, -9156344120835978747270271214169781709770612548096, -29826270875408845482926153907503172371374282701312, -16640948654079612536693839477202707409147165685888, -142535526518285294221129774291830468106536203513904, -12851066099436765491660190166637099483630016480384, -5788245602951879808419268342914548013245733439360, -4874839277230458556364077641765568396967082446208, -127274952898147764533018992206375933170285556818496, 25535262797615050337618972139259962279313581309312], [6860897831069567079876336101766196904436968555904, -52561277778508983387381170235128297602084925665344, -901378675429045244840008557408674354448713801856, 10787715678208629293086540266194857158556908132480, -25677671967888499892998772461800705767926658426112, -2874541025245874304228189341309752484314970202432, 16474392503887191127709231560589683199629788460032, -8948286620949601751936594546819458535544775926144, -21797390553510269871952900718912572467081412193472, -963178411344653587317337202852178917995641444768, 48484148523126096877256238805926258491224237475328, 32855310853789373397568649436839626232790378785856, 3523876978331689305846665026426626490786861893696, 5078464389350589208680620738076284931809825830848, 4154778765451313154570293379054550520059701227616, 35658755955673528532188986923234776955368427041380, 6303174171096139488860892357361524332112386984640, 265950099649785856883390606398176494305905344448, 1687434521424707792361465668833171892973713805504, 32143143221959603767529999885520626647815666847360, -7481331552015567749595362487524726468366856785856], [1007656968203404740793423362730797079487851663104, -10079825618591045078558684070922372262112639709440, 36170732757007596023792897003226883629269041920, 3462516928420512434660996093900221287345845539584, -9290626193936269768303247896608770956291264647168, -587758613535317686249299528931081280497655459712, 4628624789279985747550053704904932899019699329152, -4763631616633057398258022265139610651535822441856, -8700586018321210142524895231892506846690249052864, 680404305691654561577731173336429055525414405920, 13619289205877439575634302862389570427748297551360, 15765040553955732171807834045485283583877692876032, -8821700247970232337471507228497577055951749888, 1369085311351877749648001989221575863168514452992, 1272107230666259353484744673648210239084142574464, 8781885980415338414757417067785394111367177142336, 3630803466870490014783123901585434394077303207552, 376783515823402575294478921469419815266135991936, -951272443463432904156470939461126803175334823552, 11425681455788467904991049552113371096229630932544, -1945311158424952045403133514249354981023947184768]]
def d56 : ℤ := 10437526650504331941257371728713880870303936148910592
theorem checked56 : checker a56 b56 21 d56 = true := by decide
theorem product56 (i j : ℕ) (hi : i < 21) (hj : j < 21) :
    dot a56 b56 21 i j = if i = j then d56 else 0 :=
  checker_sound _ _ _ _ checked56 i j hi hj
/-- Multidegree [2, 3, 0]; 3 by 3. Matrix entries still require linkage to generator evaluation. -/
def a57 : Data := [[-144, 70, -64], [240, 12, 56], [-792, -460, -544]]
def b57 : Data := [[1202, 4220, 293], [5388, 1728, -456], [-6306, -7605, -1158]]
def d57 : ℤ := 607656
theorem checked57 : checker a57 b57 3 d57 = true := by decide
theorem product57 (i j : ℕ) (hi : i < 3) (hj : j < 3) :
    dot a57 b57 3 i j = if i = j then d57 else 0 :=
  checker_sound _ _ _ _ checked57 i j hi hj
/-- Multidegree [2, 3, 1]; 13 by 13. Matrix entries still require linkage to generator evaluation. -/
def a58 : Data := [[1120, 336, 728, 1176, 640, -2360, -392, -510, -324, -130, 24, 184, -1012], [96, 28, -2, 2, 294, -343, 343, -270, -180, 30, -40, 56, 131], [4840, 3060, 4040, 1480, 3179, 425, -187, 1067, 216, 414, 832, 832, 361], [-8, -8, 228, 8, -32, -12, -68, 84, -27, -21, -261, 135, -45], [0, 0, 0, 0, -150, 480, 20, 258, 432, 140, 192, -168, -52], [-64, -60, 148, -68, 16, 286, -66, 352, 396, 64, -270, 558, 340], [0, 0, 0, 0, -150, 180, 120, -174, 0, -4, -24, -360, -408], [0, 0, 0, 0, 320, -832, -144, -635, 9, 20, 72, 396, -48], [160, 192, 176, 336, -36, 42, -150, 52, -66, 0, -238, 98, 602], [0, 320, -832, 704, 600, -1700, -1260, -1176, 864, 128, 616, 168, -484], [-32, -32, -24, 56, -4, -14, -28, -4, -36, 9, 0, 0, -29], [120, 24, -600, 96, 5, 65, -11, -35, -21, -9, 140, -80, 95], [1980, 176, 1628, -396, 80, 768, 384, 760, 294, -102, 96, -96, -840]]
def b58 : Data := [[-36756959333530577114668464, 133903523402651804657847904, -16998815637411923888203296, 565622120760284519734199424, 243098606085154642196588432, -249913573087589432498181120, -224400610290629258309646112, 154211279457914075224153440, 123141379024543717855456512, 12639945522065766766751840, 225691767642224753093610048, 336458545713240068456424640, 122765808180451204252424816], [134057040121343219401112340, -592101821890997380161304048, 67260378204045979371562320, 677270055115666802791603296, 467202215622139853304527944, -199000373365302705295934640, 201383042954803899465738412, 495479143854775655215956024, -167683135576259413104029832, -263915641305410224891889714, -3481051532868914507929400208, 499747495761814796749763480, -288229419619912510038281264], [-2939480218402934041744986, -39196242289768683270807800, -783187687951885240586808, -467575554020383641238081152, -133175669225911436950385104, 77326080300529030936573920, 77092918984412890077661958, -34853719409139860003554428, 100933178731568530395761940, 12356179271213718170040845, 412043960795976088850193768, -418130279160045591399827132, 29932162560006431355096824], [114329008757143302929104410, -126369556793697982283238312, 6919516015466328032023416, -1349576338509667584239198880, -440590357654321249377570768, 616756721233972337535114624, 591371517712763598510415770, -201689404981133126679750276, 155137960423485272113241916, -14718748506113279453366061, 1320677688014875274930998776, -260581062091146227929726596, -36374904353590767230719800], [-149937481536961435573794132, 639640982834707446726718608, 7520072070258079587095376, -505373187758789881467517920, -764047784407282384251183120, 302572436228416683341732928, -16142367327004866113531556, -804181438328819869569264504, -151387303163453184168099624, 325619087967504263444579442, 1871478998672651569099028208, -506045654688041592996125496, 116304909894952771351047216], [-65633883474505884752276748, -121367369940211425474982320, 20307027879630110714098656, -666225840484349509311791520, -411740672989852339851006312, 332478646683132900498867696, 428880467929479617827046340, -57074056915954447421260296, 42301323992313708643592328, 20443450757028010269806922, 1196667442754796430747709328, -111973673616282349256874120, 24134351462363654434909488], [143255943900138752507013336, -14341538684821610105404032, 4187204931508552450783056, -790353234198610735929090240, -40236733514916646058633304, 397540582674813645882999600, 423145864483099991239604664, 53890003851138760872335760, -47684662055184058511195760, -150665491477675145743179792, -964591407461480464364845536, -15540194056103777583279408, -91711477640666771130473280], [54997892373558305520567204, 76239439037333158788645744, -136235049526600345652592, 555906338179532196116795232, 245783384545732106299331520, -184380574948309116814962720, -481867071079193070211738860, -234328834829682259964625576, -204450065334949380450064632, -6825714388224320282493522, -585399952765079046703248816, 102859929835123820485233816, -37360774582132097344308912], [28407420284414599002811404, 166508318607118680343386704, -23308259436687111259286928, -778507368615408471356832480, -287283720663368903742520448, 458994625720083293763468000, 287957102382103716916241020, -361013730651263958992758776, 60469076924367603770323416, 146280301172924620553229994, -598371220654904191743834768, -331060604364524375484734584, 50031719505448036185836272], [-135200397185374834609834860, 459646342430379270896871216, 17945678171875451093048592, 4333798480774540614682874976, 2590820555619662881296049440, -1794922309491323698988456544, -1372647884283652734845303004, 1210241733445392148175648184, -95330651073164984727447192, -239077070864390762010300906, 435200902962058288231227792, 1205374777066094404678483320, -88499478040535977844881392], [73853767107706278486548664, -455069968539645982591815552, 16235367215036255413644816, -1202008890758808618298762560, -108117333602595213258222432, 171093775933160959692114288, 85798007217596080471004928, 209852325686194779740153040, -31426179201418578716709648, -121736047985807930271205128, 132445339625041131444264288, -177308439009770732029559856, -43298634720478729626171072], [109646224918686861892200252, -574411152895338122907502992, 31920230618470034661857952, -394405314825553172852378592, 20553454691694013573851984, 344155291232795051770722000, 314996147905833874494830148, 563338535366765608239140136, -96305325156679282892165544, -245997402957596923165267050, -311686723286680237030321488, 291218428021032058025240616, -117573159488235487191051504], [-54918447530441324523303204, 203657323206943564482695376, -21811987378196621734945008, -201435860975793954128708064, -54579853712879065814208144, -65135012984195939837787072, -226811122627174739443257204, -135013216312091465280560664, 235244984500796073596371896, 74465224919659956583080618, 68810395590851435283445488, -170136261728848046397877080, 64003300981891968894769008]]
def d58 : ℤ := 196813977581808058174280375616
theorem checked58 : checker a58 b58 13 d58 = true := by decide
theorem product58 (i j : ℕ) (hi : i < 13) (hj : j < 13) :
    dot a58 b58 13 i j = if i = j then d58 else 0 :=
  checker_sound _ _ _ _ checked58 i j hi hj
/-- Multidegree [2, 4, 0]; 5 by 5. Matrix entries still require linkage to generator evaluation. -/
def a59 : Data := [[1568, 896, -714, -90, 64], [32, 98, -90, 180, 64], [8800, 5780, 1940, 828, 1024], [8, 32, -84, 9, 81], [0, 0, 0, 252, 144]]
def b59 : Data := [[410073324, -2155541442, -18184707, -1596094704, 1802880351], [-499791696, 3620760720, 73998432, 2077854336, -3082101480], [-318498000, -487483104, 58697136, -191309184, 48423384], [105770880, 1051364160, -20399904, -2496654720, 1035152024], [-185099040, -1839887280, 35699832, 4369145760, 974758032]]
def d59 : ℤ := 401223466656
theorem checked59 : checker a59 b59 5 d59 = true := by decide
theorem product59 (i j : ℕ) (hi : i < 5) (hj : j < 5) :
    dot a59 b59 5 i j = if i = j then d59 else 0 :=
  checker_sound _ _ _ _ checked59 i j hi hj
/-- Multidegree [3, 0, 0]; 1 by 1. Matrix entries still require linkage to generator evaluation. -/
def a60 : Data := [[15]]
def b60 : Data := [[1]]
def d60 : ℤ := 15
theorem checked60 : checker a60 b60 1 d60 = true := by decide
theorem product60 (i j : ℕ) (hi : i < 1) (hj : j < 1) :
    dot a60 b60 1 i j = if i = j then d60 else 0 :=
  checker_sound _ _ _ _ checked60 i j hi hj
/-- Multidegree [3, 0, 1]; 1 by 1. Matrix entries still require linkage to generator evaluation. -/
def a61 : Data := [[24]]
def b61 : Data := [[1]]
def d61 : ℤ := 24
theorem checked61 : checker a61 b61 1 d61 = true := by decide
theorem product61 (i j : ℕ) (hi : i < 1) (hj : j < 1) :
    dot a61 b61 1 i j = if i = j then d61 else 0 :=
  checker_sound _ _ _ _ checked61 i j hi hj
/-- Multidegree [3, 0, 2]; 3 by 3. Matrix entries still require linkage to generator evaluation. -/
def a62 : Data := [[0, -120, 54], [-56, 0, -12], [-286, 48, 54]]
def b62 : Data := [[-48, -756, -120], [-538, -1287, 252], [224, -2860, 560]]
def d62 : ℤ := 76656
theorem checked62 : checker a62 b62 3 d62 = true := by decide
theorem product62 (i j : ℕ) (hi : i < 3) (hj : j < 3) :
    dot a62 b62 3 i j = if i = j then d62 else 0 :=
  checker_sound _ _ _ _ checked62 i j hi hj
/-- Multidegree [3, 0, 3]; 6 by 6. Matrix entries still require linkage to generator evaluation. -/
def a63 : Data := [[-192, 27, -75, -180, 0, 264], [32, 8, 66, 0, 42, -14], [-396, -729, -477, 0, 78, 630], [-4, -1, 90, -288, -207, 312], [320, -512, 136, 0, 132, 8], [480, 3375, -2085, -216, 352, 198]]
def b63 : Data := [[-79033389732, 74152323288, 10363581238, 44681057712, 23586394923, 6286414494], [-39571012656, 173233261656, 8832831032, 22073399928, -35176353822, 3544643976], [-53275228128, 313662165264, 13115110040, 36077411736, -41089648770, -3707192208], [-249523242354, 501325764678, 80906881384, 71186884920, -102880619145, 2697466026], [101994054336, 140693666040, -8346811680, -65265715008, 32943203010, 2025908064], [-148432239072, 467133515316, 65523458568, 89023585032, -61067748960, 4995419184]]
def d63 : ℤ := 23829708105144
theorem checked63 : checker a63 b63 6 d63 = true := by decide
theorem product63 (i j : ℕ) (hi : i < 6) (hj : j < 6) :
    dot a63 b63 6 i j = if i = j then d63 else 0 :=
  checker_sound _ _ _ _ checked63 i j hi hj
/-- Multidegree [3, 1, 0]; 1 by 1. Matrix entries still require linkage to generator evaluation. -/
def a64 : Data := [[64]]
def b64 : Data := [[1]]
def d64 : ℤ := 64
theorem checked64 : checker a64 b64 1 d64 = true := by decide
theorem product64 (i j : ℕ) (hi : i < 1) (hj : j < 1) :
    dot a64 b64 1 i j = if i = j then d64 else 0 :=
  checker_sound _ _ _ _ checked64 i j hi hj
/-- Multidegree [3, 1, 1]; 6 by 6. Matrix entries still require linkage to generator evaluation. -/
def a65 : Data := [[-24, -184, 144, 15, 150, 101], [-40, 56, -42, 12, 0, -98], [572, 572, 102, 207, 264, 33], [-58, 30, -36, -3, -12, -9], [64, -56, -60, -56, -126, 40], [-120, 248, 44, -120, 48, -140]]
def b65 : Data := [[1759968456, 3512955462, 612043116, -1116416988, 3493332360, 24754635], [-2029738512, -3684856566, 53663796, 533907156, -2174956128, 471998925], [-6646669992, -10298195256, -1416963960, -15200049696, -9279476424, 405507468], [-5682608952, -5884743360, -796503576, -6393291360, -8676847704, -2236125420], [7573898128, 9523700104, 1408025824, 11336244592, 7501487160, 543851700], [274538136, -4465806192, 290590728, 6492225216, 245765304, -187990452]]
def d65 : ℤ := 452686101072
theorem checked65 : checker a65 b65 6 d65 = true := by decide
theorem product65 (i j : ℕ) (hi : i < 6) (hj : j < 6) :
    dot a65 b65 6 i j = if i = j then d65 else 0 :=
  checker_sound _ _ _ _ checked65 i j hi hj
/-- Multidegree [3, 1, 2]; 13 by 13. Matrix entries still require linkage to generator evaluation. -/
def a66 : Data := [[-512, 240, -208, 464, 72, -200, 156, 252, -360, 0, -54, -414, -994], [112, 96, 680, 56, 28, 231, -2, 2, 0, -42, 30, -42, 141], [-748, -2178, 3784, 968, -1377, -901, -1818, -666, -72, 299, -156, -156, -85], [16, 4, 30, -78, 4, -360, -114, -4, 108, 69, 261, -135, 436], [200, 192, 40, -8, -320, 85, 304, 224, 84, 77, 192, -168, -172], [64, 480, 416, -224, 450, -278, -1110, 510, 96, -128, -330, 682, 104], [1440, 108, 2016, 288, 5, 100, 50, 10, 63, 26, -32, -480, -136], [-768, -330, -1200, 12, -968, 56, 1804, -22, -48, 0, -8, -44, -142], [-240, -80, 520, -280, -96, 36, -88, -168, 648, 88, 748, -308, -672], [0, 0, 0, 0, -160, 400, 416, -352, 0, -32, -528, -144, -32], [-24, -64, -22, 74, -64, 22, -48, 112, 0, 14, -24, 40, -22], [16, 20, -14, -6, 4, -9, -100, 16, -54, -4, -14, 8, 67], [576, 180, 900, 180, 16, 284, 148, -36, 72, 0, 84, -84, -156]]
def b66 : Data := [[-35182134492963337227116672, -281507423391322369071862016, -20443829328984118676855808, -1390493708764633736919296, -154735910809856612295551232, 4549300711687930001175040, 91438439894267725990387712, 58473024503053216061311232, 55163678796420459469595904, -5368185793557722362100128, 234949044166393790934032384, 952639714692208899905303552, 157170792044518710304748928], [80464738321637018853627648, -137664554784622363332660736, -2987594500724461908113408, 248219284663887141019975680, 37960461156681756147802112, 98825603051666551579946496, -135209887425053184558950400, 35483185745148051729840128, 19229131230325753764948480, 148916741872917262979696736, -175919327767332393024676864, 809382413009548029014689792, 426891232037861945403152896], [-15384720344677697907892972, 232903492712904074005398536, 28523689673544069198676896, -107249926102375407353257320, 217908840963033166919523576, -3096166212744263746149216, -8881641336476037142953952, -62937941555516990005424376, -91639898143062919153773388, -70871778382986998248069711, -496955406402233478686284464, -1115757711486244130451324832, -183870174264205938680211876], [140500990939517028764128348, -411905855229968052723272360, -39248290428174872488594464, 530586066298691095285597576, -693585380718916873222732888, 60049255622288207292009696, -74065867044489074654890656, 186863341548393146539196504, 170742034006770391093257020, 204036429970428406559431323, 1503583906753173993236192368, 2175865501541093128512651296, 881098849621468735335161972], [-23193973103737699635105040, 329147671282275007970734176, 6037658552493351650175872, -177247859219140825555317472, 261340354421476604878985632, -108256247012417584173429376, -23955778652820048957402752, -224358021740255630224431520, -206667495600898118216422032, -160026531532677867092336084, -534645623693072080766094400, -2860704311311819716128119680, -418747316860717768780135600], [-51672177548284565481023312, 238834274317994509605293536, -5940599814379550742761088, -177478634157411009534999136, 156123177007159464247118880, -94198503298301101330304128, -67220885115392680715094144, -100138520213610598423335968, -18325982554256979173526736, 11249508263048260595602524, 188048489902752230590503616, -265536613634157998192695680, -96788594667381259765909872], [-24805011852254124658486168, 184985147056790544820272784, 11846773787809927431950656, -97237584033925572269970768, 212313014676574857752608112, -34148908757145606584486592, -5049363681701551608874432, -44667422192691367892898160, -143542941998781891939719512, -103669730841452485655412910, -514877002871260425985432672, -1717832666512052658127495488, -190336658337690049796564360], [-14149134656160057136108168, 358921241842693009573924400, -13691331825517432913332800, -145963836272000512824550000, 232241679382663374012457936, -12045631928170204980780096, 111595899739022727319345344, -60314143430466237632473040, -68971718165830183520982728, -123230488607846221012491738, 310288571242204635916638176, -1174014262314127363974249920, -518000108542276861848461528], [41185778945654847567629456, -309107577701903514619528544, -56088955695729506795642752, 480776511534085127330924512, -563593590434790235016208544, 135495071267562824242293376, 47292542654036470735782528, 164539153792817605365911712, 277750010957034520364196880, 300281773082667273834098548, 1453754714534956562565562944, 1265145139662458603275399040, 433471944858803431460730160], [-247690274211913287993921264, 728470091833156105242464160, 227837308007486702175898752, -729179695521630042004043040, 2725582928118647440698121824, -414002560327093462409733504, -601409322301603542350020992, -1085168278572693437550288480, -1120567034053689970784286576, -375104647572582316222888620, -3468590606707071817722311616, -11370947247188899722608616576, -1185007346414956319430947664], [-3115415081889360517562208, -37252212401523411296852928, -12734951241389788111639296, 17391365636920096252385472, -166844873562375535401092160, -41335699315161100292616960, -37952897902742778397591296, 74087577539188758073564224, 94440684735541804174800288, -154581215230232876366889528, 52644343195880586206398080, 1102096395009943665437058816, 254574180798710137931594976], [-84456172771801633664310608, -97460610177414020116419104, 43078359424687115593101696, -165253645811522822660549216, 211878035498476542042909728, 34857120036396376434940800, -170885023650580719112179840, -44389677137937629698411552, -161356098350246444571692752, -155857982837072501972261220, -616401523231959942741166400, -1215085560259046439302217088, 235832755379778261391845008], [-17609626160216474377301104, 121127482622553579242371232, -11396311055637542376181632, 195133544343340865961682400, -75845016014309230432268960, -8449359936228553290719616, -17064051545205813664742784, 15314491558084765159316128, -14708471590395022599818480, 51987466528728221123328756, 291024719777988640970114624, 220887857621378271048333184, 30789750563634797100872752]]
def d66 : ℤ := 144756753273870128785669306368
theorem checked66 : checker a66 b66 13 d66 = true := by decide
theorem product66 (i j : ℕ) (hi : i < 13) (hj : j < 13) :
    dot a66 b66 13 i j = if i = j then d66 else 0 :=
  checker_sound _ _ _ _ checked66 i j hi hj
/-- Multidegree [3, 2, 0]; 3 by 3. Matrix entries still require linkage to generator evaluation. -/
def a67 : Data := [[-64, 210, 40], [64, 0, 42], [704, 480, 391]]
def b67 : Data := [[-10080, -31455, 4410], [2272, -26592, 2624], [15360, 89280, -6720]]
def d67 : ℤ := 1736640
theorem checked67 : checker a67 b67 3 d67 = true := by decide
theorem product67 (i j : ℕ) (hi : i < 3) (hj : j < 3) :
    dot a67 b67 3 i j = if i = j then d67 else 0 :=
  checker_sound _ _ _ _ checked67 i j hi hj
/-- Multidegree [3, 2, 1]; 13 by 13. Matrix entries still require linkage to generator evaluation. -/
def a68 : Data := [[336, 640, -2360, -392, 192, 416, 672, -153, -390, -15, -115, -144, -46], [32, 336, -392, 392, 98, -7, 7, -90, 0, -30, 42, -48, -147], [-3960, -4114, -550, 242, -2601, -3434, -1258, -873, -432, -598, -598, -192, 614], [-4, -16, -6, -34, -16, 456, 16, 42, -42, -87, 45, -81, -192], [0, 120, -384, -16, -200, 190, 140, 344, 420, 112, -98, 144, -282], [-240, 64, 1144, -264, 60, -148, 68, 1320, -96, 120, -248, 396, -140], [0, -540, 648, 432, -25, -250, -50, -29, 42, 4, 60, 192, 358], [0, -240, 624, 108, -704, 1312, -16, 1397, -60, -32, -176, -9, -2], [-640, 120, -140, 500, 144, 132, 252, -208, 0, 748, -308, -154, 838], [0, 0, 0, 0, -400, 1040, -880, 784, 0, -176, -48, -672, 608], [64, 8, 28, 56, 8, 6, -14, 8, 0, -6, 10, 0, -10], [48, 10, 130, -22, 2, -50, 8, -14, -54, -14, 8, -10, 74], [792, 360, 3456, 1728, 32, 296, -72, 304, 408, -72, 72, 56, -408]]
def b68 : Data := [[130965180365163908195041168, -632115663372262809912441216, -6603901380537958739561264, -590128500458457977841775216, -131641375879096194485390496, -96765801807725822564262928, -171301120149709874503137776, 63588956551103187694526512, -43909100065586301643427152, -14427200208465179558608570, 3857830200826952215394605792, -1038486666590521357678027328, 59729664867428593983102204], [-32481592816675084442839232, 351428058384097181969683536, -96862873122740399425071200, -2585219331803273729072525440, -1099570709164190387498043504, -379617780365175708960011308, -383044052707823877691478576, 647000023579365186843719440, -275627605648091926974120832, -111188398890873008020327000, -9329248399429144250757467024, -4452287515562398549048782320, 188159123526371213256529608], [-35303273563505645377767984, -116934373453913298984540384, -4151000461009038233174952, -30571075182487306420195248, -79963829188468225624217736, -9616111682137396669439040, -74761336828059870954504408, 17519666181408604648013808, -959870890529195559391416, -19917881267392375220162451, -1049287354212886920447045144, 159910024999626556048462728, 70202119996879305107311296], [62752051218084234694875200, 350737813743076660271575008, 21018231163315494542701784, 131317123818265431287335360, 15074985703524991749301848, 30830745857290696011248440, 190057406677122230944574408, -5545483459259459276676448, 50362596142465607301453832, 10178985753951292186578769, 1017984643505890789584644216, -178133263387539691329631192, 43535334151641811229943288], [273308069958971735479165504, -287179786151061018091688352, 11016575635716216102728752, 1465738027435893216850625504, 295120626313790000067708720, 485964720267285287046361952, 538215968400436680173586928, -711429401867426649340554464, 99736174115217151698274640, 278983384589948807549388542, 1756980676958330800941480352, -157020805081599413846570096, 53535041533169551356750048], [148113607668537241586932960, -450051997757913991594476912, -102235175300578834770732608, -2319157285934706208139172592, -1455326768502824159033121984, -426959776361388139085165584, -90691407413932704198390992, 678162212096980975508927392, -262971908971764319742116552, -90247904456769937802611621, -8550576120601020844598286512, -7876274118060728762174903264, 258880340573625909919756728], [13637441848258749298016096, 677644024337337098168227056, 149293759209265066630343120, 5128654157071421075267482864, 2794366151620740013798331664, 672280292135875063777908904, 682263611251463988216827456, -1160560253009110011837224512, 516433080126231264826671160, 130143225256879207652991349, 9822017246222136302621290544, 14649540749778331979287725008, -321302404667945722633956696], [-201680429946613071240897760, 779127482296344690313975488, 107821202600632079793510320, 3855027109379086908348250432, 2110378125786920339653690224, 718316639693600309054210344, 427384972697660944998272624, -886499429174594688921129952, 393210280257713852931955024, 214960966234843205321390710, 11456480972676686230607373056, 10789193824172703525602492432, -431592041863129296055229184], [74041700617274297799060208, -44286897373172534422088400, 26142862779084344184633808, 1446319601573049113629773104, 1362049812827110426609815312, 188633282298360484200577532, 533408066787209338989763456, -661117845266232572093732096, 60301873880327859529997120, 308781325125785798424507908, -363920598371504355125676944, 3385873270375455177849248080, 38490369536331228491550192], [-816118849339950421823589408, 391825938082255360136934192, 63534640013066442747737760, 2948666015726024217031904592, 1532698846710892445499415056, 259463628554845280389194432, -626502229560185790800685648, -335717082987696212705340384, 761279715885269298668760120, -288812310907842584423318175, 18575813317055466584368852944, 9155308112286474647227025472, -699175771196120007156032040], [-1526318984903089782355700672, 3222577664397038769721282032, 163007342322971044282994896, 9944475835504652712779130128, 5200322330337342774030562656, 973782540373190930691855104, 821940940245212866632043360, -1668187101438277620337097792, 1016710705270950550401472568, -32639849681535266986633675, 27111550149821532320366688208, 31225251454785958039060162000, -1584016345640925513009037176], [276560791824947354961476448, -805455308781951917808034944, -320743833576758822666405904, -9370593004891063864600325568, -4797778557325898583213864912, -1304593383616587233830481016, -376536873795704158862677200, 2372948227557394893551588736, -1090396265438607593572688592, -557184591803835045788964402, -27047888236238032361870015712, -24908822434630230593303762736, 683023349592305934997295232], [155184383651492350191547264, 34625138151959981524977216, -64071561279002371880585360, -1334942841445219031751741856, -441846824124893968886158032, -193107115368808377992105368, 412966453808307790871089072, 229151463718309310339225440, -148666843355548806473594272, 119401211715864070605255566, -7152299035285214040593365280, -1755259401439668931067712176, 111356048905174422450423984]]
def d68 : ℤ := 347973846750959605274908304352
theorem checked68 : checker a68 b68 13 d68 = true := by decide
theorem product68 (i j : ℕ) (hi : i < 13) (hj : j < 13) :
    dot a68 b68 13 i j = if i = j then d68 else 0 :=
  checker_sound _ _ _ _ checked68 i j hi hj
/-- Multidegree [3, 3, 0]; 6 by 6. Matrix entries still require linkage to generator evaluation. -/
def a69 : Data := [[896, 512, -408, -270, -40, -204], [112, 343, -315, 0, 48, 180], [-7480, -4913, -1649, -864, -736, -218], [16, 64, -168, 18, 27, -31], [0, -125, 215, 756, 84, 30], [-32, 8, 176, 216, -144, -8]]
def b69 : Data := [[311030731740, 130867620540, 20395774788, -1150776963504, 227524954584, -230067746925], [-371497165140, -131994090996, -44779009164, 1571208840720, -332348409480, 388797870039], [-205187981556, -189724579476, -27266905068, 277743647376, -140545506504, 103211371599], [22891952120, 35126059448, 3139344712, 149264438176, 149888411440, 104726260086], [-319566105180, -250364635452, -37578542148, 1021057450416, -30070201176, -529614216819], [240516914148, 625561721604, 34942046076, -2064217339728, 253801359144, -275872318371]]
def d69 : ℤ := 129730050210816
theorem checked69 : checker a69 b69 6 d69 = true := by decide
theorem product69 (i j : ℕ) (hi : i < 6) (hj : j < 6) :
    dot a69 b69 6 i j = if i = j then d69 else 0 :=
  checker_sound _ _ _ _ checked69 i j hi hj
/-- Multidegree [4, 0, 0]; 1 by 1. Matrix entries still require linkage to generator evaluation. -/
def a70 : Data := [[64]]
def b70 : Data := [[1]]
def d70 : ℤ := 64
theorem checked70 : checker a70 b70 1 d70 = true := by decide
theorem product70 (i j : ℕ) (hi : i < 1) (hj : j < 1) :
    dot a70 b70 1 i j = if i = j then d70 else 0 :=
  checker_sound _ _ _ _ checked70 i j hi hj
/-- Multidegree [4, 0, 1]; 2 by 2. Matrix entries still require linkage to generator evaluation. -/
def a71 : Data := [[144, 45], [-48, 0]]
def b71 : Data := [[0, -15], [16, 48]]
def d71 : ℤ := 720
theorem checked71 : checker a71 b71 2 d71 = true := by decide
theorem product71 (i j : ℕ) (hi : i < 2) (hj : j < 2) :
    dot a71 b71 2 i j = if i = j then d71 else 0 :=
  checker_sound _ _ _ _ checked71 i j hi hj
/-- Multidegree [4, 0, 2]; 5 by 5. Matrix entries still require linkage to generator evaluation. -/
def a72 : Data := [[-512, 72, -200, 0, 324], [128, 32, 264, 0, 36], [968, 1782, 1166, -312, 36], [8, 2, -180, 138, 81], [-160, 256, -68, 231, 144]]
def b72 : Data := [[-16595964, 59054037, 20510268, 293741388, -147779688], [-4721976, -143122560, 27919776, -49145760, 67069632], [-12915000, 190136100, -15589968, -185625072, 89836320], [-108504480, 104321616, -31662144, -21461952, 238042560], [157915184, 242492936, 16583456, 360521824, -192978240]]
def d72 : ℤ := 61904670912
theorem checked72 : checker a72 b72 5 d72 = true := by decide
theorem product72 (i j : ℕ) (hi : i < 5) (hj : j < 5) :
    dot a72 b72 5 i j = if i = j then d72 else 0 :=
  checker_sound _ _ _ _ checked72 i j hi hj
/-- Multidegree [4, 1, 0]; 2 by 2. Matrix entries still require linkage to generator evaluation. -/
def a73 : Data := [[40, 120], [48, 0]]
def b73 : Data := [[0, 15], [6, -5]]
def d73 : ℤ := 720
theorem checked73 : checker a73 b73 2 d73 = true := by decide
theorem product73 (i j : ℕ) (hi : i < 2) (hj : j < 2) :
    dot a73 b73 2 i j = if i = j then d73 else 0 :=
  checker_sound _ _ _ _ checked73 i j hi hj
/-- Multidegree [4, 1, 1]; 7 by 7. Matrix entries still require linkage to generator evaluation. -/
def a74 : Data := [[640, 192, 416, 672, -45, -345, 90], [384, 112, -8, 8, 0, 0, -36], [5324, 3366, 4444, 1628, 624, 624, 138], [-8, -8, 228, 8, -174, 90, -27], [-96, 160, -152, -112, 336, -294, 84], [256, 240, -592, 272, -180, 372, -176], [-1944, -90, -900, -180, -42, -630, -32]]
def b74 : Data := [[1310180160936, 5027761121252, -639533575192, 8033316822448, 5830457283768, 1103638986010, -2272513223896], [1733961381504, -6880382278616, -872265740192, 43056437979104, 28718297433408, 9355044011720, -3540530402288], [-2726969796756, 4224390242378, 1570712413040, -26215672842512, -20332043923788, -7502331361151, 4362336852440], [1202637737220, -4634074348638, 1276059972912, -33227486431008, -20432384693124, -2773872760197, 3755742949128], [-7455817683152, 7062615516920, 3542220658880, -86317106336448, -48377858146976, -14060915961092, 9534115522592], [-1269653835184, -16395291118152, -258920181184, 10682285134208, 8319049442752, 5575945508188, -4086165774688], [20243047688880, -65317109290584, -9600885424896, 218083894576992, 151515060648720, 41927499131892, -35389923173856]]
def d74 : ℤ := 3440605673088672
theorem checked74 : checker a74 b74 7 d74 = true := by decide
theorem product74 (i j : ℕ) (hi : i < 7) (hj : j < 7) :
    dot a74 b74 7 i j = if i = j then d74 else 0 :=
  checker_sound _ _ _ _ checked74 i j hi hj
/-- Multidegree [4, 2, 0]; 5 by 5. Matrix entries still require linkage to generator evaluation. -/
def a75 : Data := [[896, 512, -408, -120, 25], [128, 392, -360, 0, 36], [9680, 6358, 2134, 768, 529], [8, 32, -84, 54, 9], [0, 100, -172, 252, 49]]
def b75 : Data := [[2768133, -3617376, -17898, -2151810, 1833807], [-5705148, 5045595, 424428, 44689176, -13586484], [-1876116, 183513, 179916, -10509576, 810348], [-5534220, -3918478, 490800, 88660288, -15880716], [33519312, 10499208, -2758752, -584060352, 149524992]]
def d75 : ℤ := 1826755920
theorem checked75 : checker a75 b75 5 d75 = true := by decide
theorem product75 (i j : ℕ) (hi : i < 5) (hj : j < 5) :
    dot a75 b75 5 i j = if i = j then d75 else 0 :=
  checker_sound _ _ _ _ checked75 i j hi hj
/-- Multidegree [5, 0, 0]; 1 by 1. Matrix entries still require linkage to generator evaluation. -/
def a76 : Data := [[120]]
def b76 : Data := [[1]]
def d76 : ℤ := 120
theorem checked76 : checker a76 b76 1 d76 = true := by decide
theorem product76 (i j : ℕ) (hi : i < 1) (hj : j < 1) :
    dot a76 b76 1 i j = if i = j then d76 else 0 :=
  checker_sound _ _ _ _ checked76 i j hi hj
/-- Multidegree [5, 0, 1]; 2 by 2. Matrix entries still require linkage to generator evaluation. -/
def a77 : Data := [[192, 270], [128, 0]]
def b77 : Data := [[0, 135], [64, -96]]
def d77 : ℤ := 17280
theorem checked77 : checker a77 b77 2 d77 = true := by decide
theorem product77 (i j : ℕ) (hi : i < 2) (hj : j < 2) :
    dot a77 b77 2 i j = if i = j then d77 else 0 :=
  checker_sound _ _ _ _ checked77 i j hi hj
/-- Multidegree [5, 1, 0]; 2 by 2. Matrix entries still require linkage to generator evaluation. -/
def a78 : Data := [[512, 75], [448, 0]]
def b78 : Data := [[0, 75], [448, -512]]
def d78 : ℤ := 33600
theorem checked78 : checker a78 b78 2 d78 = true := by decide
theorem product78 (i j : ℕ) (hi : i < 2) (hj : j < 2) :
    dot a78 b78 2 i j = if i = j then d78 else 0 :=
  checker_sound _ _ _ _ checked78 i j hi hj
/-- Multidegree [6, 0, 0]; 2 by 2. Matrix entries still require linkage to generator evaluation. -/
def a79 : Data := [[512, 225], [512, 0]]
def b79 : Data := [[0, 225], [512, -512]]
def d79 : ℤ := 115200
theorem checked79 : checker a79 b79 2 d79 = true := by decide
theorem product79 (i j : ℕ) (hi : i < 2) (hj : j < 2) :
    dot a79 b79 2 i j = if i = j then d79 else 0 :=
  checker_sound _ _ _ _ checked79 i j hi hj

#print axioms checker_sound
#print axioms product79
end TraceInverse
