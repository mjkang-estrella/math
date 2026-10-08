import Research.WordQueryData

/-! Fixed W018 symbolic instruction graphs, admitted typed constructors and
actual unary codec lengths. Sizes alone instantiate literals; evidence is
proof-only. This file establishes no guest execution, query correctness, fuel
sufficiency, runtime comparison or BSGS cost. -/
namespace Research.WordQueryCode

open WordCore WordCodec WordQueryData

inductive Literal where
  | fixed (value : Nat)
  | W | L | B | A | A1 | A2
  deriving Repr, DecidableEq

instance (n : Nat) : OfNat Literal n := ⟨.fixed n⟩

def Literal.eval (s : Sizes) : Literal → Nat
  | .fixed n => n
  | .W => s.W
  | .L => s.L
  | .B => s.B
  | .A => s.A
  | .A1 => s.A + 1
  | .A2 => s.A + 2

inductive TemplateInstr where
  | const (d : Fin 32) (v t : Literal)
  | mov (d a : Fin 32) (t : Literal)
  | add (d a b : Fin 32) (t : Literal)
  | sub (d a b : Fin 32) (t : Literal)
  | mul (d a b : Fin 32) (t : Literal)
  | divmod (dq dr a b : Fin 32) (t : Literal)
  | eq (d a b : Fin 32) (t : Literal)
  | lt (d a b : Fin 32) (t : Literal)
  | load (d a : Fin 32) (t : Literal)
  | store (a b : Fin 32) (t : Literal)
  | jump (t : Literal)
  | branch (a : Fin 32) (t0 t1 : Literal)
  | halt
  deriving Repr, DecidableEq

def TemplateInstr.words : TemplateInstr → List Literal
  | .const _ v t => [v, t]
  | .branch _ t0 t1 => [t0, t1]
  | .mov _ _ t | .add _ _ _ t | .sub _ _ _ t | .mul _ _ _ t
  | .divmod _ _ _ _ t | .eq _ _ _ t | .lt _ _ _ t | .load _ _ t
  | .store _ _ t | .jump t => [t]
  | .halt => []

def TemplateInstr.Fits (s : Sizes) (i : TemplateInstr) : Prop :=
  ∀ l ∈ i.words, l.eval s < s.U

instance (s : Sizes) (i : TemplateInstr) : Decidable (i.Fits s) :=
  inferInstanceAs (Decidable (∀ l ∈ i.words, l.eval s < s.U))

/-- Every guest word is constructed from its actual literal and bound proof.
There is no failed-admission fallback, reduction modulo the bound or dummy code. -/
def instantiateInstr (s : Sizes) (hn : NumericallyAdmissible s)
    (i : TemplateInstr) (h : i.Fits s) : Instr (profile s hn) :=
  match i with
  | .const d v t => .const d ⟨v.eval s, h v (by simp [TemplateInstr.words])⟩
      ⟨t.eval s, h t (by simp [TemplateInstr.words])⟩
  | .mov d a t => .mov d a ⟨t.eval s, h t (by simp [TemplateInstr.words])⟩
  | .add d a b t => .add d a b ⟨t.eval s, h t (by simp [TemplateInstr.words])⟩
  | .sub d a b t => .sub d a b ⟨t.eval s, h t (by simp [TemplateInstr.words])⟩
  | .mul d a b t => .mul d a b ⟨t.eval s, h t (by simp [TemplateInstr.words])⟩
  | .divmod dq dr a b t => .divmod dq dr a b ⟨t.eval s, h t (by simp [TemplateInstr.words])⟩
  | .eq d a b t => .eq d a b ⟨t.eval s, h t (by simp [TemplateInstr.words])⟩
  | .lt d a b t => .lt d a b ⟨t.eval s, h t (by simp [TemplateInstr.words])⟩
  | .load d a t => .load d a ⟨t.eval s, h t (by simp [TemplateInstr.words])⟩
  | .store a b t => .store a b ⟨t.eval s, h t (by simp [TemplateInstr.words])⟩
  | .jump t => .jump ⟨t.eval s, h t (by simp [TemplateInstr.words])⟩
  | .branch a t0 t1 => .branch a ⟨t0.eval s, h t0 (by simp [TemplateInstr.words])⟩
      ⟨t1.eval s, h t1 (by simp [TemplateInstr.words])⟩
  | .halt => .halt

/-- Exact accepted W018 rows 0..85. -/
def commonSkeleton : Array TemplateInstr := #[
  .const ⟨1, by decide⟩ 1 1, -- 0
  .const ⟨2, by decide⟩ 2 2, -- 1
  .const ⟨3, by decide⟩ .W 3, -- 2
  .const ⟨12, by decide⟩ .B 4, -- 3
  .const ⟨13, by decide⟩ .A 5, -- 4
  .const ⟨26, by decide⟩ .L 6, -- 5
  .const ⟨6, by decide⟩ 0 7, -- 6
  .mov ⟨7, by decide⟩ ⟨3, by decide⟩ 8, -- 7
  .mov ⟨27, by decide⟩ ⟨6, by decide⟩ 9, -- 8
  .add ⟨11, by decide⟩ ⟨6, by decide⟩ ⟨7, by decide⟩ 10, -- 9
  .mov ⟨8, by decide⟩ ⟨11, by decide⟩ 11, -- 10
  .mov ⟨9, by decide⟩ ⟨0, by decide⟩ 12, -- 11
  .lt ⟨24, by decide⟩ ⟨27, by decide⟩ ⟨8, by decide⟩ 13, -- 12
  .branch ⟨24, by decide⟩ 18 14, -- 13
  .sub ⟨8, by decide⟩ ⟨8, by decide⟩ ⟨1, by decide⟩ 15, -- 14
  .load ⟨10, by decide⟩ ⟨8, by decide⟩ 16, -- 15
  .mul ⟨9, by decide⟩ ⟨9, by decide⟩ ⟨2, by decide⟩ 17, -- 16
  .add ⟨9, by decide⟩ ⟨9, by decide⟩ ⟨10, by decide⟩ 12, -- 17
  .mov ⟨6, by decide⟩ ⟨11, by decide⟩ 19, -- 18
  .mov ⟨4, by decide⟩ ⟨9, by decide⟩ 20, -- 19
  .mov ⟨7, by decide⟩ ⟨3, by decide⟩ 21, -- 20
  .mov ⟨27, by decide⟩ ⟨6, by decide⟩ 22, -- 21
  .add ⟨11, by decide⟩ ⟨6, by decide⟩ ⟨7, by decide⟩ 23, -- 22
  .mov ⟨8, by decide⟩ ⟨11, by decide⟩ 24, -- 23
  .mov ⟨9, by decide⟩ ⟨0, by decide⟩ 25, -- 24
  .lt ⟨24, by decide⟩ ⟨27, by decide⟩ ⟨8, by decide⟩ 26, -- 25
  .branch ⟨24, by decide⟩ 31 27, -- 26
  .sub ⟨8, by decide⟩ ⟨8, by decide⟩ ⟨1, by decide⟩ 28, -- 27
  .load ⟨10, by decide⟩ ⟨8, by decide⟩ 29, -- 28
  .mul ⟨9, by decide⟩ ⟨9, by decide⟩ ⟨2, by decide⟩ 30, -- 29
  .add ⟨9, by decide⟩ ⟨9, by decide⟩ ⟨10, by decide⟩ 25, -- 30
  .mov ⟨6, by decide⟩ ⟨11, by decide⟩ 32, -- 31
  .mov ⟨5, by decide⟩ ⟨9, by decide⟩ 33, -- 32
  .mov ⟨14, by decide⟩ ⟨0, by decide⟩ 34, -- 33
  .lt ⟨24, by decide⟩ ⟨14, by decide⟩ ⟨4, by decide⟩ 35, -- 34
  .branch ⟨24, by decide⟩ 68 36, -- 35
  .mov ⟨7, by decide⟩ ⟨5, by decide⟩ 37, -- 36
  .mov ⟨27, by decide⟩ ⟨6, by decide⟩ 38, -- 37
  .add ⟨11, by decide⟩ ⟨6, by decide⟩ ⟨7, by decide⟩ 39, -- 38
  .mov ⟨8, by decide⟩ ⟨11, by decide⟩ 40, -- 39
  .mov ⟨9, by decide⟩ ⟨0, by decide⟩ 41, -- 40
  .lt ⟨24, by decide⟩ ⟨27, by decide⟩ ⟨8, by decide⟩ 42, -- 41
  .branch ⟨24, by decide⟩ 47 43, -- 42
  .sub ⟨8, by decide⟩ ⟨8, by decide⟩ ⟨1, by decide⟩ 44, -- 43
  .load ⟨10, by decide⟩ ⟨8, by decide⟩ 45, -- 44
  .mul ⟨9, by decide⟩ ⟨9, by decide⟩ ⟨2, by decide⟩ 46, -- 45
  .add ⟨9, by decide⟩ ⟨9, by decide⟩ ⟨10, by decide⟩ 41, -- 46
  .mov ⟨6, by decide⟩ ⟨11, by decide⟩ 48, -- 47
  .mov ⟨15, by decide⟩ ⟨9, by decide⟩ 49, -- 48
  .mov ⟨7, by decide⟩ ⟨3, by decide⟩ 50, -- 49
  .mov ⟨27, by decide⟩ ⟨6, by decide⟩ 51, -- 50
  .add ⟨11, by decide⟩ ⟨6, by decide⟩ ⟨7, by decide⟩ 52, -- 51
  .mov ⟨8, by decide⟩ ⟨11, by decide⟩ 53, -- 52
  .mov ⟨9, by decide⟩ ⟨0, by decide⟩ 54, -- 53
  .lt ⟨24, by decide⟩ ⟨27, by decide⟩ ⟨8, by decide⟩ 55, -- 54
  .branch ⟨24, by decide⟩ 60 56, -- 55
  .sub ⟨8, by decide⟩ ⟨8, by decide⟩ ⟨1, by decide⟩ 57, -- 56
  .load ⟨10, by decide⟩ ⟨8, by decide⟩ 58, -- 57
  .mul ⟨9, by decide⟩ ⟨9, by decide⟩ ⟨2, by decide⟩ 59, -- 58
  .add ⟨9, by decide⟩ ⟨9, by decide⟩ ⟨10, by decide⟩ 54, -- 59
  .mov ⟨6, by decide⟩ ⟨11, by decide⟩ 61, -- 60
  .mov ⟨16, by decide⟩ ⟨9, by decide⟩ 62, -- 61
  .mul ⟨25, by decide⟩ ⟨14, by decide⟩ ⟨2, by decide⟩ 63, -- 62
  .add ⟨25, by decide⟩ ⟨12, by decide⟩ ⟨25, by decide⟩ 64, -- 63
  .store ⟨25, by decide⟩ ⟨15, by decide⟩ 65, -- 64
  .add ⟨25, by decide⟩ ⟨25, by decide⟩ ⟨1, by decide⟩ 66, -- 65
  .store ⟨25, by decide⟩ ⟨16, by decide⟩ 67, -- 66
  .add ⟨14, by decide⟩ ⟨14, by decide⟩ ⟨1, by decide⟩ 34, -- 67
  .mov ⟨7, by decide⟩ ⟨5, by decide⟩ 69, -- 68
  .mov ⟨27, by decide⟩ ⟨6, by decide⟩ 70, -- 69
  .add ⟨11, by decide⟩ ⟨6, by decide⟩ ⟨7, by decide⟩ 71, -- 70
  .mov ⟨8, by decide⟩ ⟨11, by decide⟩ 72, -- 71
  .mov ⟨9, by decide⟩ ⟨0, by decide⟩ 73, -- 72
  .lt ⟨24, by decide⟩ ⟨27, by decide⟩ ⟨8, by decide⟩ 74, -- 73
  .branch ⟨24, by decide⟩ 79 75, -- 74
  .sub ⟨8, by decide⟩ ⟨8, by decide⟩ ⟨1, by decide⟩ 76, -- 75
  .load ⟨10, by decide⟩ ⟨8, by decide⟩ 77, -- 76
  .mul ⟨9, by decide⟩ ⟨9, by decide⟩ ⟨2, by decide⟩ 78, -- 77
  .add ⟨9, by decide⟩ ⟨9, by decide⟩ ⟨10, by decide⟩ 73, -- 78
  .mov ⟨6, by decide⟩ ⟨11, by decide⟩ 80, -- 79
  .mov ⟨17, by decide⟩ ⟨9, by decide⟩ 81, -- 80
  .store ⟨13, by decide⟩ ⟨4, by decide⟩ 82, -- 81
  .const ⟨25, by decide⟩ .A1 83, -- 82
  .store ⟨25, by decide⟩ ⟨5, by decide⟩ 84, -- 83
  .const ⟨25, by decide⟩ .A2 85, -- 84
  .store ⟨25, by decide⟩ ⟨17, by decide⟩ 86 -- 85
]

/-- Exact accepted W018 rows 86..109. -/
def linearBody : Array TemplateInstr := #[
  .load ⟨4, by decide⟩ ⟨13, by decide⟩ 87, -- 86
  .const ⟨25, by decide⟩ .A2 88, -- 87
  .load ⟨17, by decide⟩ ⟨25, by decide⟩ 89, -- 88
  .mov ⟨14, by decide⟩ ⟨0, by decide⟩ 90, -- 89
  .lt ⟨24, by decide⟩ ⟨14, by decide⟩ ⟨4, by decide⟩ 91, -- 90
  .branch ⟨24, by decide⟩ 106 92, -- 91
  .mul ⟨25, by decide⟩ ⟨14, by decide⟩ ⟨2, by decide⟩ 93, -- 92
  .add ⟨25, by decide⟩ ⟨12, by decide⟩ ⟨25, by decide⟩ 94, -- 93
  .load ⟨15, by decide⟩ ⟨25, by decide⟩ 95, -- 94
  .eq ⟨24, by decide⟩ ⟨15, by decide⟩ ⟨17, by decide⟩ 96, -- 95
  .branch ⟨24, by decide⟩ 97 100, -- 96
  .lt ⟨24, by decide⟩ ⟨15, by decide⟩ ⟨17, by decide⟩ 98, -- 97
  .branch ⟨24, by decide⟩ 106 99, -- 98
  .add ⟨14, by decide⟩ ⟨14, by decide⟩ ⟨1, by decide⟩ 90, -- 99
  .add ⟨25, by decide⟩ ⟨25, by decide⟩ ⟨1, by decide⟩ 101, -- 100
  .load ⟨16, by decide⟩ ⟨25, by decide⟩ 102, -- 101
  .store ⟨26, by decide⟩ ⟨1, by decide⟩ 103, -- 102
  .add ⟨25, by decide⟩ ⟨26, by decide⟩ ⟨1, by decide⟩ 104, -- 103
  .store ⟨25, by decide⟩ ⟨16, by decide⟩ 105, -- 104
  .halt, -- 105
  .store ⟨26, by decide⟩ ⟨0, by decide⟩ 107, -- 106
  .add ⟨25, by decide⟩ ⟨26, by decide⟩ ⟨1, by decide⟩ 108, -- 107
  .store ⟨25, by decide⟩ ⟨0, by decide⟩ 109, -- 108
  .halt -- 109
]

/-- Exact accepted W018 rows 86..114. -/
def binaryBody : Array TemplateInstr := #[
  .load ⟨4, by decide⟩ ⟨13, by decide⟩ 87, -- 86
  .const ⟨25, by decide⟩ .A2 88, -- 87
  .load ⟨17, by decide⟩ ⟨25, by decide⟩ 89, -- 88
  .mov ⟨18, by decide⟩ ⟨0, by decide⟩ 90, -- 89
  .mov ⟨19, by decide⟩ ⟨4, by decide⟩ 91, -- 90
  .lt ⟨24, by decide⟩ ⟨18, by decide⟩ ⟨19, by decide⟩ 92, -- 91
  .branch ⟨24, by decide⟩ 111 93, -- 92
  .sub ⟨21, by decide⟩ ⟨19, by decide⟩ ⟨18, by decide⟩ 94, -- 93
  .divmod ⟨22, by decide⟩ ⟨23, by decide⟩ ⟨21, by decide⟩ ⟨2, by decide⟩ 95, -- 94
  .add ⟨20, by decide⟩ ⟨18, by decide⟩ ⟨22, by decide⟩ 96, -- 95
  .mul ⟨25, by decide⟩ ⟨20, by decide⟩ ⟨2, by decide⟩ 97, -- 96
  .add ⟨25, by decide⟩ ⟨12, by decide⟩ ⟨25, by decide⟩ 98, -- 97
  .load ⟨15, by decide⟩ ⟨25, by decide⟩ 99, -- 98
  .eq ⟨24, by decide⟩ ⟨15, by decide⟩ ⟨17, by decide⟩ 100, -- 99
  .branch ⟨24, by decide⟩ 101 105, -- 100
  .lt ⟨24, by decide⟩ ⟨15, by decide⟩ ⟨17, by decide⟩ 102, -- 101
  .branch ⟨24, by decide⟩ 104 103, -- 102
  .add ⟨18, by decide⟩ ⟨20, by decide⟩ ⟨1, by decide⟩ 91, -- 103
  .mov ⟨19, by decide⟩ ⟨20, by decide⟩ 91, -- 104
  .add ⟨25, by decide⟩ ⟨25, by decide⟩ ⟨1, by decide⟩ 106, -- 105
  .load ⟨16, by decide⟩ ⟨25, by decide⟩ 107, -- 106
  .store ⟨26, by decide⟩ ⟨1, by decide⟩ 108, -- 107
  .add ⟨25, by decide⟩ ⟨26, by decide⟩ ⟨1, by decide⟩ 109, -- 108
  .store ⟨25, by decide⟩ ⟨16, by decide⟩ 110, -- 109
  .halt, -- 110
  .store ⟨26, by decide⟩ ⟨0, by decide⟩ 112, -- 111
  .add ⟨25, by decide⟩ ⟨26, by decide⟩ ⟨1, by decide⟩ 113, -- 112
  .store ⟨25, by decide⟩ ⟨0, by decide⟩ 114, -- 113
  .halt -- 114
]

def linearSkeleton : Array TemplateInstr := commonSkeleton ++ linearBody
def binarySkeleton : Array TemplateInstr := commonSkeleton ++ binaryBody

theorem commonSkeleton_size : commonSkeleton.size = 86 := by decide
theorem linearSkeleton_size : linearSkeleton.size = 110 := by decide
theorem binarySkeleton_size : binarySkeleton.size = 115 := by decide

def CodeFits (s : Sizes) (xs : Array TemplateInstr) : Prop :=
  xs.size ≤ s.U ∧ ∀ i ∈ xs, i.Fits s

instance (s : Sizes) (xs : Array TemplateInstr) : Decidable (CodeFits s xs) :=
  inferInstanceAs (Decidable (xs.size ≤ s.U ∧ ∀ i ∈ xs, i.Fits s))

/-- The intersection includes numerical layout, both actual array lengths and
all actual immediate/target words. Register bounds hold in the skeleton type. -/
def Admissible (s : Sizes) : Prop :=
  NumericallyAdmissible s ∧ CodeFits s linearSkeleton ∧ CodeFits s binarySkeleton

instance (s : Sizes) : Decidable (Admissible s) :=
  inferInstanceAs (Decidable (NumericallyAdmissible s ∧ CodeFits s linearSkeleton ∧
    CodeFits s binarySkeleton))

def instantiate (s : Sizes) (hn : NumericallyAdmissible s)
    (xs : Array TemplateInstr) (h : ∀ i ∈ xs, i.Fits s) : Array (Instr (profile s hn)) :=
  xs.pmap (instantiateInstr s hn) h

theorem instantiate_size (s : Sizes) (hn : NumericallyAdmissible s)
    (xs : Array TemplateInstr) (h : ∀ i ∈ xs, i.Fits s) :
    (instantiate s hn xs h).size = xs.size := by
  simp [instantiate]

def linear (s : Sizes) (h : Admissible s) : Program (profile s h.1) where
  code := instantiate s h.1 linearSkeleton h.2.1.2
  bounded := by rw [instantiate_size]; exact h.2.1.1

def binary (s : Sizes) (h : Admissible s) : Program (profile s h.1) where
  code := instantiate s h.1 binarySkeleton h.2.2.2
  bounded := by rw [instantiate_size]; exact h.2.2.1

theorem linear_size (s : Sizes) (h : Admissible s) : (linear s h).code.size = 110 := by
  simp [linear, instantiate_size, linearSkeleton_size]

theorem binary_size (s : Sizes) (h : Admissible s) : (binary s h).code.size = 115 := by
  simp [binary, instantiate_size, binarySkeleton_size]


/-- Static graph certificate: all fixed word literals are at most 114. -/
def Literal.StaticBound : Literal → Prop
  | .fixed n => n ≤ 114
  | _ => True

instance (l : Literal) : Decidable l.StaticBound := by
  cases l <;> simp [Literal.StaticBound] <;> infer_instance

theorem linear_static_bounds :
    ∀ i ∈ linearSkeleton, ∀ l ∈ i.words, l.StaticBound := by decide

theorem binary_static_bounds :
    ∀ i ∈ binarySkeleton, ∀ l ∈ i.words, l.StaticBound := by decide

theorem literal_bound (s : Sizes) (hn : NumericallyAdmissible s) (hw : 7 ≤ s.W)
    (l : Literal) (h : l.StaticBound) : l.eval s < s.U := by
  have hu : 128 ≤ s.U := Nat.pow_le_pow_right (n := 2) (i := 7) (by decide) hw
  have hh := header_bounds s hn
  have hl := layout_bounds s hn
  cases l <;> simp only [Literal.eval, Literal.StaticBound] at * <;> omega

theorem admissible_iff (s : Sizes) :
    Admissible s ↔ NumericallyAdmissible s ∧ 7 ≤ s.W := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    have hb := h.2.2.1
    rw [binarySkeleton_size] at hb
    by_cases hw : 7 ≤ s.W
    · exact hw
    · have hw6 : s.W ≤ 6 := by omega
      have hu : s.U ≤ 64 := Nat.pow_le_pow_right (n := 2) (j := 6) (by decide) hw6
      omega
  · rintro ⟨hn, hw⟩
    have hu : 128 ≤ s.U := Nat.pow_le_pow_right (n := 2) (i := 7) (by decide) hw
    refine ⟨hn, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [linearSkeleton_size]; omega
    · intro i hi l hl
      exact literal_bound s hn hw l (linear_static_bounds i hi l hl)
    · rw [binarySkeleton_size]; omega
    · intro i hi l hl
      exact literal_bound s hn hw l (binary_static_bounds i hi l hl)

/-- Admission evidence does not change either constructed code array. -/
theorem evidence_irrelevant (s : Sizes) (h₁ h₂ : Admissible s) :
    linear s h₁ = linear s h₂ ∧ binary s h₁ = binary s h₂ := ⟨rfl, rfl⟩

/-- Equal public sizes give identical programs, regardless of admission proofs.
Data is not an argument to the skeleton or any program constructor. -/
theorem size_only (s t : Sizes) (hs : Admissible s) (ht : Admissible t) (h : s = t) :
    HEq (linear s hs) (linear t ht) ∧ HEq (binary s hs) (binary t ht) := by
  subst t
  exact ⟨HEq.rfl, HEq.rfl⟩

theorem common_prefix (s : Sizes) (h : Admissible s) :
    (linear s h).code.extract 0 86 = (binary s h).code.extract 0 86 := by
  simp only [linear, binary, instantiate, linearSkeleton, binarySkeleton, Array.pmap_append]
  have hc : ∀ (hc : ∀ i ∈ commonSkeleton, i.Fits s),
      (commonSkeleton.pmap (instantiateInstr s h.1) hc).size = 86 := by
    intro hc
    simp [commonSkeleton_size]
  rw [← hc (fun a ha => h.2.1.2 a (Array.mem_append_left linearBody ha)),
    Array.extract_append_left]
  rw [hc]
  rw [← hc (fun a ha => h.2.2.2 a (Array.mem_append_left binaryBody ha)),
    Array.extract_append_left]

/-- Raw operand list in exactly WordCodec order; registers retain their indices. -/
def TemplateInstr.fields (s : Sizes) : TemplateInstr → List Nat
  | .const d v t => [d.val, v.eval s, t.eval s]
  | .mov d a t => [d.val, a.val, t.eval s]
  | .add d a b t | .sub d a b t | .mul d a b t | .eq d a b t | .lt d a b t =>
    [d.val, a.val, b.val, t.eval s]
  | .divmod dq dr a b t => [dq.val, dr.val, a.val, b.val, t.eval s]
  | .load d a t => [d.val, a.val, t.eval s]
  | .store a b t => [a.val, b.val, t.eval s]
  | .jump t => [t.eval s]
  | .branch a t0 t1 => [a.val, t0.eval s, t1.eval s]
  | .halt => []

theorem fields_instantiate (s : Sizes) (hn : NumericallyAdmissible s)
    (i : TemplateInstr) (h : i.Fits s) :
    WordCodec.fields (instantiateInstr s hn i h) = i.fields s := by
  cases i <;> rfl

def TemplateInstr.bitCount (s : Sizes) (i : TemplateInstr) : Nat :=
  4 + ((i.fields s).map (· + 1)).sum

theorem bits_instantiate (s : Sizes) (hn : NumericallyAdmissible s)
    (xs : Array TemplateInstr) (h : ∀ i ∈ xs, i.Fits s) :
    ((instantiate s hn xs h).toList.map
      (fun i => 4 + ((WordCodec.fields i).map (· + 1)).sum)).sum =
    (xs.toList.map (TemplateInstr.bitCount s)).sum := by
  simp only [instantiate, Array.toList_pmap, List.map_pmap]
  simp only [fields_instantiate, List.pmap_eq_map]
  rfl


/-- Sum of the actual codec field contributions, excluding the program-count
prefix. The graph is reduced once; all six varying slots remain symbolic. -/
theorem linear_field_bits (s : Sizes) :
    (linearSkeleton.toList.map (TemplateInstr.bitCount s)).sum =
      10094 + s.W + s.B + 4 * s.A + s.L := by
  simp only [linearSkeleton, Array.toList_append, List.map_append, List.sum_append,
    commonSkeleton, linearBody,  List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, TemplateInstr.bitCount, TemplateInstr.fields,
    Literal.eval]
  omega

theorem binary_field_bits (s : Sizes) :
    (binarySkeleton.toList.map (TemplateInstr.bitCount s)).sum =
      10966 + s.W + s.B + 4 * s.A + s.L := by
  simp only [binarySkeleton, Array.toList_append, List.map_append, List.sum_append,
    commonSkeleton, binaryBody,  List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, TemplateInstr.bitCount, TemplateInstr.fields,
    Literal.eval]
  omega

theorem linear_programBits (s : Sizes) (h : Admissible s) :
    programBits (linear s h) = 10205 + s.W + s.B + 4 * s.A + s.L := by
  rw [programBits_exact, linear_size]
  change 110 + 1 + ((instantiate s h.1 linearSkeleton h.2.1.2).toList.map
    (fun i => 4 + ((WordCodec.fields i).map (· + 1)).sum)).sum = _
  rw [bits_instantiate, linear_field_bits]
  omega

theorem binary_programBits (s : Sizes) (h : Admissible s) :
    programBits (binary s h) = 11082 + s.W + s.B + 4 * s.A + s.L := by
  rw [programBits_exact, binary_size]
  change 115 + 1 + ((instantiate s h.1 binarySkeleton h.2.2.2).toList.map
    (fun i => 4 + ((WordCodec.fields i).map (· + 1)).sum)).sum = _
  rw [bits_instantiate, binary_field_bits]
  omega

theorem profile_descriptor_bits (s : Sizes) (h : Admissible s) :
    (encodeProfile (profile s h.1)).length = s.W + s.M + s.L + 39 := by
  rw [encodeProfile_length]
  change s.W + 32 + s.M + s.L + 2 + 5 = _
  omega

theorem linear_manifest_bits (s : Sizes) (h : Admissible s) :
    (encodeManifest ⟨profile s h.1, linear s h⟩).length =
      (s.W + s.M + s.L + 39) + (10205 + s.W + s.B + 4 * s.A + s.L) := by
  rw [encodeManifest_length, linear_programBits]
  change s.W + 32 + s.M + s.L + 2 + 5 + _ = _
  omega

theorem binary_manifest_bits (s : Sizes) (h : Admissible s) :
    (encodeManifest ⟨profile s h.1, binary s h⟩).length =
      (s.W + s.M + s.L + 39) + (11082 + s.W + s.B + 4 * s.A + s.L) := by
  rw [encodeManifest_length, binary_programBits]
  change s.W + 32 + s.M + s.L + 2 + 5 + _ = _
  omega

/-- The public fuel descriptor is separate from input/program/manifest bits.
This length theorem supplies no proof that the challenge budget suffices. -/
theorem fuel_descriptor_bits (s : Sizes) : (unary s.F).length = s.F + 1 :=
  unary_length s.F

-- The eight accepted W018 public shapes, including all k=0/m=0/k=W cases.
theorem accepted_7_0_0 : Admissible ⟨7, 0, 0⟩ := by decide

theorem accepted_7_0_7 : Admissible ⟨7, 0, 7⟩ := by decide

theorem accepted_7_1_0 : Admissible ⟨7, 1, 0⟩ := by decide

theorem accepted_7_1_7 : Admissible ⟨7, 1, 7⟩ := by decide

theorem accepted_7_2_1 : Admissible ⟨7, 2, 1⟩ := by decide

theorem accepted_7_3_2 : Admissible ⟨7, 3, 2⟩ := by decide

theorem accepted_7_6_7 : Admissible ⟨7, 6, 7⟩ := by decide

theorem accepted_7_12_0 : Admissible ⟨7, 12, 0⟩ := by decide

theorem accepted_capacity_endpoint :
    (⟨7, 12, 0⟩ : Sizes).M = (⟨7, 12, 0⟩ : Sizes).U := by decide

theorem rejected_7_7_7 : ¬ Admissible ⟨7, 7, 7⟩ := by decide

theorem rejected_7_13_0 : ¬ Admissible ⟨7, 13, 0⟩ := by decide

/-- Numerical layout fitting does not by itself establish either code bound. -/
theorem rejected_6_0_0 :
    NumericallyAdmissible ⟨6, 0, 0⟩ ∧
    ¬ CodeFits ⟨6, 0, 0⟩ linearSkeleton ∧
    ¬ CodeFits ⟨6, 0, 0⟩ binarySkeleton := by decide

theorem rejected_width_le_six (s : Sizes) (h : s.W ≤ 6) : ¬ Admissible s := by
  intro ha
  have hw := (admissible_iff s).mp ha
  omega

theorem rejected_zero_width : ¬ Admissible ⟨0, 0, 0⟩ := by decide

end Research.WordQueryCode
