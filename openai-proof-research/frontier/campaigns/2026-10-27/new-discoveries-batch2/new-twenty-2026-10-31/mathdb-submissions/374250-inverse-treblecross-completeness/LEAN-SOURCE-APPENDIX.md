# Lean source appendix

MathDB 374250. Modules are in dependency order.

### `TBStatement.lean`

```lean
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.ZMod.Defs

/-!
# Inverse Treblecross: literal definitions (Liang–Li, arXiv:2604.16759 v1)

* Board: a `1 × n` strip, a list of cells; `true` is a cell holding an X, `false` an empty cell.
* Move: put an X on an empty cell. A move that creates three X's in a row is not legal
  ("completing a line of three is strictly prohibited"). Normal play: a player with no legal move loses.
* `sg`: the Sprague–Grundy value, the mex of the values of the options.
* `χ₁`, `χ₂` on `ℤ/10ℤ` via `a/3` (the source: "the map x ↦ x/3 (equivalently x ↦ 7x)").
* The regular set `R = R₁ ∪ R₋₁` of Definition 4.4, and Conjecture 5.1.
-/

namespace ITB

/-- three consecutive cells all hold an X -/
def ThreeInRow (s : List Bool) : Prop :=
  ∃ i, s[i]? = some true ∧ s[i + 1]? = some true ∧ s[i + 2]? = some true

/-- `t` is reached from `s` by one legal move -/
def IsMove (s t : List Bool) : Prop :=
  ∃ i, s[i]? = some false ∧ t = s.set i true ∧ ¬ ThreeInRow t

theorem count_false_lt_of_isMove {s t : List Bool} (h : IsMove s t) :
    t.count false < s.count false := by
  obtain ⟨i, hi, rfl, -⟩ := h
  obtain ⟨hlt, hv⟩ := List.getElem?_eq_some_iff.mp hi
  rw [List.count_set hlt]
  have : 0 < s.count false := List.count_pos_iff.mpr (hv ▸ List.getElem_mem hlt)
  simp [hv]
  omega

/-- The Sprague–Grundy value: the least natural number that is not the value of an option. -/
noncomputable def sg (s : List Bool) : ℕ :=
  sInf {n : ℕ | ∀ t, IsMove s t → sg t ≠ n}
termination_by s.count false
decreasing_by exact count_false_lt_of_isMove (by assumption)

/-- `[a]`: the empty board with `a` cells -/
def emptyBoard (a : ℕ) : List Bool := List.replicate a false

/-- `[aXb]`: `a` empty cells, one X, `b` empty cells -/
def board (a b : ℕ) : List Bool := List.replicate a false ++ [true] ++ List.replicate b false

/-- `a/3` in `ℤ/10ℤ` (`3 · 7 = 21 ≡ 1`); see `three_mul_div3` and `div3_unique` -/
def div3 (a : ZMod 10) : ZMod 10 := 7 * a

theorem three_mul_div3 (a : ZMod 10) : 3 * div3 a = a := by
  unfold div3; rw [← mul_assoc]; exact (by decide : (3 : ZMod 10) * 7 = 1) ▸ one_mul a

theorem div3_unique {a y : ZMod 10} (h : 3 * y = a) : y = div3 a := by
  unfold div3; rw [← h, ← mul_assoc]; exact ((by decide : (7 : ZMod 10) * 3 = 1) ▸ one_mul y).symm

/-- χ₁(a) = 1 if a/3 ∈ {0,1,2,3,4}, and −1 otherwise -/
def chi1 (a : ZMod 10) : ℤ := if div3 a ∈ ([0, 1, 2, 3, 4] : List (ZMod 10)) then 1 else -1

/-- χ₂(a) = 1 if a/3 ∈ {−1,0,1}, −1 if a/3 ∈ {4,5,6}, and 0 otherwise -/
def chi2 (a : ZMod 10) : ℤ :=
  if div3 a ∈ ([-1, 0, 1] : List (ZMod 10)) then 1
  else if div3 a ∈ ([4, 5, 6] : List (ZMod 10)) then -1 else 0

/-- Class R₁ of Definition 4.4: `R₁⁽⁰⁾`, `R₁⁽¹⁾` and `R₁*` = `[X6̄]`, `[6̄X]`, `[X4̄X]` -/
def R1 (s : List Bool) : Prop :=
  (∃ a : ℕ, s = emptyBoard a ∧ chi1 a = 1) ∨
  (∃ a b : ℕ, s = board a b ∧ chi2 a * chi2 b = 1) ∨
  (∃ k : ℕ, (k : ZMod 10) = 6 ∧ (s = board 0 k ∨ s = board k 0)) ∨
  (∃ k : ℕ, (k : ZMod 10) = 4 ∧ s = [true] ++ List.replicate k false ++ [true])

/-- Class R₋₁ of Definition 4.4: `R₋₁⁽⁰⁾`, `R₋₁⁽¹⁾` and `R₋₁*` = `[X1̄]`, `[1̄X]`, `[X9̄X]` -/
def Rm1 (s : List Bool) : Prop :=
  (∃ a : ℕ, s = emptyBoard a ∧ chi1 a = -1) ∨
  (∃ a b : ℕ, s = board a b ∧ chi2 a * chi2 b = -1) ∨
  (∃ k : ℕ, (k : ZMod 10) = 1 ∧ (s = board 0 k ∨ s = board k 0)) ∨
  (∃ k : ℕ, (k : ZMod 10) = 9 ∧ s = [true] ++ List.replicate k false ++ [true])

/-- the regular set `R = R₁ ∪ R₋₁` -/
def InR (s : List Bool) : Prop := R1 s ∨ Rm1 s

/-- the four exceptions `[1X1]`, `[1X4]`, `[4X1]`, `[4X4]` -/
def exceptions : List (List Bool) := [board 1 1, board 1 4, board 4 1, board 4 4]

/-- Conjecture 5.1 (v1): R contains all board states with at most one piece and `G ≤ 1`,
with exactly four exceptions `[1X1]`, `[1X4]`, `[4X1]`, `[4X4]`. -/
def Conjecture51 : Prop :=
  (∀ s : List Bool, s.count true ≤ 1 → sg s ≤ 1 → InR s ∨ s ∈ exceptions) ∧
  (∀ s ∈ exceptions, s.count true ≤ 1 ∧ sg s ≤ 1 ∧ ¬ InR s)

end ITB
```

### `TBGame.lean`

```lean
import TBStatement
import Mathlib.Data.Nat.Bitwise

/-!
# Inverse Treblecross: Sprague–Grundy basics and the sum theorem

* `sg_ne_of_isMove`, `exists_of_lt_sg`, `sg_eq_of`: the mex characterization of `sg`.
* `tir`: a Boolean version of `ThreeInRow`.
* `isMove_iff`: a move replaces one `false` by `true` (append form).
* `sg_rel`: Sprague–Grundy sum theorem in simulation form.
* `sg_wall`: a dead empty cell splits the board; `sg_guard`: a split that no line of three can cross.
-/

namespace ITB

/-! ## mex characterization -/

theorem sg_def (s : List Bool) : sg s = sInf {n : ℕ | ∀ t, IsMove s t → sg t ≠ n} := by
  rw [sg]

theorem exists_bound (s : List Bool) : ∃ N, ∀ t, IsMove s t → sg t < N := by
  have key : ∀ l : List ℕ, ∃ N, ∀ x ∈ l, x < N := by
    intro l
    induction l with
    | nil => exact ⟨0, by simp⟩
    | cons a l ih =>
      obtain ⟨N, hN⟩ := ih
      refine ⟨max N (a + 1), ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · have := hN x hx; omega
  obtain ⟨N, hN⟩ := key ((List.range s.length).map fun i => sg (s.set i true))
  refine ⟨N, fun t ht => ?_⟩
  obtain ⟨i, hi, rfl, -⟩ := ht
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hi
  exact hN _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hlt, rfl⟩)

theorem sg_mem (s : List Bool) : sg s ∈ {n : ℕ | ∀ t, IsMove s t → sg t ≠ n} := by
  rw [sg_def]
  apply Nat.sInf_mem
  obtain ⟨N, hN⟩ := exists_bound s
  exact ⟨N, fun t ht => (Nat.ne_of_lt (hN t ht))⟩

theorem sg_ne_of_isMove {s t : List Bool} (h : IsMove s t) : sg t ≠ sg s :=
  sg_mem s t h

theorem exists_of_lt_sg {s : List Bool} {u : ℕ} (h : u < sg s) : ∃ t, IsMove s t ∧ sg t = u := by
  rw [sg_def] at h
  have hn := Nat.notMem_of_lt_sInf h
  by_contra hne
  apply hn
  intro t ht e
  exact hne ⟨t, ht, e⟩

theorem sg_eq_of {s : List Bool} {v : ℕ} (h1 : ∀ u < v, ∃ t, IsMove s t ∧ sg t = u)
    (h2 : ∀ t, IsMove s t → sg t ≠ v) : sg s = v := by
  apply le_antisymm
  · rw [sg_def]; exact Nat.sInf_le h2
  · by_contra hlt
    rw [not_le] at hlt
    obtain ⟨t, ht, e⟩ := h1 _ hlt
    exact sg_ne_of_isMove ht e

theorem sg_eq_zero_of_noMove {s : List Bool} (h : ∀ t, ¬ IsMove s t) : sg s = 0 :=
  sg_eq_of (fun u hu => absurd hu (Nat.not_lt_zero u)) (fun t ht => absurd ht (h t))

/-! ## Boolean three-in-a-row -/

def tir : List Bool → Bool
  | a :: b :: c :: t => (a && b && c) || tir (b :: c :: t)
  | _ => false

theorem threeInRow_iff (s : List Bool) : ThreeInRow s ↔ tir s = true := by
  induction s with
  | nil => simp [ThreeInRow, tir]
  | cons a s ih =>
    constructor
    · rintro ⟨i, h0, h1, h2⟩
      cases i with
      | zero =>
        match s, h1, h2 with
        | b :: c :: t, h1, h2 =>
          simp at h0 h1 h2; simp [tir, h0, h1, h2]
      | succ i =>
        have : ThreeInRow s := ⟨i, by simpa using h0, by simpa using h1, by simpa using h2⟩
        have hs := ih.mp this
        match s, hs with
        | b :: c :: t, hs => simp [tir, hs]
    · intro h
      match s, h, ih with
      | b :: c :: t, h, ih =>
        simp only [tir, Bool.or_eq_true, Bool.and_eq_true] at h
        rcases h with ⟨⟨ha, hb⟩, hc⟩ | h
        · exact ⟨0, by simp [ha], by simp [hb], by simp [hc]⟩
        · obtain ⟨i, h0, h1, h2⟩ := ih.mpr h
          exact ⟨i + 1, by simpa using h0, by simpa using h1, by simpa using h2⟩

theorem not_threeInRow_iff (s : List Bool) : ¬ ThreeInRow s ↔ tir s = false := by
  rw [threeInRow_iff]; simp

@[simp] theorem tir_nil : tir [] = false := rfl
@[simp] theorem tir_single (a : Bool) : tir [a] = false := rfl
@[simp] theorem tir_pair (a b : Bool) : tir [a, b] = false := rfl
@[simp] theorem tir_cons3 (a b c : Bool) (t : List Bool) :
    tir (a :: b :: c :: t) = ((a && b && c) || tir (b :: c :: t)) := rfl

@[simp] theorem tir_false_cons (l : List Bool) : tir (false :: l) = tir l := by
  match l with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => simp

theorem tir_cons_false_cons (a : Bool) (l : List Bool) : tir (a :: false :: l) = tir l := by
  match l with
  | [] => rfl
  | _ :: _ => simp

theorem tir_cons2_false_cons (a b : Bool) (l : List Bool) : tir (a :: b :: false :: l) = tir l := by
  simp [tir_cons_false_cons]

/-- windows meeting `y` lie in the last two cells of `x` followed by `y` -/
theorem tir_append (x y : List Bool) :
    tir (x ++ y) = (tir x || tir (x.drop (x.length - 2) ++ y)) := by
  induction x with
  | nil => simp
  | cons a x ih =>
    match x, ih with
    | [], _ => simp
    | [b], _ => simp
    | b :: c :: x', ih =>
      have e : (a :: b :: c :: x').length - 2 = (b :: c :: x').length - 2 + 1 := by simp
      rw [e, List.drop_succ_cons]
      simp only [List.cons_append, tir_cons3] at ih ⊢
      rw [ih]
      simp [Bool.or_assoc]

theorem tir_append_left {x : List Bool} (y : List Bool) (h : tir x = true) : tir (x ++ y) = true := by
  rw [tir_append, h]; rfl

theorem tir_append_right (x : List Bool) {y : List Bool} (h : tir y = true) : tir (x ++ y) = true := by
  induction x with
  | nil => simpa using h
  | cons a x ih =>
    match x, ih with
    | [], ih => simp at ih; match y, ih with | _ :: _ :: _, ih => simp [ih]
    | [b], ih => simp at ih; match y, ih with | _ :: _ :: _, ih => simp [ih]
    | b :: c :: x', ih => simp at ih ⊢; simp [ih]

theorem tir_false_of_append_left {x y : List Bool} (h : tir (x ++ y) = false) : tir x = false := by
  cases hx : tir x
  · rfl
  · have := tir_append_left y hx; rw [h] at this; cases this

theorem tir_false_of_append_right {x y : List Bool} (h : tir (x ++ y) = false) : tir y = false := by
  cases hy : tir y
  · rfl
  · have := tir_append_right x hy; rw [h] at this; cases this

theorem drop_two_length_le (x : List Bool) :
    x.drop (x.length - 2) = [] ∨ (∃ a, x.drop (x.length - 2) = [a]) ∨
      ∃ a b, x.drop (x.length - 2) = [a, b] := by
  have hl : (x.drop (x.length - 2)).length ≤ 2 := by simp; omega
  match h : x.drop (x.length - 2), hl with
  | [], _ => exact Or.inl rfl
  | [a], _ => exact Or.inr (Or.inl ⟨a, rfl⟩)
  | [a, b], _ => exact Or.inr (Or.inr ⟨a, b, rfl⟩)

/-- a dead (always empty) cell separates the board -/
theorem tir_wall (x y : List Bool) : tir (x ++ false :: y) = (tir x || tir y) := by
  rw [tir_append]
  rcases drop_two_length_le x with h | ⟨a, h⟩ | ⟨a, b, h⟩ <;> rw [h]
  · simp
  · simp [tir_cons_false_cons]
  · simp [tir_cons_false_cons]

/-! ## moves in append form -/

theorem isMove_iff {s t : List Bool} :
    IsMove s t ↔ ∃ l r, s = l ++ false :: r ∧ t = l ++ true :: r ∧ tir t = false := by
  constructor
  · rintro ⟨i, hi, rfl, ht⟩
    obtain ⟨hlt, hv⟩ := List.getElem?_eq_some_iff.mp hi
    refine ⟨s.take i, s.drop (i + 1), ?_, ?_, (not_threeInRow_iff _).mp ht⟩
    · conv_lhs => rw [← List.take_append_drop i s]
      rw [List.drop_eq_getElem_cons hlt, hv]
    · rw [List.set_eq_take_append_cons_drop]; simp [hlt]
  · rintro ⟨l, r, rfl, rfl, ht⟩
    refine ⟨l.length, by simp, by simp, (not_threeInRow_iff _).mpr ht⟩

theorem isMove_of {l r : List Bool} (h : tir (l ++ true :: r) = false) :
    IsMove (l ++ false :: r) (l ++ true :: r) :=
  isMove_iff.mpr ⟨l, r, rfl, rfl, h⟩

/-- where the played cell lies in a concatenation -/
theorem locate2 {x y l r : List Bool} (h : x ++ y = l ++ false :: r) :
    (∃ r', x = l ++ false :: r' ∧ r = r' ++ y) ∨ (∃ l', y = l' ++ false :: r ∧ l = x ++ l') := by
  rcases List.append_eq_append_iff.mp h with ⟨as, h1, h2⟩ | ⟨cs, h1, h2⟩
  · exact Or.inr ⟨as, h2, h1⟩
  · cases cs with
    | nil => simp at h2 h1; exact Or.inr ⟨[], by simp [h2], by simp [h1]⟩
    | cons c cs =>
      simp at h2; obtain ⟨rfl, rfl⟩ := h2
      exact Or.inl ⟨cs, h1, rfl⟩

/-! ## pointwise growth -/

/-- `x'` has an X wherever `x` has one (same length) -/
def Mono : List Bool → List Bool → Prop
  | [], [] => True
  | a :: l, b :: m => (a = true → b = true) ∧ Mono l m
  | _, _ => False

theorem Mono.refl : ∀ l : List Bool, Mono l l
  | [] => trivial
  | _ :: l => ⟨id, Mono.refl l⟩

theorem Mono.append : ∀ {a a' b b' : List Bool}, Mono a a' → Mono b b' → Mono (a ++ b) (a' ++ b')
  | [], [], _, _, _, hb => hb
  | _ :: _, _ :: _, _, _, ⟨h, ha⟩, hb => ⟨h, Mono.append ha hb⟩

theorem Mono.of_move (l r : List Bool) : Mono (l ++ false :: r) (l ++ true :: r) :=
  Mono.append (Mono.refl l) ⟨fun _ => rfl, Mono.refl r⟩

theorem Mono.split : ∀ {a b z : List Bool}, Mono (a ++ b) z → ∃ a' b', z = a' ++ b' ∧ Mono a a' ∧ Mono b b'
  | [], _, z, h => ⟨[], z, rfl, trivial, h⟩
  | _ :: a, b, w :: z, ⟨h1, h⟩ => by
      obtain ⟨a', b', rfl, ha, hb⟩ := Mono.split (a := a) (b := b) h
      exact ⟨w :: a', b', rfl, ⟨h1, ha⟩, hb⟩
  | _ :: _, _, [], h => False.elim h

theorem Mono.true_cons : ∀ {l z : List Bool}, Mono (true :: l) z → ∃ z', z = true :: z' ∧ Mono l z'
  | _, b :: z, ⟨h1, h⟩ => ⟨z, by rw [h1 rfl], h⟩
  | _, [], h => False.elim h

theorem Mono.cons : ∀ {a : Bool} {l z : List Bool}, Mono (a :: l) z → ∃ b z', z = b :: z' ∧ Mono l z'
  | _, _, b :: z, ⟨_, h⟩ => ⟨b, z, rfl, h⟩
  | _, _, [], h => False.elim h

theorem Mono.nil_right : ∀ {z : List Bool}, Mono [] z → z = []
  | [], _ => rfl
  | _ :: _, h => False.elim h

/-! ## the sum theorem -/

theorem xor_ne_xor {a b c : ℕ} (h : a ≠ b) : a ^^^ c ≠ b ^^^ c := by
  intro e; apply h
  have := congrArg (· ^^^ c) e
  simpa [Nat.xor_assoc] using this

theorem sg_rel (R : List Bool → List Bool → List Bool → Prop)
    (h1 : ∀ s x y, R s x y → ∀ s', IsMove s s' →
      (∃ x', IsMove x x' ∧ R s' x' y) ∨ (∃ y', IsMove y y' ∧ R s' x y'))
    (h2 : ∀ s x y, R s x y → ∀ x', IsMove x x' → ∃ s', IsMove s s' ∧ R s' x' y)
    (h3 : ∀ s x y, R s x y → ∀ y', IsMove y y' → ∃ s', IsMove s s' ∧ R s' x y') :
    ∀ s x y, R s x y → sg s = sg x ^^^ sg y := by
  suffices H : ∀ n, ∀ s x y, x.count false + y.count false = n → R s x y → sg s = sg x ^^^ sg y from
    fun s x y h => H _ s x y rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s x y hn hR
    apply sg_eq_of
    · intro u hu
      rcases Nat.lt_xor_cases hu with h | h
      · obtain ⟨x', hx', e⟩ := exists_of_lt_sg h
        obtain ⟨s', hs', hR'⟩ := h2 s x y hR x' hx'
        refine ⟨s', hs', ?_⟩
        have hlt := count_false_lt_of_isMove hx'
        rw [ih _ (by omega) s' x' y rfl hR', e, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      · obtain ⟨y', hy', e⟩ := exists_of_lt_sg h
        obtain ⟨s', hs', hR'⟩ := h3 s x y hR y' hy'
        refine ⟨s', hs', ?_⟩
        have hlt := count_false_lt_of_isMove hy'
        rw [ih _ (by omega) s' x y' rfl hR', e, Nat.xor_comm u, ← Nat.xor_assoc, Nat.xor_self,
          Nat.zero_xor]
    · intro s' hs'
      rcases h1 s x y hR s' hs' with ⟨x', hx', hR'⟩ | ⟨y', hy', hR'⟩
      · have hlt := count_false_lt_of_isMove hx'
        rw [ih _ (by omega) s' x' y rfl hR']
        exact xor_ne_xor (sg_ne_of_isMove hx')
      · have hlt := count_false_lt_of_isMove hy'
        rw [ih _ (by omega) s' x y' rfl hR', Nat.xor_comm, Nat.xor_comm (sg x)]
        exact xor_ne_xor (sg_ne_of_isMove hy')

/-! ## dead cells -/

/-- the cell between `x` and `y` can never be filled -/
def Dead (x y : List Bool) : Prop :=
  (∃ x0, x = x0 ++ [true, true]) ∨ (∃ y0, y = true :: true :: y0) ∨
    ((∃ x0, x = x0 ++ [true]) ∧ ∃ y0, y = true :: y0)

theorem Dead.mono_left {x x' y : List Bool} (h : Dead x y) (hm : Mono x x') : Dead x' y := by
  rcases h with ⟨x0, rfl⟩ | hy | ⟨⟨x0, rfl⟩, hy⟩
  · obtain ⟨a', b', rfl, -, hb⟩ := Mono.split hm
    obtain ⟨z, rfl, hz⟩ := Mono.true_cons hb
    obtain ⟨z', rfl, hz'⟩ := Mono.true_cons hz
    rw [Mono.nil_right hz']
    exact Or.inl ⟨a', rfl⟩
  · exact Or.inr (Or.inl hy)
  · obtain ⟨a', b', rfl, -, hb⟩ := Mono.split hm
    obtain ⟨z, rfl, hz⟩ := Mono.true_cons hb
    rw [Mono.nil_right hz]
    exact Or.inr (Or.inr ⟨⟨a', rfl⟩, hy⟩)

theorem Dead.mono_right {x y y' : List Bool} (h : Dead x y) (hm : Mono y y') : Dead x y' := by
  rcases h with hx | ⟨y0, rfl⟩ | ⟨hx, ⟨y0, rfl⟩⟩
  · exact Or.inl hx
  · obtain ⟨z, rfl, hz⟩ := Mono.true_cons hm
    obtain ⟨z', rfl, -⟩ := Mono.true_cons hz
    exact Or.inr (Or.inl ⟨z', rfl⟩)
  · obtain ⟨z, rfl, -⟩ := Mono.true_cons hm
    exact Or.inr (Or.inr ⟨hx, ⟨z, rfl⟩⟩)

theorem Dead.tir_fill {x y : List Bool} (h : Dead x y) : tir (x ++ true :: y) = true := by
  rcases h with ⟨x0, rfl⟩ | ⟨y0, rfl⟩ | ⟨⟨x0, rfl⟩, ⟨y0, rfl⟩⟩
  · rw [List.append_assoc]; apply tir_append_right x0; simp
  · apply tir_append_right x; simp
  · rw [List.append_assoc]; apply tir_append_right x0; simp

/-- a dead cell splits the board into independent parts -/
theorem sg_wall {x y : List Bool} (hD : Dead x y) (h : tir (x ++ false :: y) = false) :
    sg (x ++ false :: y) = sg x ^^^ sg y := by
  let R : List Bool → List Bool → List Bool → Prop := fun s x y =>
    s = x ++ false :: y ∧ tir s = false ∧ Dead x y
  refine sg_rel R ?_ ?_ ?_ _ x y ⟨rfl, h, hD⟩
  · rintro s x y ⟨rfl, hs, hD⟩ s' hs'
    obtain ⟨l, r, e, rfl, ht⟩ := isMove_iff.mp hs'
    rcases locate2 e with ⟨r', rfl, rfl⟩ | ⟨l', e2, rfl⟩
    · left
      refine ⟨l ++ true :: r', isMove_of ?_, by simp, by simpa using ht, hD.mono_left (Mono.of_move _ _)⟩
      exact tir_false_of_append_left (y := false :: y) (by simpa using ht)
    · cases l' with
      | nil =>
        simp at e2; subst e2
        have := hD.tir_fill; simp at ht; rw [ht] at this; exact absurd this (by simp)
      | cons c l' =>
        simp at e2; obtain ⟨rfl, rfl⟩ := e2
        right
        refine ⟨l' ++ true :: r, isMove_of ?_, by simp, by simpa using ht,
          hD.mono_right (Mono.of_move _ _)⟩
        exact tir_false_of_append_right (x := x ++ [false]) (by simpa using ht)
  · rintro s x y ⟨rfl, hs, hD⟩ x' hx'
    obtain ⟨l, r, rfl, rfl, ht⟩ := isMove_iff.mp hx'
    refine ⟨l ++ true :: r ++ false :: y, ?_, rfl, ?_, hD.mono_left (Mono.of_move _ _)⟩
    · have : tir (l ++ true :: r ++ false :: y) = false := by
        rw [tir_wall, ht, tir_false_of_append_right (x := l ++ false :: r ++ [false]) (by simpa using hs)]; rfl
      have e := isMove_of (l := l) (r := r ++ false :: y) (by simpa using this)
      simpa using e
    · rw [tir_wall, ht, tir_false_of_append_right (x := l ++ false :: r ++ [false]) (by simpa using hs)]; rfl
  · rintro s x y ⟨rfl, hs, hD⟩ y' hy'
    obtain ⟨l, r, rfl, rfl, ht⟩ := isMove_iff.mp hy'
    refine ⟨x ++ false :: (l ++ true :: r), ?_, rfl, ?_, hD.mono_right (Mono.of_move _ _)⟩
    · have : tir (x ++ false :: (l ++ true :: r)) = false := by
        rw [tir_wall, ht, tir_false_of_append_left (y := false :: (l ++ false :: r)) hs]; rfl
      have e := isMove_of (l := x ++ false :: l) (r := r) (by simpa using this)
      simpa using e
    · rw [tir_wall, ht, tir_false_of_append_left (y := false :: (l ++ false :: r)) hs]; rfl

/-! ## guarded splits (Lemma 3.3 of the source) -/

/-- `x` ends with `X _ _` -/
def LG (x : List Bool) : Prop := ∃ x0 a b, x = x0 ++ [true, a, b]

/-- `y` starts with `_ _ X` -/
def RG (y : List Bool) : Prop := ∃ c d y0, y = c :: d :: true :: y0

/-- no line of three can ever cross between `x` and `y` -/
def Guard (x y : List Bool) : Prop := ((LG x ∨ x = [true]) ∧ RG y) ∨ (LG x ∧ y = [true])

theorem LG.mono {x x' : List Bool} (h : LG x) (hm : Mono x x') : LG x' := by
  obtain ⟨x0, a, b, rfl⟩ := h
  obtain ⟨a', b', rfl, -, hb⟩ := Mono.split hm
  obtain ⟨z1, rfl, hz1⟩ := Mono.true_cons hb
  obtain ⟨c, z2, rfl, hz2⟩ := Mono.cons hz1
  obtain ⟨d, z3, rfl, hz3⟩ := Mono.cons hz2
  rw [Mono.nil_right hz3]
  exact ⟨a', c, d, rfl⟩

theorem RG.mono {y y' : List Bool} (h : RG y) (hm : Mono y y') : RG y' := by
  obtain ⟨c, d, y0, rfl⟩ := h
  obtain ⟨c', z1, rfl, hz1⟩ := Mono.cons hm
  obtain ⟨d', z2, rfl, hz2⟩ := Mono.cons hz1
  obtain ⟨z3, rfl, -⟩ := Mono.true_cons hz2
  exact ⟨c', d', z3, rfl⟩

theorem Guard.mono_left {x x' y : List Bool} (h : Guard x y) (hm : Mono x x') : Guard x' y := by
  rcases h with ⟨hx | rfl, hy⟩ | ⟨hx, hy⟩
  · exact Or.inl ⟨Or.inl (hx.mono hm), hy⟩
  · obtain ⟨z, rfl, hz⟩ := Mono.true_cons hm
    rw [Mono.nil_right hz]; exact Or.inl ⟨Or.inr rfl, hy⟩
  · exact Or.inr ⟨hx.mono hm, hy⟩

theorem Guard.mono_right {x y y' : List Bool} (h : Guard x y) (hm : Mono y y') : Guard x y' := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, rfl⟩
  · exact Or.inl ⟨hx, hy.mono hm⟩
  · obtain ⟨z, rfl, hz⟩ := Mono.true_cons hm
    rw [Mono.nil_right hz]; exact Or.inr ⟨hx, rfl⟩

theorem Guard.noTir {x y : List Bool} (h : Guard x y) (hx : tir x = false) (hy : tir y = false) :
    tir (x ++ y) = false := by
  have lg : ∀ x0 a b, tir (x0 ++ [true, a, b]) = false → (a && b) = false := by
    intro x0 a b h
    have := tir_false_of_append_right (x := x0) h
    simpa using this
  rcases h with ⟨⟨x0, a, b, rfl⟩ | rfl, ⟨c, d, y0, rfl⟩⟩ | ⟨⟨x0, a, b, rfl⟩, rfl⟩
  · have hab := lg x0 a b hx
    have hcd : (c && d) = false := by cases c <;> cases d <;> simp_all
    rw [tir_append, hx]
    have e : (x0 ++ [true, a, b]).drop ((x0 ++ [true, a, b]).length - 2) = [a, b] := by
      simp [List.drop_append]
    rw [e]
    have hy' := hy
    simp at hy' ⊢
    cases a <;> cases b <;> cases c <;> cases d <;> simp_all
  · simp at hy ⊢; cases c <;> cases d <;> simp_all
  · have hab := lg x0 a b hx
    rw [tir_append, hx]
    have e : (x0 ++ [true, a, b]).drop ((x0 ++ [true, a, b]).length - 2) = [a, b] := by
      simp [List.drop_append]
    rw [e]
    cases a <;> cases b <;> simp_all

theorem sg_guard {x y : List Bool} (hG : Guard x y) (hx : tir x = false) (hy : tir y = false) :
    sg (x ++ y) = sg x ^^^ sg y := by
  let R : List Bool → List Bool → List Bool → Prop := fun s x y =>
    s = x ++ y ∧ tir x = false ∧ tir y = false ∧ Guard x y
  refine sg_rel R ?_ ?_ ?_ _ x y ⟨rfl, hx, hy, hG⟩
  · rintro s x y ⟨rfl, hx, hy, hG⟩ s' hs'
    obtain ⟨l, r, e, rfl, ht⟩ := isMove_iff.mp hs'
    rcases locate2 e with ⟨r', rfl, rfl⟩ | ⟨l', rfl, rfl⟩
    · left
      have h' : tir (l ++ true :: r') = false :=
        tir_false_of_append_left (y := y) (by simpa using ht)
      exact ⟨_, isMove_of h', by simp, h', hy, hG.mono_left (Mono.of_move _ _)⟩
    · right
      have h' : tir (l' ++ true :: r) = false :=
        tir_false_of_append_right (x := x) (by simpa using ht)
      exact ⟨_, isMove_of h', by simp, hx, h', hG.mono_right (Mono.of_move _ _)⟩
  · rintro s x y ⟨rfl, hx, hy, hG⟩ x' hx'
    obtain ⟨l, r, rfl, rfl, ht⟩ := isMove_iff.mp hx'
    have hG' := hG.mono_left (Mono.of_move l r)
    have := hG'.noTir ht hy
    refine ⟨_, ?_, rfl, ht, hy, hG'⟩
    have e := isMove_of (l := l) (r := r ++ y) (by simpa using this)
    simpa using e
  · rintro s x y ⟨rfl, hx, hy, hG⟩ y' hy'
    obtain ⟨l, r, rfl, rfl, ht⟩ := isMove_iff.mp hy'
    have hG' := hG.mono_right (Mono.of_move l r)
    have := hG'.noTir hx ht
    refine ⟨_, ?_, rfl, hx, ht, hG'⟩
    have e := isMove_of (l := x ++ l) (r := r) (by simpa using this)
    simpa using e

theorem sg_of_count_false_eq_zero {s : List Bool} (h : s.count false = 0) : sg s = 0 := by
  apply sg_eq_zero_of_noMove
  intro t ht
  have := count_false_lt_of_isMove ht
  omega

end ITB
```

### `TBGaps.lean`

```lean
import TBGame

/-!
# Gap lists

`ofGaps [g0, g1, ..., gk]` is the board with `g0` empty cells, an X, `g1` empty cells, an X, ...,
an X, `gk` empty cells. Every board has this form. We prove:

* `tir_ofGaps`: three in a row ↔ two consecutive internal gaps are both `0`;
* `move_ofGaps`, `split_ofGaps`: the moves of `ofGaps gs` are exactly the gap splits;
* the reduction rules used by the certificate (`rule_TT`, `rule_one`, `rule_four`, `rule_x2x_left`,
  `rule_x2x_right`), as identities of Sprague–Grundy values.
-/

namespace ITB

open List

def ofGaps : List ℕ → List Bool
  | [] => []
  | [n] => replicate n false
  | n :: m :: t => replicate n false ++ true :: ofGaps (m :: t)

/-- what follows the first gap -/
def tl : List ℕ → List Bool
  | [] => []
  | y :: ys => true :: ofGaps (y :: ys)

/-- what precedes the last gap -/
def hd : List ℕ → List Bool
  | [] => []
  | x :: xs => ofGaps (x :: xs) ++ [true]

@[simp] theorem tl_nil : tl [] = [] := rfl
@[simp] theorem tl_cons (y : ℕ) (ys : List ℕ) : tl (y :: ys) = true :: ofGaps (y :: ys) := rfl
@[simp] theorem hd_nil : hd [] = [] := rfl

theorem hd_of_ne {zs : List ℕ} (h : zs ≠ []) : hd zs = ofGaps zs ++ [true] := by
  cases zs with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

theorem ofGaps_cons (g : ℕ) (ys : List ℕ) : ofGaps (g :: ys) = replicate g false ++ tl ys := by
  cases ys <;> simp [ofGaps, tl]

theorem ofGaps_append (xs zs : List ℕ) (hz : zs ≠ []) : ofGaps (xs ++ zs) = hd xs ++ ofGaps zs := by
  induction xs with
  | nil => simp [hd]
  | cons a xs ih =>
    cases xs with
    | nil =>
      obtain ⟨z, zs', rfl⟩ := List.exists_cons_of_ne_nil hz
      simp [ofGaps, hd]
    | cons b xs =>
      have : b :: xs ++ zs ≠ [] := by simp
      obtain ⟨z, zs', e⟩ := List.exists_cons_of_ne_nil this
      rw [List.cons_append, e, ofGaps, ← e, ih]
      simp [hd, ofGaps]

theorem hd_append_single (xs : List ℕ) (p : ℕ) : hd (xs ++ [p]) = hd xs ++ replicate p false ++ [true] := by
  cases xs with
  | nil => simp [ofGaps, hd]
  | cons a xs =>
    rw [hd_of_ne (by simp), ofGaps_append _ _ (by simp)]
    simp [ofGaps]

theorem ofGaps_snoc (xs : List ℕ) (p : ℕ) : ofGaps (xs ++ [p]) = hd xs ++ replicate p false := by
  rw [ofGaps_append _ _ (by simp)]; rfl

theorem count_ofGaps : ∀ gs : List ℕ, (ofGaps gs).count false = gs.sum
  | [] => rfl
  | [n] => by simp [ofGaps]
  | n :: m :: t => by
    have := count_ofGaps (m :: t)
    simp only [ofGaps] at this ⊢
    simp [this, List.sum_cons]

theorem board_eq_ofGaps (a b : ℕ) : board a b = ofGaps [a, b] := by
  simp [board, ofGaps]

theorem emptyBoard_eq_ofGaps (a : ℕ) : emptyBoard a = ofGaps [a] := rfl

/-! ## three in a row on gap lists -/

/-- two consecutive internal gaps are both zero (input: the list without its first gap) -/
def cz : List ℕ → Prop
  | a :: b :: c :: t => (a = 0 ∧ b = 0) ∨ cz (b :: c :: t)
  | _ => False

theorem tir_replicate_append (n : ℕ) (l : List Bool) : tir (replicate n false ++ l) = tir l := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.cons_append, tir_false_cons, ih]

theorem tir_replicate (n : ℕ) : tir (replicate n false) = false := by
  simpa using tir_replicate_append n []

theorem tir_true_ofGaps : ∀ u : List ℕ, tir (true :: ofGaps u) = true ↔ cz u
  | [] => by simp [ofGaps, cz]
  | [a] => by
    simp only [ofGaps, cz, iff_false]
    cases a with
    | zero => simp
    | succ a => rw [List.replicate_succ, tir_cons_false_cons, tir_replicate]; simp
  | [a, b] => by
    simp only [ofGaps, cz, iff_false]
    cases a with
    | zero =>
      cases b with
      | zero => simp
      | succ b => simp [List.replicate_succ]; rw [tir_cons_false_cons, tir_replicate]
    | succ a =>
      rw [List.replicate_succ, List.cons_append, tir_cons_false_cons, tir_replicate_append]
      cases b with
      | zero => simp
      | succ b => rw [List.replicate_succ, tir_cons_false_cons, tir_replicate]; simp
  | a :: b :: c :: t => by
    have ih := tir_true_ofGaps (b :: c :: t)
    have key : tir (true :: ofGaps (a :: b :: c :: t)) =
        tir (true :: replicate a false ++ true :: ofGaps (b :: c :: t)) := by simp [ofGaps]
    rw [key]
    simp only [cz]
    cases a with
    | succ a =>
      rw [List.replicate_succ, List.cons_append, List.cons_append, tir_cons_false_cons,
        tir_replicate_append, ih]
      simp
    | zero =>
      simp only [List.replicate_zero, List.cons_append, List.nil_append]
      cases b with
      | zero => simp [ofGaps]
      | succ b =>
        have e1 : tir (true :: true :: ofGaps ((b + 1) :: c :: t)) =
            tir (true :: ofGaps ((b + 1) :: c :: t)) := by
          simp only [ofGaps, List.replicate_succ, List.cons_append]
          rw [tir_cons2_false_cons, tir_cons_false_cons]
        rw [e1, ih]; simp

theorem tir_ofGaps (g0 : ℕ) (t : List ℕ) : tir (ofGaps (g0 :: t)) = true ↔ cz t := by
  cases t with
  | nil => simp [ofGaps, tir_replicate, cz]
  | cons a t =>
    rw [ofGaps, tir_replicate_append]
    exact tir_true_ofGaps (a :: t)

/-! ## moves are gap splits -/

theorem split_ofGaps (xs ys : List ℕ) (j k : ℕ) :
    ofGaps (xs ++ (j + 1 + k) :: ys) = (hd xs ++ replicate j false) ++ false :: (replicate k false ++ tl ys) ∧
    ofGaps (xs ++ j :: k :: ys) = (hd xs ++ replicate j false) ++ true :: (replicate k false ++ tl ys) := by
  rw [ofGaps_append _ _ (by simp), ofGaps_append _ _ (by simp), ofGaps_cons, ofGaps_cons, tl_cons,
    ofGaps_cons]
  constructor
  · rw [show j + 1 + k = j + (k + 1) by omega, List.replicate_add, List.replicate_succ]; simp
  · simp

theorem eq_replicate_of_append {l r : List Bool} {g : ℕ} (h : l ++ false :: r = replicate g false) :
    l = replicate l.length false ∧ r = replicate r.length false ∧ g = l.length + 1 + r.length := by
  have hl := congrArg List.length h
  simp at hl
  have hall : ∀ x ∈ l ++ false :: r, x = false := fun x hx => by
    rw [h] at hx; exact (List.mem_replicate.mp hx).2
  refine ⟨List.eq_replicate_iff.mpr ⟨rfl, fun x hx => hall x (by simp [hx])⟩,
    List.eq_replicate_iff.mpr ⟨rfl, fun x hx => hall x (by simp [hx])⟩, by omega⟩

theorem move_ofGaps : ∀ (gs : List ℕ) (l r : List Bool), ofGaps gs = l ++ false :: r →
    ∃ xs g ys j k, gs = xs ++ g :: ys ∧ g = j + 1 + k ∧ l ++ true :: r = ofGaps (xs ++ j :: k :: ys)
  | [], l, r, h => by simp [ofGaps] at h
  | g :: ys, l, r, h => by
    rw [ofGaps_cons] at h
    rcases locate2 h with ⟨r', e1, rfl⟩ | ⟨l', e2, rfl⟩
    · obtain ⟨hl, hr, hg⟩ := eq_replicate_of_append e1.symm
      refine ⟨[], g, ys, l.length, r'.length, rfl, hg, ?_⟩
      rw [(split_ofGaps [] ys l.length r'.length).2, ← hl, ← hr]; simp [hd]
    · cases ys with
      | nil => simp [tl] at e2
      | cons y ys =>
        cases l' with
        | nil => simp [tl] at e2
        | cons c l'' =>
          simp only [tl_cons, List.cons_append, List.cons.injEq] at e2
          obtain ⟨hc, e3⟩ := e2
          subst hc
          obtain ⟨xs, g', ys', j, k, e4, hg, e5⟩ := move_ofGaps (y :: ys) l'' r e3
          refine ⟨g :: xs, g', ys', j, k, by simp [e4], hg, ?_⟩
          have : xs ++ j :: k :: ys' ≠ [] := by simp
          obtain ⟨z, zs, ez⟩ := List.exists_cons_of_ne_nil this
          rw [List.cons_append, ofGaps_cons, ez, tl_cons, ← ez, ← e5]
          simp

/-! ## reduction rules -/

theorem tir_false_mid {a b c : List Bool} (h : tir (a ++ b ++ c) = false) : tir b = false :=
  tir_false_of_append_right (x := a) (tir_false_of_append_left (y := c) (by simpa using h))

theorem sg_TT (B : List Bool) (h : tir (true :: true :: false :: B) = false) :
    sg (true :: true :: false :: B) = sg B ∧ tir B = false := by
  have h' : tir ([true, true] ++ false :: B) = false := by simpa using h
  have := sg_wall (x := [true, true]) (y := B) (Or.inl ⟨[], rfl⟩) h'
  rw [sg_of_count_false_eq_zero (s := [true, true]) rfl, Nat.zero_xor] at this
  exact ⟨by simpa using this, tir_false_of_append_right (x := [true, true, false]) (by simpa using h)⟩

theorem sg_nil : sg [] = 0 := sg_of_count_false_eq_zero rfl

theorem TT_right (ys : List ℕ) (q : ℕ) (hq : q = 0 → ys = [])
    (h : tir (true :: true :: (replicate q false ++ tl ys)) = false) :
    sg (true :: true :: (replicate q false ++ tl ys)) = sg (replicate (q - 1) false ++ tl ys) ∧
      tir (replicate (q - 1) false ++ tl ys) = false := by
  cases q with
  | zero =>
    obtain rfl := hq rfl
    simp only [replicate_zero, tl, nil_append, Nat.zero_sub]
    exact ⟨by rw [sg_of_count_false_eq_zero (s := [true, true]) rfl, sg_nil], rfl⟩
  | succ q =>
    simp only [replicate_succ, cons_append, Nat.add_sub_cancel] at h ⊢
    exact sg_TT _ h

/-- `[w X X v]`: the cells next to a pair of X's are dead -/
theorem rule_TT (xs ys : List ℕ) (p q : ℕ) (hp : p = 0 → xs = []) (hq : q = 0 → ys = [])
    (h : tir (ofGaps (xs ++ p :: 0 :: q :: ys)) = false) :
    sg (ofGaps (xs ++ p :: 0 :: q :: ys)) = sg (ofGaps (xs ++ [p - 1])) ^^^ sg (ofGaps ((q - 1) :: ys)) ∧
    tir (ofGaps (xs ++ [p - 1])) = false ∧ tir (ofGaps ((q - 1) :: ys)) = false := by
  have e : ofGaps (xs ++ p :: 0 :: q :: ys) =
      hd xs ++ replicate p false ++ true :: true :: (replicate q false ++ tl ys) := by
    rw [ofGaps_append _ _ (by simp)]; simp only [ofGaps_cons, tl_cons]; simp
  rw [e] at h ⊢
  rw [ofGaps_snoc, ofGaps_cons]
  have hR := tir_false_of_append_right (x := hd xs ++ replicate p false) (by simpa using h)
  obtain ⟨e2, t2⟩ := TT_right ys q hq hR
  cases p with
  | zero =>
    obtain rfl := hp rfl
    simp only [hd, replicate_zero, nil_append, Nat.zero_sub] at e2 ⊢
    exact ⟨by rw [e2, sg_nil, Nat.zero_xor], rfl, t2⟩
  | succ p =>
    have e3 : hd xs ++ replicate (p + 1) false ++ true :: true :: (replicate q false ++ tl ys) =
        (hd xs ++ replicate p false) ++ false :: (true :: true :: (replicate q false ++ tl ys)) := by
      simp [replicate_succ']
    rw [e3] at h ⊢
    rw [sg_wall (Or.inr (Or.inl ⟨_, rfl⟩)) h, e2]
    exact ⟨by simp, tir_false_of_append_left (y := false :: _) h, t2⟩

/-- Lemma 3.1 (3): `[w X 1 X v] = [w X] ⊕ [X v]` -/
theorem rule_one (xs ys : List ℕ) (p q : ℕ) (h : tir (ofGaps (xs ++ p :: 1 :: q :: ys)) = false) :
    sg (ofGaps (xs ++ p :: 1 :: q :: ys)) = sg (ofGaps (xs ++ [p, 0])) ^^^ sg (ofGaps (0 :: q :: ys)) ∧
    tir (ofGaps (xs ++ [p, 0])) = false ∧ tir (ofGaps (0 :: q :: ys)) = false := by
  have e : ofGaps (xs ++ p :: 1 :: q :: ys) = ofGaps (xs ++ [p, 0]) ++ false :: ofGaps (0 :: q :: ys) := by
    rw [ofGaps_append _ _ (by simp), show xs ++ [p, 0] = (xs ++ [p]) ++ [0] by simp, ofGaps_snoc,
      hd_append_single]
    (simp only [ofGaps_cons, tl_cons]; simp)
  have eL : ofGaps (xs ++ [p, 0]) = (hd xs ++ replicate p false) ++ [true] := by
    rw [show xs ++ [p, 0] = (xs ++ [p]) ++ [0] by simp, ofGaps_snoc, hd_append_single]; simp
  have eR : ofGaps (0 :: q :: ys) = true :: ofGaps (q :: ys) := by (simp only [ofGaps_cons, tl_cons]; simp)
  rw [e] at h ⊢
  have hD : Dead (ofGaps (xs ++ [p, 0])) (ofGaps (0 :: q :: ys)) :=
    Or.inr (Or.inr ⟨⟨_, eL⟩, ⟨_, eR⟩⟩)
  exact ⟨sg_wall hD h, tir_false_of_append_left (y := false :: _) h,
    tir_false_of_append_right (x := _ ++ [false]) (by simpa using h)⟩

/-- Lemma 3.3 (3): `[w X 4 X v] = [w X 2] ⊕ [2 X v]` -/
theorem rule_four (xs ys : List ℕ) (p q : ℕ) (h : tir (ofGaps (xs ++ p :: 4 :: q :: ys)) = false) :
    sg (ofGaps (xs ++ p :: 4 :: q :: ys)) = sg (ofGaps (xs ++ [p, 2])) ^^^ sg (ofGaps (2 :: q :: ys)) ∧
    tir (ofGaps (xs ++ [p, 2])) = false ∧ tir (ofGaps (2 :: q :: ys)) = false := by
  have eL : ofGaps (xs ++ [p, 2]) = (hd xs ++ replicate p false) ++ [true, false, false] := by
    rw [show xs ++ [p, 2] = (xs ++ [p]) ++ [2] by simp, ofGaps_snoc, hd_append_single]; simp
  have eR : ofGaps (2 :: q :: ys) = false :: false :: true :: ofGaps (q :: ys) := by
    (simp only [ofGaps_cons, tl_cons]; simp)
  have e : ofGaps (xs ++ p :: 4 :: q :: ys) = ofGaps (xs ++ [p, 2]) ++ ofGaps (2 :: q :: ys) := by
    rw [eL, eR, ofGaps_append _ _ (by simp)]; (simp only [ofGaps_cons, tl_cons]; simp)
  rw [e] at h ⊢
  have hx := tir_false_of_append_left h
  have hy := tir_false_of_append_right h
  exact ⟨sg_guard (Or.inl ⟨Or.inl ⟨_, _, _, eL⟩, ⟨_, _, _, eR⟩⟩) hx hy, hx, hy⟩

/-- Lemma 3.3 (1): `[X 2 X w] = [2 X w]` -/
theorem rule_x2x_left (c : ℕ) (ys : List ℕ) (h : tir (ofGaps (0 :: 2 :: c :: ys)) = false) :
    sg (ofGaps (0 :: 2 :: c :: ys)) = sg (ofGaps (2 :: c :: ys)) ∧ tir (ofGaps (2 :: c :: ys)) = false := by
  have eR : ofGaps (2 :: c :: ys) = false :: false :: true :: ofGaps (c :: ys) := by
    (simp only [ofGaps_cons, tl_cons]; simp)
  have e : ofGaps (0 :: 2 :: c :: ys) = [true] ++ ofGaps (2 :: c :: ys) := by
    (simp only [ofGaps_cons, tl_cons]; simp)
  rw [e] at h ⊢
  have hy := tir_false_of_append_right h
  rw [sg_guard (Or.inl ⟨Or.inr rfl, ⟨_, _, _, eR⟩⟩) rfl hy,
    sg_of_count_false_eq_zero (s := [true]) rfl, Nat.zero_xor]
  exact ⟨rfl, hy⟩

/-- Lemma 3.3 (2): `[w X 2 X] = [w X 2]` -/
theorem rule_x2x_right (ys : List ℕ) (c : ℕ) (h : tir (ofGaps (ys ++ [c, 2, 0])) = false) :
    sg (ofGaps (ys ++ [c, 2, 0])) = sg (ofGaps (ys ++ [c, 2])) ∧ tir (ofGaps (ys ++ [c, 2])) = false := by
  have eL : ofGaps (ys ++ [c, 2]) = (hd ys ++ replicate c false) ++ [true, false, false] := by
    rw [show ys ++ [c, 2] = (ys ++ [c]) ++ [2] by simp, ofGaps_snoc, hd_append_single]; simp
  have e : ofGaps (ys ++ [c, 2, 0]) = ofGaps (ys ++ [c, 2]) ++ [true] := by
    rw [show ys ++ [c, 2, 0] = (ys ++ [c, 2]) ++ [0] by simp, ofGaps_snoc, hd_of_ne (by simp)]; simp
  rw [e] at h ⊢
  have hx := tir_false_of_append_left h
  rw [sg_guard (Or.inr ⟨⟨_, _, _, eL⟩, rfl⟩) hx rfl,
    sg_of_count_false_eq_zero (s := [true]) rfl, Nat.xor_zero]
  exact ⟨rfl, hx⟩

end ITB
```

### `TBCheck.lean`

```lean
/-
Inverse Treblecross (MathDB 374250): the abstract certificate checker.

Positions are gap lists `[g0, g1, ..., gk]`: `g0` empty cells, a piece, `g1` empty cells, a piece, ...
A gap is described by knowledge `K`: `e n` (exactly `n`) or `g m r` (at least `m`, and `≡ r` mod 10).
Everything here is computation; soundness is proved in later modules.
-/

namespace ITB

inductive K where
  | e (n : Nat)
  | g (m r : Nat)
deriving DecidableEq, Repr

inductive Info where
  | s (n : Nat)
  | b (r : Nat)
deriving DecidableEq, Repr

/-- least concrete value compatible with the knowledge (for `g m r` with `r < 10`) -/
def K.low : K → Nat
  | .e n => n
  | .g m r => m + (r + 10 - m % 10) % 10

def info : K → Option Info
  | .e n => if n < 5 then some (.s n) else some (.b (n % 10))
  | .g m r => if 5 ≤ m + (r + 10 - m % 10) % 10 then some (.b r) else none

/-- is the gap equal to `c` (`c ≤ 4`)? -/
def aeq (k : K) (c : Nat) : Option Bool :=
  match k with
  | .e n => some (n == c)
  | .g m r => if c < m || c % 10 != r then some false else none

def apred : K → K
  | .e n => .e (n - 1)
  | .g m r => .g (m - 1) ((r + 9) % 10)

/-- threshold for the middle splits of a large gap -/
def thrA : Nat := 7

def splitsAll : K → List (K × K)
  | .e n => (List.range n).map fun j => (.e j, .e (n - 1 - j))
  | .g m r =>
      ((List.range thrA).flatMap fun j =>
        [(.e j, .g (m - 1 - j) ((r + 9 * (j + 1)) % 10)), (.g (m - 1 - j) ((r + 9 * (j + 1)) % 10), .e j)]) ++
      (List.range 10).map fun s => (.g thrA s, .g thrA ((r + 9 * (s + 1)) % 10))

def splitsSure (L : Nat) : K → List (K × K)
  | .e n => (List.range n).filterMap fun j =>
      if j < L || n - 1 - j < L then some (.e j, .e (n - 1 - j)) else none
  | .g m r => (List.range (min m L)).flatMap fun j =>
      [(.e j, .g (m - 1 - j) ((r + 9 * (j + 1)) % 10)), (.g (m - 1 - j) ((r + 9 * (j + 1)) % 10), .e j)]

/-- `p` holds for some move: gap `k` of the list replaced by a pair from `f k`. `pre` is reversed. -/
def anyMv (f : K → List (K × K)) (p : List K → Bool) : List K → List K → Bool
  | _, [] => false
  | pre, k :: rest => (f k).any (fun ab => p (pre.reverseAux (ab.1 :: ab.2 :: rest))) || anyMv f p (k :: pre) rest

def allMv (f : K → List (K × K)) (p : List K → Bool) : List K → List K → Bool
  | _, [] => true
  | pre, k :: rest => (f k).all (fun ab => p (pre.reverseAux (ab.1 :: ab.2 :: rest))) && allMv f p (k :: pre) rest

/-- no two consecutive internal zero gaps; input is the list without its first gap -/
def noZZ : List K → Option Bool
  | a :: b :: c :: t =>
      match aeq a 0, aeq b 0 with
      | some true, some true => some false
      | some false, _ => noZZ (b :: c :: t)
      | _, some false => noZZ (b :: c :: t)
      | _, _ => match noZZ (b :: c :: t) with
        | some false => some false
        | _ => none
  | _ => some true

def legal : List K → Option Bool
  | [] => some true
  | _ :: t => noZZ t

inductive Act where
  | done
  | one (l : List K)
  | two (l r : List K)

/-- scan the internal gaps; `pre` is the reversed prefix (head = gap before `g`) -/
def scan : List K → List K → Option Act
  | pre, g :: h :: t =>
      match aeq g 0 with
      | some true =>
          match pre with
          | p :: pre' =>
              match aeq p 0, aeq h 0 with
              | some pz, some qz =>
                  if (pz && !pre'.isEmpty) || (qz && !t.isEmpty) then none
                  else some (.two ((apred p :: pre').reverse) (apred h :: t))
              | _, _ => none
          | [] => none
      | some false =>
          match aeq g 1 with
          | some true => some (.two ((K.e 0 :: pre).reverse) (K.e 0 :: h :: t))
          | some false =>
              match aeq g 4 with
              | some true => some (.two ((K.e 2 :: pre).reverse) (K.e 2 :: h :: t))
              | some false => scan (g :: pre) (h :: t)
              | none => none
          | none => none
      | none => none
  | _, _ => some .done

/-- `[0, 2, _, ...]`: a piece at the edge followed by a gap of two and another piece -/
def edge02 : List K → Option Bool
  | a :: b :: _ :: _ =>
      match aeq a 0, aeq b 2 with
      | some x, some y => some (x && y)
      | _, _ => none
  | _ => some false

def step (gs : List K) : Option Act :=
  match gs with
  | [] => some .done
  | g0 :: t =>
      match scan [g0] t with
      | some .done =>
          match edge02 gs with
          | some true => some (.one t)
          | some false =>
              match edge02 gs.reverse with
              | some true => some (.one gs.reverse.tail.reverse)
              | some false => some .done
              | none => none
          | none => none
      | r => r

def red : Nat → List K → Option (List (List K))
  | 0, _ => none
  | n + 1, gs =>
      match step gs with
      | some .done => some [gs]
      | some (.one l) => red n l
      | some (.two l r) =>
          match red n l, red n r with
          | some a, some b => some (a ++ b)
          | _, _ => none
      | none => none

/-! Value function on information lists. Residue tables (index = residue mod 10):
`c1bit r = (1 - χ1 r)/2`, `z0 r ↔ χ2 r = 0`, `c2bit r = (1 - χ2 r)/2` when `χ2 r ≠ 0`,
`sgbit z = (1 - σ z)/2` with `σ = -1` on `{1,4}` and `+1` on `{6,9}`. -/

def c1bit (r : Nat) : Nat :=
  match r with
  | 1 => 1 | 4 => 1 | 5 => 1 | 7 => 1 | 8 => 1 | _ => 0

def z0 (r : Nat) : Bool :=
  match r with
  | 1 => true | 4 => true | 6 => true | 9 => true | _ => false

def c2bit (r : Nat) : Nat :=
  match r with
  | 2 => 1 | 5 => 1 | 8 => 1 | _ => 0

def sgbit (r : Nat) : Nat :=
  match r with
  | 1 => 1 | 4 => 1 | _ => 0

def Info.res : Info → Nat
  | .s n => n % 10
  | .b r => r

def Info.isZ : Info → Bool
  | .s n => n == 0
  | .b _ => false

/-- the gap is at least `c` (`c ≤ 5`) -/
def Info.ge (i : Info) (c : Nat) : Bool :=
  match i with
  | .s n => c ≤ n
  | .b _ => true

def Info.isS (i : Info) (c : Nat) : Bool :=
  match i with
  | .s n => n == c
  | .b _ => false

def val1 (ia ib : Info) : Option Nat :=
  let ra := ia.res
  let rb := ib.res
  if !z0 ra && !z0 rb then some (c2bit ra ^^^ c2bit rb)
  else if (ia.isZ && rb == 6) || (ib.isZ && ra == 6) then some 0
  else if (ia.isZ && rb == 1) || (ib.isZ && ra == 1) then some 1
  else if z0 ra != z0 rb then
    if z0 ra then some (2 + (sgbit ra ^^^ c2bit rb)) else some (2 + (sgbit rb ^^^ c2bit ra))
  else if (ia.isS 1 || ia.isS 4) && (ib.isS 1 || ib.isS 4) then some 1
  else none

def valE (ic id : Info) : Option Nat :=
  if ic.ge 2 && !z0 ic.res && id.ge 3 && (id.res == 3 || id.res == 8) then
    some ((if id.res == 3 then 2 else 3) ^^^ c2bit ic.res)
  else none

def val2 (i0 i1 i2 : Info) : Option Nat :=
  let x : Option Nat :=
    if i0.isZ && i2.isZ then
      if i1.res == 4 then some 0
      else if i1.res == 9 then some 1
      else if i1.isS 3 then some 2
      else none
    else none
  match x with
  | some v => some v
  | none =>
    match (if i2.isZ then valE i0 i1 else none) with
    | some v => some v
    | none => if i0.isZ then valE i2 i1 else none

def fvalI : List Info → Option Nat
  | [i] => some (c1bit i.res)
  | [ia, ib] => val1 ia ib
  | [i0, i1, i2] => val2 i0 i1 i2
  | _ => none

def infos : List K → Option (List Info)
  | [] => some []
  | k :: ks =>
      match info k, infos ks with
      | some i, some is => some (i :: is)
      | _, _ => none

def fval (ks : List K) : Option Nat :=
  match infos ks with
  | some is => fvalI is
  | none => none

def fsum : List (List K) → Option Nat
  | [] => some 0
  | c :: cs =>
      match fval c, fsum cs with
      | some v, some w => some (v ^^^ w)
      | _, _ => none

def locL : Nat := 5

/-- value of a position after reducing it, when every component is a family member -/
def rval (q : List K) : Option Nat :=
  match red q.length q with
  | some cs => fsum cs
  | none => none

/-- reply search: some component `c` of the sum has a local move to a family sum of value `v` -/
def replyOk (v : Nat) : List (List K) → List (List K) → Bool
  | _, [] => false
  | pre, c :: rest =>
      (match fsum (pre ++ rest) with
       | some ov => anyMv (splitsSure locL) (fun r => legal r == some true && rval r == some (v ^^^ ov)) [] c
       | none => false) || replyOk v (pre ++ [c]) rest

def hasVal (u : Nat) (P : List K) : Bool :=
  anyMv (splitsSure 100) (fun q => legal q == some true && rval q == some u) [] P

def optOk (v : Nat) (q : List K) : Bool :=
  match legal q with
  | some false => true
  | none => false
  | some true =>
      match red q.length q with
      | none => false
      | some cs =>
          match fsum cs with
          | some w => w != v
          | none => replyOk v [] cs

def chkP (P : List K) : Bool :=
  match fval P with
  | none => true
  | some v => (List.range v).all (fun u => hasVal u P) && allMv splitsAll (optOk v) [] P

/-- both-Z0 boards: options of value 0 and 1 -/
def conjOk (P : List K) : Bool := hasVal 0 P && hasVal 1 P

/-! Canonical knowledge: exact below `thrM`, otherwise residue. -/
def thrM : Nat := 13

def canon (n : Nat) : K := if n < thrM then .e n else .g thrM (n % 10)

def ksAll : List K := (List.range thrM).map K.e ++ (List.range 10).map (K.g thrM)

end ITB
```

### `TBSound.lean`

```lean
import TBGaps
import TBCheck

/-!
# Soundness of the abstract checker

A gap `n` satisfies knowledge `e m` if `n = m`, and `g m r` if `m ≤ n` and `n ≡ r (mod 10)`.
Every abstract operation of `TBCheck` is proved sound for every concrete gap list satisfying the
knowledge. `thmA` derives the values of all family members from the certificate.
-/

set_option linter.unnecessarySeqFocus false

namespace ITB

open List

def sat (n : ℕ) : K → Prop
  | .e m => n = m
  | .g m r => m ≤ n ∧ n % 10 = r

def Sat : List ℕ → List K → Prop
  | [], [] => True
  | n :: ns, k :: ks => sat n k ∧ Sat ns ks
  | _, _ => False

def Sat2 : List (List ℕ) → List (List K) → Prop
  | [], [] => True
  | g :: gs, c :: cs => Sat g c ∧ Sat2 gs cs
  | _, _ => False

def ninfo (n : ℕ) : Info := if n < 5 then .s n else .b (n % 10)

/-- the family `F` and its claimed values -/
def cval (gs : List ℕ) : Option ℕ := fvalI (gs.map ninfo)

noncomputable def xsum : List (List ℕ) → ℕ
  | [] => 0
  | c :: cs => sg (ofGaps c) ^^^ xsum cs

def sumAll (gcs : List (List ℕ)) : ℕ := (gcs.map List.sum).sum

/-! ## lists of knowledge -/

theorem Sat.append : ∀ {a b : List ℕ} {c d : List K}, Sat a c → Sat b d → Sat (a ++ b) (c ++ d)
  | [], _, [], _, _, h => h
  | _ :: _, _, _ :: _, _, ⟨h1, h2⟩, h => ⟨h1, Sat.append h2 h⟩

theorem Sat.split : ∀ {gs : List ℕ} {xs ys : List K}, Sat gs (xs ++ ys) →
    ∃ ga gb, gs = ga ++ gb ∧ Sat ga xs ∧ Sat gb ys
  | gs, [], _, h => ⟨[], gs, rfl, trivial, h⟩
  | _ :: _, _ :: _, _, ⟨h1, h2⟩ => by
      obtain ⟨ga, gb, rfl, ha, hb⟩ := Sat.split h2
      exact ⟨_ :: ga, gb, rfl, ⟨h1, ha⟩, hb⟩
  | [], _ :: _, _, h => h.elim

theorem Sat.split_left : ∀ {ga gb : List ℕ} {ks : List K}, Sat (ga ++ gb) ks →
    ∃ ka kb, ks = ka ++ kb ∧ Sat ga ka ∧ Sat gb kb
  | [], _, ks, h => ⟨[], ks, rfl, trivial, h⟩
  | _ :: _, _, _ :: _, ⟨h1, h2⟩ => by
      obtain ⟨ka, kb, rfl, ha, hb⟩ := Sat.split_left h2
      exact ⟨_ :: ka, kb, rfl, ⟨h1, ha⟩, hb⟩
  | _ :: _, _, [], h => h.elim

theorem Sat.cons_left {g : ℕ} {gs : List ℕ} {ks : List K} (h : Sat (g :: gs) ks) :
    ∃ k ks', ks = k :: ks' ∧ sat g k ∧ Sat gs ks' := by
  cases ks with
  | nil => exact h.elim
  | cons k ks => exact ⟨k, ks, rfl, h.1, h.2⟩

theorem Sat.cons_right {k : K} {ks : List K} {gs : List ℕ} (h : Sat gs (k :: ks)) :
    ∃ g gs', gs = g :: gs' ∧ sat g k ∧ Sat gs' ks := by
  cases gs with
  | nil => exact h.elim
  | cons g gs => exact ⟨g, gs, rfl, h.1, h.2⟩

theorem Sat.nil_right {gs : List ℕ} (h : Sat gs []) : gs = [] := by
  cases gs with
  | nil => rfl
  | cons _ _ => exact h.elim

theorem Sat.reverse : ∀ {gs : List ℕ} {ks : List K}, Sat gs ks → Sat gs.reverse ks.reverse
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h1, h2⟩ => by
      simp only [List.reverse_cons]; exact Sat.append (Sat.reverse h2) ⟨h1, trivial⟩

theorem Sat2.append : ∀ {a b : List (List ℕ)} {c d : List (List K)}, Sat2 a c → Sat2 b d →
    Sat2 (a ++ b) (c ++ d)
  | [], _, [], _, _, h => h
  | _ :: _, _, _ :: _, _, ⟨h1, h2⟩, h => ⟨h1, Sat2.append h2 h⟩

theorem Sat2.split : ∀ {gs : List (List ℕ)} {xs ys : List (List K)}, Sat2 gs (xs ++ ys) →
    ∃ ga gb, gs = ga ++ gb ∧ Sat2 ga xs ∧ Sat2 gb ys
  | gs, [], _, h => ⟨[], gs, rfl, trivial, h⟩
  | _ :: _, _ :: _, _, ⟨h1, h2⟩ => by
      obtain ⟨ga, gb, rfl, ha, hb⟩ := Sat2.split h2
      exact ⟨_ :: ga, gb, rfl, ⟨h1, ha⟩, hb⟩
  | [], _ :: _, _, h => h.elim

theorem xsum_append : ∀ a b : List (List ℕ), xsum (a ++ b) = xsum a ^^^ xsum b
  | [], b => by simp [xsum]
  | c :: a, b => by simp [xsum, xsum_append a b, Nat.xor_assoc]

theorem sumAll_append (a b : List (List ℕ)) : sumAll (a ++ b) = sumAll a + sumAll b := by
  simp [sumAll]

theorem Sat.cons {g : ℕ} {k : K} {gs : List ℕ} {ks : List K} (h : sat g k) (hs : Sat gs ks) :
    Sat (g :: gs) (k :: ks) := ⟨h, hs⟩

/-! ## primitive operations -/

theorem info_sound {n : ℕ} {k : K} {i : Info} (hs : sat n k) (h : info k = some i) : ninfo n = i := by
  cases k with
  | e m =>
    simp only [sat] at hs; subst hs
    simp only [info, ninfo] at h ⊢
    split_ifs at h ⊢ <;> simp_all
  | g m r =>
    simp only [sat] at hs
    simp only [info] at h
    split_ifs at h with h5
    cases h
    simp only [ninfo, show ¬ n < 5 by omega, ↓reduceIte, hs.2]

theorem aeq_true {n c : ℕ} {k : K} (hs : sat n k) (h : aeq k c = some true) : n = c := by
  cases k with
  | e m => simp only [sat] at hs; subst hs; simpa [aeq] using h
  | g m r => simp only [aeq] at h; split_ifs at h <;> simp at h

theorem aeq_false {n c : ℕ} {k : K} (hs : sat n k) (h : aeq k c = some false) : n ≠ c := by
  cases k with
  | e m => simp only [sat] at hs; subst hs; simpa [aeq] using h
  | g m r =>
    simp only [sat] at hs
    simp only [aeq] at h
    split_ifs at h with h1
    simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h1
    omega

theorem aeq_eq_true_iff {n c : ℕ} {k : K} {b : Bool} (hs : sat n k) (h : aeq k c = some b) :
    n = c ↔ b = true := by
  cases b
  · simp [aeq_false hs h]
  · simp [aeq_true hs h]

theorem aeq_true_e {k : K} {c : ℕ} (h : aeq k c = some true) : k = .e c := by
  cases k with
  | e m => simp [aeq] at h; rw [h]
  | g m r => simp only [aeq] at h; split_ifs at h <;> simp at h

theorem apred_sound {n : ℕ} {k : K} (hs : sat n k) (h : 1 ≤ n ∨ aeq k 0 = some true) :
    sat (n - 1) (apred k) := by
  cases k with
  | e m => simp only [sat] at hs; subst hs; simp [apred, sat]
  | g m r =>
    rcases h with h | h
    · simp only [sat] at hs; simp only [apred, sat]; omega
    · simp only [aeq] at h; split_ifs at h <;> simp at h

theorem splitsAll_complete {g j k' : ℕ} {k : K} (hs : sat g k) (hg : g = j + 1 + k') :
    ∃ ab ∈ splitsAll k, sat j ab.1 ∧ sat k' ab.2 := by
  cases k with
  | e n =>
    simp only [sat] at hs; subst hs
    refine ⟨(.e j, .e (j + 1 + k' - 1 - j)), ?_, rfl, by simp only [sat]; omega⟩
    rw [hg]
    simp only [splitsAll, List.mem_map, List.mem_range]
    exact ⟨j, by omega, rfl⟩
  | g m r =>
    simp only [sat] at hs
    by_cases hj : j < 7
    · refine ⟨(.e j, .g (m - 1 - j) ((r + 9 * (j + 1)) % 10)), ?_, rfl, ?_⟩
      · simp only [splitsAll, thrA, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
        exact Or.inl ⟨j, hj, Or.inl rfl⟩
      · simp only [sat]; omega
    · by_cases hk : k' < 7
      · refine ⟨(.g (m - 1 - k') ((r + 9 * (k' + 1)) % 10), .e k'), ?_, ?_, rfl⟩
        · simp only [splitsAll, thrA, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
          exact Or.inl ⟨k', hk, Or.inr (Or.inl rfl)⟩
        · simp only [sat]; omega
      · refine ⟨(.g thrA (j % 10), .g thrA ((r + 9 * (j % 10 + 1)) % 10)), ?_, ?_, ?_⟩
        · simp only [splitsAll, List.mem_append, List.mem_map, List.mem_range]
          exact Or.inr ⟨j % 10, by omega, rfl⟩
        · show 7 ≤ j ∧ j % 10 = j % 10
          omega
        · show 7 ≤ k' ∧ k' % 10 = (r + 9 * (j % 10 + 1)) % 10
          omega

theorem splitsSure_sound {g L : ℕ} {k : K} {ab : K × K} (hs : sat g k) (h : ab ∈ splitsSure L k) :
    ∃ j k', g = j + 1 + k' ∧ sat j ab.1 ∧ sat k' ab.2 := by
  cases k with
  | e n =>
    simp only [sat] at hs; subst hs
    simp only [splitsSure, List.mem_filterMap, List.mem_range] at h
    obtain ⟨j, hj, h⟩ := h
    split_ifs at h
    cases h
    exact ⟨j, g - 1 - j, by omega, rfl, rfl⟩
  | g m r =>
    simp only [sat] at hs
    simp only [splitsSure, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at h
    obtain ⟨j, hj, h | h⟩ := h
    · subst h
      exact ⟨j, g - 1 - j, by omega, rfl, by simp only [sat]; omega⟩
    · subst h
      exact ⟨g - 1 - j, j, by omega, by simp only [sat]; omega, rfl⟩

theorem noZZ_sound : ∀ (ks : List K) (gs : List ℕ), Sat gs ks → ∀ b, noZZ ks = some b → (cz gs ↔ b = false)
  | a :: b :: c :: t, ga :: gb :: gc :: gt, ⟨ha, hb, hc, ht⟩, v, h => by
    have ih := noZZ_sound (b :: c :: t) (gb :: gc :: gt) ⟨hb, hc, ht⟩
    simp only [cz]
    simp only [noZZ] at h
    cases h1 : aeq a 0 with
    | none =>
      cases h2 : aeq b 0 with
      | none =>
        rw [h1, h2] at h; simp only at h
        cases h3 : noZZ (b :: c :: t) with
        | none => rw [h3] at h; simp at h
        | some w =>
          rw [h3] at h
          cases w with
          | true => simp at h
          | false =>
            simp at h; subst h
            have := (ih false h3).mpr rfl; simp [this]
      | some y =>
        cases y with
        | false =>
          rw [h1, h2] at h; simp only at h
          rw [← ih v h]; have := aeq_false hb h2; simp [this]
        | true =>
          rw [h1, h2] at h; simp only at h
          cases h3 : noZZ (b :: c :: t) with
          | none => rw [h3] at h; simp at h
          | some w =>
            rw [h3] at h
            cases w with
            | true => simp at h
            | false =>
              simp at h; subst h
              have := (ih false h3).mpr rfl; simp [this]
    | some x =>
      cases x with
      | false =>
        rw [h1] at h; simp only at h
        rw [← ih v h]; have := aeq_false ha h1; simp [this]
      | true =>
        cases h2 : aeq b 0 with
        | none =>
          rw [h1, h2] at h; simp only at h
          cases h3 : noZZ (b :: c :: t) with
          | none => rw [h3] at h; simp at h
          | some w =>
            rw [h3] at h
            cases w with
            | true => simp at h
            | false =>
              simp at h; subst h
              have := (ih false h3).mpr rfl; simp [this]
        | some y =>
          cases y with
          | false =>
            rw [h1, h2] at h; simp only at h
            rw [← ih v h]; have := aeq_false hb h2; simp [this]
          | true =>
            rw [h1, h2] at h; simp only at h
            cases h; simp [aeq_true ha h1, aeq_true hb h2]
  | [], gs, hs, v, h => by simp [noZZ] at h; subst h; rw [Sat.nil_right hs]; simp [cz]
  | [_], gs, hs, v, h => by
    simp [noZZ] at h; subst h
    obtain ⟨g, gs', rfl, -, h2⟩ := Sat.cons_right hs
    rw [Sat.nil_right h2]; simp [cz]
  | [_, _], gs, hs, v, h => by
    simp [noZZ] at h; subst h
    obtain ⟨g, gs', rfl, -, h2⟩ := Sat.cons_right hs
    obtain ⟨g', gs'', rfl, -, h3⟩ := Sat.cons_right h2
    rw [Sat.nil_right h3]; simp [cz]
  | _ :: _ :: _ :: _, [], hs, _, _ => hs.elim
  | _ :: _ :: _ :: _, [_], hs, _, _ => hs.2.elim
  | _ :: _ :: _ :: _, [_, _], hs, _, _ => hs.2.2.elim

theorem legal_sound {gs : List ℕ} {ks : List K} {b : Bool} (hs : Sat gs ks) (h : legal ks = some b) :
    tir (ofGaps gs) = !b := by
  cases ks with
  | nil =>
    rw [Sat.nil_right hs]; simp [legal] at h; subst h; rfl
  | cons k ks =>
    obtain ⟨g, gs', rfl, -, h2⟩ := Sat.cons_right hs
    simp only [legal] at h
    have e := noZZ_sound ks gs' h2 b h
    have t := tir_ofGaps g gs'
    cases b <;> cases hb : tir (ofGaps (g :: gs')) <;> simp_all

/-! ## move enumeration -/

theorem allMv_spec (f : K → List (K × K)) (p : List K → Bool) : ∀ (ks pre : List K),
    allMv f p pre ks = true → ∀ xs k ys, ks = xs ++ k :: ys → ∀ ab ∈ f k,
      p (pre.reverse ++ xs ++ ab.1 :: ab.2 :: ys) = true
  | [], _, _, xs, k, ys, e, _, _ => by simp at e
  | k0 :: rest, pre, h, xs, k, ys, e, ab, hab => by
    simp only [allMv, Bool.and_eq_true, List.all_eq_true] at h
    cases xs with
    | nil =>
      simp at e; obtain ⟨rfl, rfl⟩ := e
      have := h.1 ab hab
      rw [List.reverseAux_eq] at this
      simpa using this
    | cons x xs =>
      simp at e; obtain ⟨rfl, rfl⟩ := e
      have := allMv_spec f p _ (k0 :: pre) h.2 xs k ys rfl ab hab
      simpa using this

theorem anyMv_spec (f : K → List (K × K)) (p : List K → Bool) : ∀ (ks pre : List K),
    anyMv f p pre ks = true → ∃ xs k ys, ∃ ab ∈ f k, ks = xs ++ k :: ys ∧
      p (pre.reverse ++ xs ++ ab.1 :: ab.2 :: ys) = true
  | [], _, h => by simp [anyMv] at h
  | k0 :: rest, pre, h => by
    simp only [anyMv, Bool.or_eq_true, List.any_eq_true] at h
    rcases h with ⟨ab, hab, h⟩ | h
    · refine ⟨[], k0, rest, ab, hab, rfl, ?_⟩
      rw [List.reverseAux_eq] at h; simpa using h
    · obtain ⟨xs, k, ys, ab, hab, rfl, h'⟩ := anyMv_spec f p rest (k0 :: pre) h
      exact ⟨k0 :: xs, k, ys, ab, hab, rfl, by simpa using h'⟩

/-- a "sure" abstract move is realized by a concrete move -/
theorem sure_move {L : ℕ} {p : List K → Bool} {gs : List ℕ} {ks : List K} (hS : Sat gs ks)
    (h : anyMv (splitsSure L) p [] ks = true) :
    ∃ q gq, p q = true ∧ Sat gq q ∧ gq.sum + 1 = gs.sum ∧
      ∃ A B, ofGaps gs = A ++ false :: B ∧ ofGaps gq = A ++ true :: B := by
  obtain ⟨xs, k, ys, ab, hab, rfl, hp⟩ := anyMv_spec _ p ks [] h
  obtain ⟨ga, gb, rfl, ha, hb⟩ := Sat.split hS
  obtain ⟨g, gys, rfl, hg, hys⟩ := Sat.cons_right hb
  obtain ⟨j, k', rfl, h1, h2⟩ := splitsSure_sound hg hab
  obtain ⟨e1, e2⟩ := split_ofGaps ga gys j k'
  refine ⟨_, ga ++ j :: k' :: gys, by simpa using hp, Sat.append ha (Sat.cons h1 (Sat.cons h2 hys)), ?_, _, _, e1, e2⟩
  simp [List.sum_append]; omega

theorem replyOk_spec (v : ℕ) : ∀ (l pre : List (List K)), replyOk v pre l = true →
    ∃ a c b ov, l = a ++ c :: b ∧ fsum (pre ++ a ++ b) = some ov ∧
      anyMv (splitsSure locL) (fun r => legal r == some true && rval r == some (v ^^^ ov)) [] c = true
  | [], _, h => by simp [replyOk] at h
  | c :: rest, pre, h => by
    simp only [replyOk, Bool.or_eq_true] at h
    rcases h with h | h
    · cases hf : fsum (pre ++ rest) with
      | none => rw [hf] at h; simp at h
      | some ov => rw [hf] at h; exact ⟨[], c, rest, ov, rfl, by simpa using hf, h⟩
    · obtain ⟨a, c', b, ov, rfl, hf, h⟩ := replyOk_spec v rest (pre ++ [c]) h
      exact ⟨c :: a, c', b, ov, rfl, by simpa using hf, h⟩

/-! ## the reducer -/

def ActOK (gs : List ℕ) : Act → Prop
  | .done => True
  | .one l => ∃ gl, Sat gl l ∧ sg (ofGaps gs) = sg (ofGaps gl) ∧ tir (ofGaps gl) = false ∧
      gl.sum ≤ gs.sum
  | .two l r => ∃ gl gr, Sat gl l ∧ Sat gr r ∧ sg (ofGaps gs) = sg (ofGaps gl) ^^^ sg (ofGaps gr) ∧
      tir (ofGaps gl) = false ∧ tir (ofGaps gr) = false ∧ gl.sum + gr.sum ≤ gs.sum

theorem scan_sound : ∀ (rest pre : List K) (grest gpre : List ℕ) (act : Act),
    scan pre rest = some act → pre ≠ [] → Sat gpre pre → Sat grest rest →
    tir (ofGaps (gpre.reverse ++ grest)) = false → ActOK (gpre.reverse ++ grest) act
  | g :: h :: t, pre, grest, gpre, act, hsc, hpre, hSp, hSr, htir => by
    obtain ⟨g', grest1, rfl, hg, hr1⟩ := Sat.cons_right hSr
    obtain ⟨h', t', rfl, hh, ht⟩ := Sat.cons_right hr1
    obtain ⟨p, pre', rfl⟩ := List.exists_cons_of_ne_nil hpre
    obtain ⟨p', gpre', rfl, hp, hpre'⟩ := Sat.cons_right hSp
    have eq0 : (p' :: gpre').reverse ++ g' :: h' :: t' = gpre'.reverse ++ p' :: g' :: h' :: t' := by simp
    simp only [scan] at hsc
    cases hz : aeq g 0 with
    | none => rw [hz] at hsc; simp at hsc
    | some z =>
      cases z with
      | true =>
        rw [hz] at hsc
        have hg0 := aeq_true hg hz; subst hg0
        cases hpz : aeq p 0 with
        | none => rw [hpz] at hsc; simp at hsc
        | some pz =>
          cases hqz : aeq h 0 with
          | none => rw [hpz, hqz] at hsc; simp at hsc
          | some qz =>
            rw [hpz, hqz] at hsc
            simp only at hsc
            split_ifs at hsc with hc
            cases hsc
            simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
              not_or, not_and] at hc
            rw [eq0] at htir ⊢
            have hp0 : p' = 0 → gpre'.reverse = [] := by
              intro e
              have := (aeq_eq_true_iff hp hpz).mp e
              have := hc.1 this
              simp only [ne_eq, not_not] at this
              subst this; rw [Sat.nil_right hpre']; rfl
            have hq0 : h' = 0 → t' = [] := by
              intro e
              have := (aeq_eq_true_iff hh hqz).mp e
              have := hc.2 this
              simp only [ne_eq, not_not] at this
              subst this; exact Sat.nil_right ht
            obtain ⟨e1, t1, t2⟩ := rule_TT gpre'.reverse t' p' h' hp0 hq0 htir
            refine ⟨gpre'.reverse ++ [p' - 1], (h' - 1) :: t', ?_, ?_, e1, t1, t2, ?_⟩
            · simp only [List.reverse_cons]
              refine Sat.append (Sat.reverse hpre') ⟨apred_sound hp ?_, trivial⟩
              cases pz
              · exact Or.inl (by have := aeq_false hp hpz; omega)
              · exact Or.inr hpz
            · refine ⟨apred_sound hh ?_, ht⟩
              cases qz
              · exact Or.inl (by have := aeq_false hh hqz; omega)
              · exact Or.inr hqz
            · simp [List.sum_append]; omega
      | false =>
        rw [hz] at hsc
        have hg0 := aeq_false hg hz
        cases ho : aeq g 1 with
        | none => rw [ho] at hsc; simp at hsc
        | some o =>
          cases o with
          | true =>
            rw [ho] at hsc; simp only at hsc; cases hsc
            have hg1 := aeq_true hg ho; subst hg1
            rw [eq0] at htir ⊢
            obtain ⟨e1, t1, t2⟩ := rule_one gpre'.reverse t' p' h' htir
            refine ⟨gpre'.reverse ++ [p', 0], 0 :: h' :: t', ?_, ⟨rfl, hh, ht⟩, e1, t1, t2, ?_⟩
            · simp only [List.reverse_cons]
              have := Sat.append (Sat.reverse hpre') (show Sat [p', 0] [p, K.e 0] from ⟨hp, rfl, trivial⟩)
              simpa using this
            · simp [List.sum_append]; omega
          | false =>
            rw [ho] at hsc
            have hg1 := aeq_false hg ho
            cases hf : aeq g 4 with
            | none => rw [hf] at hsc; simp at hsc
            | some f =>
              cases f with
              | true =>
                rw [hf] at hsc; simp only at hsc; cases hsc
                have hg4 := aeq_true hg hf; subst hg4
                rw [eq0] at htir ⊢
                obtain ⟨e1, t1, t2⟩ := rule_four gpre'.reverse t' p' h' htir
                refine ⟨gpre'.reverse ++ [p', 2], 2 :: h' :: t', ?_, ⟨rfl, hh, ht⟩, e1, t1, t2, ?_⟩
                · simp only [List.reverse_cons]
                  have := Sat.append (Sat.reverse hpre') (show Sat [p', 2] [p, K.e 2] from ⟨hp, rfl, trivial⟩)
                  simpa using this
                · simp [List.sum_append]; omega
              | false =>
                rw [hf] at hsc
                have := scan_sound (h :: t) (g :: p :: pre') (h' :: t') (g' :: p' :: gpre') act hsc
                  (by simp) ⟨hg, hp, hpre'⟩ ⟨hh, ht⟩ (by simpa using htir)
                simpa using this
  | [], pre, grest, gpre, act, hsc, _, _, hSr, _ => by
    simp [scan] at hsc; subst hsc; trivial
  | [_], pre, grest, gpre, act, hsc, _, _, hSr, _ => by
    simp [scan] at hsc; subst hsc; trivial

theorem edge02_true {ks : List K} {gs : List ℕ} (hs : Sat gs ks) (h : edge02 ks = some true) :
    ∃ c gt, gs = 0 :: 2 :: c :: gt ∧ Sat (2 :: c :: gt) ks.tail := by
  match ks, h with
  | a :: b :: c :: t, h =>
    simp only [edge02] at h
    cases h1 : aeq a 0 with
    | none => rw [h1] at h; simp at h
    | some x =>
      cases h2 : aeq b 2 with
      | none => rw [h1, h2] at h; simp at h
      | some y =>
        rw [h1, h2] at h; simp at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ga, gs1, rfl, ha, h1'⟩ := Sat.cons_right hs
        obtain ⟨gb, gs2, rfl, hb, h2'⟩ := Sat.cons_right h1'
        obtain ⟨gc, gt, rfl, hc, h3'⟩ := Sat.cons_right h2'
        rw [aeq_true ha h1, aeq_true hb h2] at *
        exact ⟨gc, gt, rfl, hb, hc, h3'⟩

theorem step_sound (ks : List K) (gs : List ℕ) (act : Act) (h : step ks = some act) (hs : Sat gs ks)
    (htir : tir (ofGaps gs) = false) : ActOK gs act := by
  cases ks with
  | nil => simp [step] at h; subst h; trivial
  | cons g0 t =>
    obtain ⟨g0', gt, rfl, hg0, hgt⟩ := Sat.cons_right hs
    have hscan := scan_sound t [g0] gt [g0']
    simp only [List.reverse_singleton, List.singleton_append] at hscan
    simp only [step] at h
    cases hsc : scan [g0] t with
    | none => rw [hsc] at h; simp at h
    | some a =>
      rw [hsc] at h
      cases a with
      | one l => simp at h; subst h; exact hscan _ hsc (by simp) ⟨hg0, trivial⟩ hgt htir
      | two l r => simp at h; subst h; exact hscan _ hsc (by simp) ⟨hg0, trivial⟩ hgt htir
      | done =>
        simp only at h
        cases he : edge02 (g0 :: t) with
        | none => rw [he] at h; simp at h
        | some x =>
          cases x with
          | true =>
            rw [he] at h; simp at h; subst h
            obtain ⟨c, gt', e, hS⟩ := edge02_true hs he
            rw [e] at htir ⊢
            obtain ⟨e1, t1⟩ := rule_x2x_left c gt' htir
            exact ⟨_, hS, e1, t1, by simp⟩
          | false =>
            rw [he] at h; simp only at h
            cases he' : edge02 (g0 :: t).reverse with
            | none => rw [he'] at h; simp at h
            | some y =>
              cases y with
              | false => rw [he'] at h; simp at h; subst h; trivial
              | true =>
                rw [he'] at h; simp at h; subst h
                obtain ⟨c, gt', e, hS⟩ := edge02_true (Sat.reverse hs) he'
                have e2 : g0' :: gt = gt'.reverse ++ [c, 2, 0] := by
                  rw [← List.reverse_reverse (g0' :: gt), e]; simp
                rw [e2] at htir ⊢
                obtain ⟨e1, t1⟩ := rule_x2x_right gt'.reverse c htir
                refine ⟨_, ?_, e1, t1, by simp [List.sum_append]⟩
                have := Sat.reverse hS
                simpa using this

theorem red_sound : ∀ (n : ℕ) (ks : List K) (cs : List (List K)) (gs : List ℕ),
    red n ks = some cs → Sat gs ks → tir (ofGaps gs) = false →
    ∃ gcs, Sat2 gcs cs ∧ sg (ofGaps gs) = xsum gcs ∧ sumAll gcs ≤ gs.sum
  | 0, _, _, _, h, _, _ => by simp [red] at h
  | n + 1, ks, cs, gs, h, hs, htir => by
    simp only [red] at h
    cases hst : step ks with
    | none => rw [hst] at h; simp at h
    | some act =>
      rw [hst] at h
      have hA := step_sound ks gs act hst hs htir
      cases act with
      | done =>
        simp only at h; cases h
        exact ⟨[gs], ⟨hs, trivial⟩, by simp [xsum], by simp [sumAll]⟩
      | one l =>
        simp only at h
        obtain ⟨gl, hSl, e, tl', hsum⟩ := hA
        obtain ⟨gcs, h1, h2, h3⟩ := red_sound n l cs gl h hSl tl'
        exact ⟨gcs, h1, by rw [e, h2], by omega⟩
      | two l r =>
        simp only at h
        obtain ⟨gl, gr, hSl, hSr, e, tl', tr', hsum⟩ := hA
        cases hl : red n l with
        | none => rw [hl] at h; simp at h
        | some a =>
          cases hr : red n r with
          | none => rw [hl, hr] at h; simp at h
          | some b =>
            rw [hl, hr] at h; simp at h; subst h
            obtain ⟨ga, h1, h2, h3⟩ := red_sound n l a gl hl hSl tl'
            obtain ⟨gb, h1', h2', h3'⟩ := red_sound n r b gr hr hSr tr'
            refine ⟨ga ++ gb, Sat2.append h1 h1', by rw [e, h2, h2', xsum_append], ?_⟩
            rw [sumAll_append]; omega

/-! ## values -/

theorem infos_sound : ∀ {gs : List ℕ} {ks : List K} {is : List Info}, Sat gs ks →
    infos ks = some is → gs.map ninfo = is
  | [], [], is, _, h => by simp [infos] at h; subst h; rfl
  | g :: gs, k :: ks, is, ⟨h1, h2⟩, h => by
    simp only [infos] at h
    cases hi : info k with
    | none => rw [hi] at h; simp at h
    | some i =>
      cases hs : infos ks with
      | none => rw [hi, hs] at h; simp at h
      | some is' =>
        rw [hi, hs] at h; simp at h; subst h
        simp [info_sound h1 hi, infos_sound h2 hs]
  | [], _ :: _, _, h, _ => h.elim
  | _ :: _, [], _, h, _ => h.elim

theorem fval_sound {gs : List ℕ} {ks : List K} {v : ℕ} (hs : Sat gs ks) (h : fval ks = some v) :
    cval gs = some v := by
  simp only [fval] at h
  cases hi : infos ks with
  | none => rw [hi] at h; simp at h
  | some is => rw [hi] at h; simp only at h; rw [cval, infos_sound hs hi]; exact h

/-- all family members of total size below `N` have their claimed values -/
def GoodBelow (N : ℕ) : Prop := ∀ gs : List ℕ, gs.sum < N → ∀ v, cval gs = some v → sg (ofGaps gs) = v

theorem fsum_sound {N : ℕ} (hG : GoodBelow N) : ∀ {gcs : List (List ℕ)} {cs : List (List K)} {w : ℕ},
    Sat2 gcs cs → fsum cs = some w → sumAll gcs < N → xsum gcs = w
  | [], [], w, _, h, _ => by simp [fsum] at h; subst h; rfl
  | g :: gcs, c :: cs, w, ⟨h1, h2⟩, h, hN => by
    simp only [fsum] at h
    cases hv : fval c with
    | none => rw [hv] at h; simp at h
    | some v =>
      cases hw : fsum cs with
      | none => rw [hv, hw] at h; simp at h
      | some w' =>
        rw [hv, hw] at h; simp at h; subst h
        simp only [sumAll, List.map_cons, List.sum_cons] at hN
        simp only [xsum]
        rw [hG g (by omega) v (fval_sound h1 hv), fsum_sound hG h2 hw (by unfold sumAll; omega)]
  | [], _ :: _, _, h, _, _ => h.elim
  | _ :: _, [], _, h, _, _ => h.elim

theorem rval_sound {N : ℕ} (hG : GoodBelow N) {gq : List ℕ} {q : List K} {u : ℕ} (hS : Sat gq q)
    (ht : tir (ofGaps gq) = false) (hN : gq.sum < N) (h : rval q = some u) : sg (ofGaps gq) = u := by
  simp only [rval] at h
  cases hr : red q.length q with
  | none => rw [hr] at h; simp at h
  | some cs =>
    rw [hr] at h; simp only at h
    obtain ⟨gcs, h1, h2, h3⟩ := red_sound _ q cs gq hr hS ht
    rw [h2, fsum_sound hG h1 h (by omega)]

theorem hasVal_sound {N : ℕ} (hG : GoodBelow N) {gs : List ℕ} {ks : List K} {u : ℕ} (hS : Sat gs ks)
    (hN : gs.sum ≤ N) (h : hasVal u ks = true) : ∃ t, IsMove (ofGaps gs) t ∧ sg t = u := by
  obtain ⟨q, gq, hp, hSq, hsum, A, B, e1, e2⟩ := sure_move hS h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  have ht : tir (ofGaps gq) = false := by simpa using legal_sound hSq hp.1
  refine ⟨ofGaps gq, ?_, rval_sound hG hSq ht (by omega) hp.2⟩
  rw [e1, e2]; rw [e2] at ht; exact isMove_of ht

theorem optAll_sound {N : ℕ} (hG : GoodBelow N) {gs : List ℕ} {ks : List K} {v : ℕ} (hS : Sat gs ks)
    (hN : gs.sum ≤ N) (h : allMv splitsAll (optOk v) [] ks = true) :
    ∀ t, IsMove (ofGaps gs) t → sg t ≠ v := by
  intro t ht
  obtain ⟨l, r, e, rfl, htir⟩ := isMove_iff.mp ht
  obtain ⟨gxs, g, gys, j, k', rfl, rfl, e5⟩ := move_ofGaps gs l r e
  obtain ⟨xs, kb, rfl, hxs, hkb⟩ := Sat.split_left hS
  obtain ⟨k, ys, rfl, hk, hys⟩ := Sat.cons_left hkb
  obtain ⟨ab, hab, h1, h2⟩ := splitsAll_complete hk rfl
  have hq := allMv_spec _ _ _ [] h xs k ys rfl ab hab
  simp only [List.reverse_nil, List.nil_append] at hq
  set q := xs ++ ab.1 :: ab.2 :: ys with hqdef
  have hSq : Sat (gxs ++ j :: k' :: gys) q := Sat.append hxs (Sat.cons h1 (Sat.cons h2 hys))
  rw [e5] at htir ⊢
  have hsumq : (gxs ++ j :: k' :: gys).sum + 1 = (gxs ++ (j + 1 + k') :: gys).sum := by
    simp [List.sum_append]; omega
  simp only [optOk] at hq
  cases hl : legal q with
  | none => rw [hl] at hq; simp at hq
  | some b =>
    cases b with
    | false =>
      have := legal_sound hSq hl; rw [htir] at this; simp at this
    | true =>
      rw [hl] at hq; simp only at hq
      cases hr : red q.length q with
      | none => rw [hr] at hq; simp at hq
      | some cs =>
        rw [hr] at hq; simp only at hq
        obtain ⟨gcs, hS2, hx, hsc⟩ := red_sound _ q cs _ hr hSq htir
        rw [hx]
        cases hf : fsum cs with
        | some w =>
          rw [hf] at hq; simp at hq
          rw [fsum_sound hG hS2 hf (by omega)]; exact hq
        | none =>
          rw [hf] at hq; simp only at hq
          obtain ⟨a, c, b, ov, rfl, hfo, hany⟩ := replyOk_spec v cs [] hq
          obtain ⟨ga, gcb, rfl, hga, hcb⟩ := Sat2.split hS2
          obtain ⟨gc, gb, rfl, hgc, hgb⟩ : ∃ gc gb, gcb = gc :: gb ∧ Sat gc c ∧ Sat2 gb b := by
            cases gcb with
            | nil => exact hcb.elim
            | cons gc gb => exact ⟨gc, gb, rfl, hcb.1, hcb.2⟩
          rw [sumAll_append] at hsc
          simp only [sumAll, List.map_cons, List.sum_cons] at hsc
          have hov : xsum (ga ++ gb) = ov := by
            refine fsum_sound hG (Sat2.append hga hgb) (by simpa using hfo) ?_
            rw [sumAll_append]; unfold sumAll; omega
          obtain ⟨rq, gr, hp, hSr, hsr, A, B, e1, e2⟩ := sure_move hgc hany
          simp only [Bool.and_eq_true, beq_iff_eq] at hp
          have htr : tir (ofGaps gr) = false := by simpa using legal_sound hSr hp.1
          have hval := rval_sound hG hSr htr (by omega) hp.2
          have hmv : IsMove (ofGaps gc) (ofGaps gr) := by
            rw [e1, e2]; rw [e2] at htr; exact isMove_of htr
          have hne := sg_ne_of_isMove hmv
          rw [hval] at hne
          simp only [xsum_append] at hov ⊢
          simp only [xsum]
          intro hv
          apply hne
          have e : xsum ga ^^^ (sg (ofGaps gc) ^^^ xsum gb) =
              sg (ofGaps gc) ^^^ (xsum ga ^^^ xsum gb) := by ac_rfl
          rw [← hov, ← hv, e, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-! ## Theorem A -/

def canonOK : Prop := ∀ gs : List ℕ, (cval gs).isSome → chkP (gs.map canon) = true

theorem canon_sat (n : ℕ) : sat n (canon n) := by
  unfold canon thrM; split_ifs with h
  · rfl
  · exact ⟨by omega, rfl⟩

theorem Sat_canon : ∀ gs : List ℕ, Sat gs (gs.map canon)
  | [] => trivial
  | g :: gs => ⟨canon_sat g, Sat_canon gs⟩

theorem info_canon (n : ℕ) : info (canon n) = some (ninfo n) := by
  unfold canon thrM ninfo
  split_ifs with h1 h2 h2 <;> simp [info] <;> omega

theorem infos_canon : ∀ gs : List ℕ, infos (gs.map canon) = some (gs.map ninfo)
  | [] => rfl
  | g :: gs => by simp [infos, info_canon, infos_canon gs]

theorem fval_canon (gs : List ℕ) : fval (gs.map canon) = cval gs := by
  simp [fval, infos_canon, cval]

theorem thmA (hc : canonOK) : ∀ gs v, cval gs = some v → sg (ofGaps gs) = v := by
  suffices H : ∀ N, GoodBelow N from fun gs v h => H (gs.sum + 1) gs (by omega) v h
  intro N
  induction N with
  | zero => intro gs h; omega
  | succ N ih =>
    intro gs hgs v hv
    by_cases hlt : gs.sum < N
    · exact ih gs hlt v hv
    have hN : gs.sum ≤ N := by omega
    have hchk := hc gs (by simp [hv])
    have hS := Sat_canon gs
    simp only [chkP, fval_canon, hv, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hchk
    apply sg_eq_of
    · intro u hu
      exact hasVal_sound ih hS hN (hchk.1 u hu)
    · exact optAll_sound ih hS hN hchk.2

/-- boards `[aXb]` outside the family: options of value 0 and 1 give `sg ≥ 2` -/
theorem two_le_of_conjOk (hc : canonOK) {gs : List ℕ} (h : conjOk (gs.map canon) = true) :
    2 ≤ sg (ofGaps gs) := by
  have hG : GoodBelow (gs.sum + 1) := fun gs' _ v hv => thmA hc gs' v hv
  simp only [conjOk, Bool.and_eq_true] at h
  obtain ⟨t0, ht0, e0⟩ := hasVal_sound hG (Sat_canon gs) (by omega) h.1
  obtain ⟨t1, ht1, e1⟩ := hasVal_sound hG (Sat_canon gs) (by omega) h.2
  have n0 := sg_ne_of_isMove ht0
  have n1 := sg_ne_of_isMove ht1
  omega

end ITB
```

### `TBCert00.lean`

```lean
import TBCheck

/-! Certificate row 0: first gap `K.e 0`. Each statement is checked by the kernel. -/

namespace ITB

theorem cert1 : (ksAll.all fun k => chkP [k]) = true := by decide +kernel

theorem cert2_0 : (ksAll.all fun k2 => chkP [K.e 0, k2]) = true := by decide +kernel

theorem cert3_0 : (ksAll.all fun k2 => chkP [K.e 0, k2, K.e 0]) = true := by decide +kernel

theorem cert3m_0 : (ksAll.all fun k2 => chkP [K.e 0, k2, K.e 0]) = true := by decide +kernel

theorem certc_0 : (ksAll.all fun k2 => (fval [K.e 0, k2]).isSome || conjOk [K.e 0, k2]) = true := by
  decide +kernel

end ITB
```

### `TBCert01.lean`

```lean
import TBCheck

/-! Certificate row 1: first gap `K.e 1`. Each statement is checked by the kernel. -/

namespace ITB

theorem cert2_1 : (ksAll.all fun k2 => chkP [K.e 1, k2]) = true := by decide +kernel

theorem cert3_1 : (ksAll.all fun k2 => chkP [K.e 1, k2, K.e 0]) = true := by decide +kernel

theorem cert3m_1 : (ksAll.all fun k2 => chkP [K.e 0, k2, K.e 1]) = true := by decide +kernel

theorem certc_1 : (ksAll.all fun k2 => (fval [K.e 1, k2]).isSome || conjOk [K.e 1, k2]) = true := by
  decide +kernel

end ITB
```

### `TBCert02.lean`

```lean
import TBCheck

/-! Certificate row 2: first gap `K.e 2`. Each statement is checked by the kernel. -/

namespace ITB

theorem cert2_2 : (ksAll.all fun k2 => chkP [K.e 2, k2]) = true := by decide +kernel

theorem cert3_2 : (ksAll.all fun k2 => chkP [K.e 2, k2, K.e 0]) = true := by decide +kernel

theorem cert3m_2 : (ksAll.all fun k2 => chkP [K.e 0, k2, K.e 2]) = true := by decide +kernel

theorem certc_2 : (ksAll.all fun k2 => (fval [K.e 2, k2]).isSome || conjOk [K.e 2, k2]) = true := by
  decide +kernel

end ITB
```

### `TBCert03.lean`

```lean
import TBCheck

/-! Certificate row 3: first gap `K.e 3`. Each statement is checked by the kernel. -/

namespace ITB

theorem cert2_3 : (ksAll.all fun k2 => chkP [K.e 3, k2]) = true := by decide +kernel

theorem cert3_3 : (ksAll.all fun k2 => chkP [K.e 3, k2, K.e 0]) = true := by decide +kernel

theorem cert3m_3 : (ksAll.all fun k2 => chkP [K.e 0, k2, K.e 3]) = true := by decide +kernel

theorem certc_3 : (ksAll.all fun k2 => (fval [K.e 3, k2]).isSome || conjOk [K.e 3, k2]) = true := by
  decide +kernel

end ITB
```

### `TBCert04.lean`

```lean
import TBCheck

/-! Certificate row 4: first gap `K.e 4`. Each statement is checked by the kernel. -/

namespace ITB

theorem cert2_4 : (ksAll.all fun k2 => chkP [K.e 4, k2]) = true := by decide +kernel

theorem cert3_4 : (ksAll.all fun k2 => chkP [K.e 4, k2, K.e 0]) = true := by decide +kernel

theorem cert3m_4 : (ksAll.all fun k2 => chkP [K.e 0, k2, K.e 4]) = true := by decide +kernel

theorem certc_4 : (ksAll.all fun k2 => (fval [K.e 4, k2]).isSome || conjOk [K.e 4, k2]) = true := by
  decide +kernel

end ITB
```

### `TBCert05.lean`

```lean
import TBCheck

/-! Certificate row 5: first gap `K.e 5`. Each statement is checked by the kernel. -/

namespace ITB

theorem cert2_5 : (ksAll.all fun k2 => chkP [K.e 5, k2]) = true := by decide +kernel

theorem cert3_5 : (ksAll.all fun k2 => chkP [K.e 5, k2, K.e 0]) = true := by decide +kernel

theorem cert3m_5 : (ksAll.all fun k2 => chkP [K.e 0, k2, K.e 5]) = true := by decide +kernel

theorem certc_5 : (ksAll.all fun k2 => (fval [K.e 5, k2]).isSome || conjOk [K.e 5, k2]) = true := by
  decide +kernel

end ITB
```

### `TBCert06.lean`

```lean
import TBCheck

/-! Certificate row 6: first gap `K.e 6`. Each statement is checked by the kernel. -/

namespace ITB

theorem cert2_6 : (ksAll.all fun k2 => chkP [K.e 6, k2]) = true := by decide +kernel

theorem cert3_6 : (ksAll.all fun k2 => chkP [K.e 6, k2, K.e 0]) = true := by decide +kernel

theorem cert3m_6 : (ksAll.all fun k2 => chkP [K.e 0, k2, K.e 6]) = true := by decide +kernel

theorem certc_6 : (ksAll.all fun k2 => (fval [K.e 6, k2]).isSome || conjOk [K.e 6, k2]) = true := by
  decide +kernel

end ITB
```

### `TBCert07.lean`

```lean
import TBCheck

/-! Certificate row 7: first gap `K.e 7`. Each statement is checked by the kernel. -/

namespace ITB

theorem cert2_7 : (ksAll.all fun k2 => chkP [K.e 7, k2]) = true := by decide +kernel

theorem cert3_7 : (ksAll.all fun k2 => chkP [K.e 7, k2, K.e 0]) = true := by decide +kernel

theorem cert3m_7 : (ksAll.all fun k2 => chkP [K.e 0, k2, K.e 7]) = true := by decide +kernel

theorem certc_7 : (ksAll.all fun k2 => (fval [K.e 7, k2]).isSome || conjOk [K.e 7, k2]) = true := by
  decide +kernel

end ITB
```

### `TBCert08.lean`

```lean
import TBCheck

/-! Certificate row 8: first gap `K.e 8`. Each statement is checked by the kernel. -/

namespace ITB

theorem cert2_8 : (ksAll.all fun k2 => chkP [K.e 8, k2]) = true := by decide +kernel

theorem cert3_8 : (ksAll.all fun k2 => chkP [K.e 8, k2, K.e 0]) = true := by decide +kernel

theorem cert3m_8 : (ksAll.all fun k2 => chkP [K.e 0, k2, K.e 8]) = true := by decide +kernel

theorem certc_8 : (ksAll.all fun k2 => (fval [K.e 8, k2]).isSome || conjOk [K.e 8, k2]) = true := by
  decide +kernel

end ITB
```

### `TBCert09.lean`

```lean
import TBCheck

/-! Certificate row 9: first gap `K.e 9`. Each statement is checked by the kernel. -/

namespace ITB

theorem cert2_9 : (ksAll.all fun k2 => chkP [K.e 9, k2]) = true := by decide +kernel

theorem cert3_9 : (ksAll.all fun k2 => chkP [K.e 9, k2, K.e 0]) = true := by decide +kernel

theorem cert3m_9 : (ksAll.all fun k2 => chkP [K.e 0, k2, K.e 9]) = true := by decide +kernel

theorem certc_9 : (ksAll.all fun k2 => (fval [K.e 9, k2]).isSome || conjOk [K.e 9, k2]) = true := by
  decide +kernel

end ITB
```

### `TBCert10.lean`

```lean
import TBCheck

/-! Certificate row 10: first gap `K.e 10`. Each statement is checked by the kernel. -/

namespace ITB

theorem cert2_10 : (ksAll.all fun k2 => chkP [K.e 10, k2]) = true := by decide +kernel

theorem cert3_10 : (ksAll.all fun k2 => chkP [K.e 10, k2, K.e 0]) = true := by decide +kernel

theorem cert3m_10 : (ksAll.all fun k2 => chkP [K.e 0, k2, K.e 10]) = true := by decide +kernel

theorem certc_10 : (ksAll.all fun k2 => (fval [K.e 10, k2]).isSome || conjOk [K.e 10, k2]) = true := by
  decide +kernel

end ITB
```

### `TBCert11.lean`

```lean
import TBCheck

/-! Certificate row 11: first gap `K.e 11`. Each statement is checked by the kernel. -/

namespace ITB

theorem cert2_11 : (ksAll.all fun k2 => chkP [K.e 11, k2]) = true := by decide +kernel

theorem cert3_11 : (ksAll.all fun k2 => chkP [K.e 11, k2, K.e 0]) = true := by decide +kernel

theorem cert3m_11 : (ksAll.all fun k2 => chkP [K.e 0, k2, K.e 11]) = true := by decide +kernel

theorem certc_11 : (ksAll.all fun k2 => (fval [K.e 11, k2]).isSome || conjOk [K.e 11, k2]) = true := by
  decide +kernel

end ITB
```

### `TBCert12.lean`

```lean
import TBCheck

/-! Certificate row 12: first gap `K.e 12`. Each statement is checked by the kernel. -/

namespace ITB

theorem cert2_12 : (ksAll.all fun k2 => chkP [K.e 12, k2]) = true := by decide +kernel

theorem cert3_12 : (ksAll.all fun k2 => chkP [K.e 12, k2, K.e 0]) = true := by decide +kernel

theorem cert3m_12 : (ksAll.all fun k2 => chkP [K.e 0, k2, K.e 12]) = true := by decide +kernel

theorem certc_12 : (ksAll.all fun k2 => (fval [K.e 12, k2]).isSome || conjOk [K.e 12, k2]) = true := by
  decide +kernel

end ITB
```

### `TBCert13.lean`

```lean
import TBCheck

/-! Certificate row 13: first gap `K.g 13 0`. Each statement is checked by the kernel. -/

namespace ITB

theorem cert2_13 : (ksAll.all fun k2 => chkP [(K.g 13 0), k2]) = true := by decide +kernel

theorem cert3_13 : (ksAll.all fun k2 => chkP [(K.g 13 0), k2, K.e 0]) = true := by decide +kernel

theorem cert3m_13 : (ksAll.all fun k2 => chkP [K.e 0, k2, (K.g 13 0)]) = true := by decide +kernel

theorem certc_13 : (ksAll.all fun k2 => (fval [(K.g 13 0), k2]).isSome || conjOk [(K.g 13 0), k2]) = true := by
  decide +kernel

end ITB
```

### `TBCert14.lean`

```lean
import TBCheck

/-! Certificate row 14: first gap `K.g 13 1`. Each statement is checked by the kernel. -/

namespace ITB

theorem cert2_14 : (ksAll.all fun k2 => chkP [(K.g 13 1), k2]) = true := by decide +kernel

theorem cert3_14 : (ksAll.all fun k2 => chkP [(K.g 13 1), k2, K.e 0]) = true := by decide +kernel

theorem cert3m_14 : (ksAll.all fun k2 => chkP [K.e 0, k2, (K.g 13 1)]) = true := by decide +kernel

theorem certc_14 : (ksAll.all fun k2 => (fval [(K.g 13 1), k2]).isSome || conjOk [(K.g 13 1), k2]) = true := by
  decide +kernel

end ITB
```

### `TBCert15.lean`

```lean
import TBCheck

/-! Certificate row 15: first gap `K.g 13 2`. Each statement is checked by the kernel. -/

namespace ITB

theorem cert2_15 : (ksAll.all fun k2 => chkP [(K.g 13 2), k2]) = true := by decide +kernel

theorem cert3_15 : (ksAll.all fun k2 => chkP [(K.g 13 2), k2, K.e 0]) = true := by decide +kernel

theorem cert3m_15 : (ksAll.all fun k2 => chkP [K.e 0, k2, (K.g 13 2)]) = true := by decide +kernel

theorem certc_15 : (ksAll.all fun k2 => (fval [(K.g 13 2), k2]).isSome || conjOk [(K.g 13 2), k2]) = true := by
  decide +kernel

end ITB
```

### `TBCert16.lean`

```lean
import TBCheck

/-! Certificate row 16: first gap `K.g 13 3`. Each statement is checked by the kernel. -/

namespace ITB

theorem cert2_16 : (ksAll.all fun k2 => chkP [(K.g 13 3), k2]) = true := by decide +kernel

theorem cert3_16 : (ksAll.all fun k2 => chkP [(K.g 13 3), k2, K.e 0]) = true := by decide +kernel

theorem cert3m_16 : (ksAll.all fun k2 => chkP [K.e 0, k2, (K.g 13 3)]) = true := by decide +kernel

theorem certc_16 : (ksAll.all fun k2 => (fval [(K.g 13 3), k2]).isSome || conjOk [(K.g 13 3), k2]) = true := by
  decide +kernel

end ITB
```

### `TBCert17.lean`

```lean
import TBCheck

/-! Certificate row 17: first gap `K.g 13 4`. Each statement is checked by the kernel. -/

namespace ITB

theorem cert2_17 : (ksAll.all fun k2 => chkP [(K.g 13 4), k2]) = true := by decide +kernel

theorem cert3_17 : (ksAll.all fun k2 => chkP [(K.g 13 4), k2, K.e 0]) = true := by decide +kernel

theorem cert3m_17 : (ksAll.all fun k2 => chkP [K.e 0, k2, (K.g 13 4)]) = true := by decide +kernel

theorem certc_17 : (ksAll.all fun k2 => (fval [(K.g 13 4), k2]).isSome || conjOk [(K.g 13 4), k2]) = true := by
  decide +kernel

end ITB
```

### `TBCert18.lean`

```lean
import TBCheck

/-! Certificate row 18: first gap `K.g 13 5`. Each statement is checked by the kernel. -/

namespace ITB

theorem cert2_18 : (ksAll.all fun k2 => chkP [(K.g 13 5), k2]) = true := by decide +kernel

theorem cert3_18 : (ksAll.all fun k2 => chkP [(K.g 13 5), k2, K.e 0]) = true := by decide +kernel

theorem cert3m_18 : (ksAll.all fun k2 => chkP [K.e 0, k2, (K.g 13 5)]) = true := by decide +kernel

theorem certc_18 : (ksAll.all fun k2 => (fval [(K.g 13 5), k2]).isSome || conjOk [(K.g 13 5), k2]) = true := by
  decide +kernel

end ITB
```

### `TBCert19.lean`

```lean
import TBCheck

/-! Certificate row 19: first gap `K.g 13 6`. Each statement is checked by the kernel. -/

namespace ITB

theorem cert2_19 : (ksAll.all fun k2 => chkP [(K.g 13 6), k2]) = true := by decide +kernel

theorem cert3_19 : (ksAll.all fun k2 => chkP [(K.g 13 6), k2, K.e 0]) = true := by decide +kernel

theorem cert3m_19 : (ksAll.all fun k2 => chkP [K.e 0, k2, (K.g 13 6)]) = true := by decide +kernel

theorem certc_19 : (ksAll.all fun k2 => (fval [(K.g 13 6), k2]).isSome || conjOk [(K.g 13 6), k2]) = true := by
  decide +kernel

end ITB
```

### `TBCert20.lean`

```lean
import TBCheck

/-! Certificate row 20: first gap `K.g 13 7`. Each statement is checked by the kernel. -/

namespace ITB

theorem cert2_20 : (ksAll.all fun k2 => chkP [(K.g 13 7), k2]) = true := by decide +kernel

theorem cert3_20 : (ksAll.all fun k2 => chkP [(K.g 13 7), k2, K.e 0]) = true := by decide +kernel

theorem cert3m_20 : (ksAll.all fun k2 => chkP [K.e 0, k2, (K.g 13 7)]) = true := by decide +kernel

theorem certc_20 : (ksAll.all fun k2 => (fval [(K.g 13 7), k2]).isSome || conjOk [(K.g 13 7), k2]) = true := by
  decide +kernel

end ITB
```

### `TBCert21.lean`

```lean
import TBCheck

/-! Certificate row 21: first gap `K.g 13 8`. Each statement is checked by the kernel. -/

namespace ITB

theorem cert2_21 : (ksAll.all fun k2 => chkP [(K.g 13 8), k2]) = true := by decide +kernel

theorem cert3_21 : (ksAll.all fun k2 => chkP [(K.g 13 8), k2, K.e 0]) = true := by decide +kernel

theorem cert3m_21 : (ksAll.all fun k2 => chkP [K.e 0, k2, (K.g 13 8)]) = true := by decide +kernel

theorem certc_21 : (ksAll.all fun k2 => (fval [(K.g 13 8), k2]).isSome || conjOk [(K.g 13 8), k2]) = true := by
  decide +kernel

end ITB
```

### `TBCert22.lean`

```lean
import TBCheck

/-! Certificate row 22: first gap `K.g 13 9`. Each statement is checked by the kernel. -/

namespace ITB

theorem cert2_22 : (ksAll.all fun k2 => chkP [(K.g 13 9), k2]) = true := by decide +kernel

theorem cert3_22 : (ksAll.all fun k2 => chkP [(K.g 13 9), k2, K.e 0]) = true := by decide +kernel

theorem cert3m_22 : (ksAll.all fun k2 => chkP [K.e 0, k2, (K.g 13 9)]) = true := by decide +kernel

theorem certc_22 : (ksAll.all fun k2 => (fval [(K.g 13 9), k2]).isSome || conjOk [(K.g 13 9), k2]) = true := by
  decide +kernel

end ITB
```

### `TBAssembly.lean`

```lean
import TBSound
import TBCert00
import TBCert01
import TBCert02
import TBCert03
import TBCert04
import TBCert05
import TBCert06
import TBCert07
import TBCert08
import TBCert09
import TBCert10
import TBCert11
import TBCert12
import TBCert13
import TBCert14
import TBCert15
import TBCert16
import TBCert17
import TBCert18
import TBCert19
import TBCert20
import TBCert21
import TBCert22

/-! Coverage of the canonical gap alphabet by the kernel-checked rows. -/
namespace ITB

theorem canon_mem (n : ℕ) : canon n ∈ ksAll := by
  unfold canon ksAll
  split
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨n, List.mem_range.mpr ‹_›, rfl⟩)
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨n % 10, List.mem_range.mpr (by omega), rfl⟩)


theorem chk_two {a b : K} (ha : a ∈ ksAll) (hb : b ∈ ksAll) :
    chkP [a, b] = true := by
  change a ∈ [K.e 0, K.e 1, K.e 2, K.e 3, K.e 4, K.e 5, K.e 6, K.e 7, K.e 8, K.e 9, K.e 10, K.e 11, K.e 12, K.g 13 0, K.g 13 1, K.g 13 2, K.g 13 3, K.g 13 4, K.g 13 5, K.g 13 6, K.g 13 7, K.g 13 8, K.g 13 9] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp cert2_0 b hb
  · exact List.all_eq_true.mp cert2_1 b hb
  · exact List.all_eq_true.mp cert2_2 b hb
  · exact List.all_eq_true.mp cert2_3 b hb
  · exact List.all_eq_true.mp cert2_4 b hb
  · exact List.all_eq_true.mp cert2_5 b hb
  · exact List.all_eq_true.mp cert2_6 b hb
  · exact List.all_eq_true.mp cert2_7 b hb
  · exact List.all_eq_true.mp cert2_8 b hb
  · exact List.all_eq_true.mp cert2_9 b hb
  · exact List.all_eq_true.mp cert2_10 b hb
  · exact List.all_eq_true.mp cert2_11 b hb
  · exact List.all_eq_true.mp cert2_12 b hb
  · exact List.all_eq_true.mp cert2_13 b hb
  · exact List.all_eq_true.mp cert2_14 b hb
  · exact List.all_eq_true.mp cert2_15 b hb
  · exact List.all_eq_true.mp cert2_16 b hb
  · exact List.all_eq_true.mp cert2_17 b hb
  · exact List.all_eq_true.mp cert2_18 b hb
  · exact List.all_eq_true.mp cert2_19 b hb
  · exact List.all_eq_true.mp cert2_20 b hb
  · exact List.all_eq_true.mp cert2_21 b hb
  · exact List.all_eq_true.mp cert2_22 b hb

theorem chk_three_right {a b : K} (ha : a ∈ ksAll) (hb : b ∈ ksAll) :
    chkP [a, b, K.e 0] = true := by
  change a ∈ [K.e 0, K.e 1, K.e 2, K.e 3, K.e 4, K.e 5, K.e 6, K.e 7, K.e 8, K.e 9, K.e 10, K.e 11, K.e 12, K.g 13 0, K.g 13 1, K.g 13 2, K.g 13 3, K.g 13 4, K.g 13 5, K.g 13 6, K.g 13 7, K.g 13 8, K.g 13 9] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp cert3_0 b hb
  · exact List.all_eq_true.mp cert3_1 b hb
  · exact List.all_eq_true.mp cert3_2 b hb
  · exact List.all_eq_true.mp cert3_3 b hb
  · exact List.all_eq_true.mp cert3_4 b hb
  · exact List.all_eq_true.mp cert3_5 b hb
  · exact List.all_eq_true.mp cert3_6 b hb
  · exact List.all_eq_true.mp cert3_7 b hb
  · exact List.all_eq_true.mp cert3_8 b hb
  · exact List.all_eq_true.mp cert3_9 b hb
  · exact List.all_eq_true.mp cert3_10 b hb
  · exact List.all_eq_true.mp cert3_11 b hb
  · exact List.all_eq_true.mp cert3_12 b hb
  · exact List.all_eq_true.mp cert3_13 b hb
  · exact List.all_eq_true.mp cert3_14 b hb
  · exact List.all_eq_true.mp cert3_15 b hb
  · exact List.all_eq_true.mp cert3_16 b hb
  · exact List.all_eq_true.mp cert3_17 b hb
  · exact List.all_eq_true.mp cert3_18 b hb
  · exact List.all_eq_true.mp cert3_19 b hb
  · exact List.all_eq_true.mp cert3_20 b hb
  · exact List.all_eq_true.mp cert3_21 b hb
  · exact List.all_eq_true.mp cert3_22 b hb

theorem chk_three_left {a b : K} (ha : a ∈ ksAll) (hb : b ∈ ksAll) :
    chkP [K.e 0, b, a] = true := by
  change a ∈ [K.e 0, K.e 1, K.e 2, K.e 3, K.e 4, K.e 5, K.e 6, K.e 7, K.e 8, K.e 9, K.e 10, K.e 11, K.e 12, K.g 13 0, K.g 13 1, K.g 13 2, K.g 13 3, K.g 13 4, K.g 13 5, K.g 13 6, K.g 13 7, K.g 13 8, K.g 13 9] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp cert3m_0 b hb
  · exact List.all_eq_true.mp cert3m_1 b hb
  · exact List.all_eq_true.mp cert3m_2 b hb
  · exact List.all_eq_true.mp cert3m_3 b hb
  · exact List.all_eq_true.mp cert3m_4 b hb
  · exact List.all_eq_true.mp cert3m_5 b hb
  · exact List.all_eq_true.mp cert3m_6 b hb
  · exact List.all_eq_true.mp cert3m_7 b hb
  · exact List.all_eq_true.mp cert3m_8 b hb
  · exact List.all_eq_true.mp cert3m_9 b hb
  · exact List.all_eq_true.mp cert3m_10 b hb
  · exact List.all_eq_true.mp cert3m_11 b hb
  · exact List.all_eq_true.mp cert3m_12 b hb
  · exact List.all_eq_true.mp cert3m_13 b hb
  · exact List.all_eq_true.mp cert3m_14 b hb
  · exact List.all_eq_true.mp cert3m_15 b hb
  · exact List.all_eq_true.mp cert3m_16 b hb
  · exact List.all_eq_true.mp cert3m_17 b hb
  · exact List.all_eq_true.mp cert3m_18 b hb
  · exact List.all_eq_true.mp cert3m_19 b hb
  · exact List.all_eq_true.mp cert3m_20 b hb
  · exact List.all_eq_true.mp cert3m_21 b hb
  · exact List.all_eq_true.mp cert3m_22 b hb

theorem chk_low_options {a b : K} (ha : a ∈ ksAll) (hb : b ∈ ksAll) :
    ((fval [a, b]).isSome || conjOk [a, b]) = true := by
  change a ∈ [K.e 0, K.e 1, K.e 2, K.e 3, K.e 4, K.e 5, K.e 6, K.e 7, K.e 8, K.e 9, K.e 10, K.e 11, K.e 12, K.g 13 0, K.g 13 1, K.g 13 2, K.g 13 3, K.g 13 4, K.g 13 5, K.g 13 6, K.g 13 7, K.g 13 8, K.g 13 9] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp certc_0 b hb
  · exact List.all_eq_true.mp certc_1 b hb
  · exact List.all_eq_true.mp certc_2 b hb
  · exact List.all_eq_true.mp certc_3 b hb
  · exact List.all_eq_true.mp certc_4 b hb
  · exact List.all_eq_true.mp certc_5 b hb
  · exact List.all_eq_true.mp certc_6 b hb
  · exact List.all_eq_true.mp certc_7 b hb
  · exact List.all_eq_true.mp certc_8 b hb
  · exact List.all_eq_true.mp certc_9 b hb
  · exact List.all_eq_true.mp certc_10 b hb
  · exact List.all_eq_true.mp certc_11 b hb
  · exact List.all_eq_true.mp certc_12 b hb
  · exact List.all_eq_true.mp certc_13 b hb
  · exact List.all_eq_true.mp certc_14 b hb
  · exact List.all_eq_true.mp certc_15 b hb
  · exact List.all_eq_true.mp certc_16 b hb
  · exact List.all_eq_true.mp certc_17 b hb
  · exact List.all_eq_true.mp certc_18 b hb
  · exact List.all_eq_true.mp certc_19 b hb
  · exact List.all_eq_true.mp certc_20 b hb
  · exact List.all_eq_true.mp certc_21 b hb
  · exact List.all_eq_true.mp certc_22 b hb

end ITB
```

### `TBEndpoint.lean`

```lean
import TBAssembly
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases

set_option linter.unnecessarySeqFocus false

namespace ITB

theorem ninfo_res (n : ℕ) : (ninfo n).res = n % 10 := by
  unfold ninfo
  split <;> rfl

theorem ninfo_isZ (n : ℕ) : (ninfo n).isZ = true ↔ n = 0 := by
  unfold ninfo
  split <;> simp [Info.isZ] <;> omega

theorem ninfo_isS (n c : ℕ) (hc : c < 5) : (ninfo n).isS c = true ↔ n = c := by
  unfold ninfo
  split <;> simp [Info.isS] <;> omega

theorem canonOK_checked : canonOK := by
  intro gs h
  rcases gs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, ds⟩⟩⟩⟩
  · simp [cval, fvalI] at h
  · exact List.all_eq_true.mp cert1 _ (canon_mem a)
  · exact chk_two (canon_mem a) (canon_mem b)
  · by_cases ha : a = 0
    · subst a
      exact chk_three_left (canon_mem c) (canon_mem b)
    · by_cases hc : c = 0
      · subst c
        exact chk_three_right (canon_mem a) (canon_mem b)
      · have ha' : (ninfo a).isZ = false := Bool.eq_false_iff.mpr (mt (ninfo_isZ a).mp ha)
        have hc' : (ninfo c).isZ = false := Bool.eq_false_iff.mpr (mt (ninfo_isZ c).mp hc)
        simp [cval, fvalI, val2, ha', hc'] at h
  · simp [cval, fvalI] at h

theorem count_true_replicate_false (a : ℕ) : (List.replicate a false).count true = 0 := by
  simp [List.count_replicate]

theorem count_emptyBoard (a : ℕ) : (emptyBoard a).count true = 0 := by
  simp [emptyBoard, count_true_replicate_false]

theorem count_board (a b : ℕ) : (board a b).count true = 1 := by
  simp [board, count_true_replicate_false]

theorem at_most_one {s : List Bool} (hs : s.count true ≤ 1) :
    (∃ a, s = emptyBoard a) ∨ ∃ a b, s = board a b := by
  induction s with
  | nil => exact Or.inl ⟨0, rfl⟩
  | cons x s ih =>
    cases x with
    | false =>
      have hs' : s.count true ≤ 1 := by simpa using hs
      rcases ih hs' with ⟨a, rfl⟩ | ⟨a, b, rfl⟩
      · exact Or.inl ⟨a+1, rfl⟩
      · exact Or.inr ⟨a+1, b, rfl⟩
    | true =>
      have h : s.count true = 0 := by simp at hs; omega
      have e : s = List.replicate s.length false := by
        apply List.eq_replicate_of_mem
        intro x hx
        cases x
        · rfl
        · exact False.elim ((List.count_eq_zero.mp h) hx)
      exact Or.inr ⟨0, s.length, by rw [board, List.replicate_zero, List.nil_append, List.singleton_append, ← e]⟩

theorem board_inj {a b c d : ℕ} (h : board a b = board c d) : a = c ∧ b = d := by
  induction a generalizing c with
  | zero =>
    cases c with
    | zero =>
      have hl := congrArg List.length h
      simp [board] at hl
      exact ⟨rfl, by omega⟩
    | succ c => simp [board, List.replicate_succ] at h
  | succ a ih =>
    cases c with
    | zero => simp [board, List.replicate_succ] at h
    | succ c =>
      have ht : board a b = board c d := List.cons.inj h |>.2
      obtain ⟨rfl, rfl⟩ := ih ht
      exact ⟨rfl, rfl⟩

theorem chi2_table (n : ℕ) :
    chi2 n = if z0 (n % 10) then 0 else if c2bit (n % 10) = 0 then 1 else -1 := by
  conv_lhs => rw [← ZMod.natCast_mod n 10]
  have hr : n % 10 < 10 := Nat.mod_lt _ (by decide)
  generalize n % 10 = r at hr ⊢
  interval_cases r <;> decide

theorem empty_regular (n : ℕ) : InR (emptyBoard n) := by
  by_cases h : div3 (n : ZMod 10) ∈ ([0, 1, 2, 3, 4] : List (ZMod 10))
  · exact Or.inl (Or.inl ⟨n, rfl, by simp [chi1, h]⟩)
  · exact Or.inr (Or.inl ⟨n, rfl, by simp [chi1, h]⟩)

def InR_empty (n : ℕ) : Prop := chi1 n = 1 ∨ chi1 n = -1

def InR_one (a b : ℕ) : Prop :=
  chi2 a * chi2 b ≠ 0 ∨ (a = 0 ∧ (b % 10 = 1 ∨ b % 10 = 6)) ∨
    (b = 0 ∧ (a % 10 = 1 ∨ a % 10 = 6))

theorem inR_board_iff (a b : ℕ) : InR (board a b) ↔ InR_one a b := by
  have hcast (n k : ℕ) (hk : k < 10) : (n : ZMod 10) = (k : ZMod 10) ↔ n % 10 = k := by
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hk]
  have empty_ne (n : ℕ) : board a b ≠ emptyBoard n := by
    intro h
    have e := congrArg (List.count true) h
    simp [count_board, count_emptyBoard] at e
  have two_ne (n : ℕ) : board a b ≠ [true] ++ List.replicate n false ++ [true] := by
    intro h
    have e := congrArg (List.count true) h
    simp [count_board, count_true_replicate_false] at e
  have boundary (k : ℕ) (hk : k < 10) :
      (∃ n : ℕ, (n : ZMod 10) = (k : ZMod 10) ∧ (board a b = board 0 n ∨ board a b = board n 0)) ↔
        (a = 0 ∧ b % 10 = k) ∨ (b = 0 ∧ a % 10 = k) := by
    constructor
    · rintro ⟨n, hn, h | h⟩
      · obtain ⟨ha, hb⟩ := board_inj h
        exact Or.inl ⟨ha, hb ▸ (hcast n k hk).mp hn⟩
      · obtain ⟨ha, hb⟩ := board_inj h
        exact Or.inr ⟨hb, ha ▸ (hcast n k hk).mp hn⟩
    · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
      · exact ⟨b, (hcast b k hk).mpr h, Or.inl rfl⟩
      · exact ⟨a, (hcast a k hk).mpr h, Or.inr rfl⟩
  have single (z : ℤ) : (∃ m n : ℕ, board a b = board m n ∧ chi2 m * chi2 n = z) ↔
      chi2 a * chi2 b = z := by
    constructor
    · rintro ⟨m, n, h, hz⟩
      obtain ⟨rfl, rfl⟩ := board_inj h
      exact hz
    · exact fun h => ⟨a, b, rfl, h⟩
  have prod : (chi2 a * chi2 b = 1 ∨ chi2 a * chi2 b = -1) ↔ chi2 a * chi2 b ≠ 0 := by
    rw [chi2_table, chi2_table]
    split_ifs <;> decide
  have bd1 : (1 : ZMod 10) = ((1 : ℕ) : ZMod 10) := rfl
  have bd6 : (6 : ZMod 10) = ((6 : ℕ) : ZMod 10) := rfl
  unfold InR R1 Rm1 InR_one
  simp only [empty_ne, two_ne, false_and, and_false, exists_false, false_or, or_false, single]
  rw [bd6, bd1, boundary 6 (by decide), boundary 1 (by decide)]
  tauto

theorem low_single {a b : ℕ} (h : sg (board a b) ≤ 1) :
    InR_one a b ∨ (a,b) ∈ [(1,1),(1,4),(4,1),(4,4)] := by
  have hc := chk_low_options (canon_mem a) (canon_mem b)
  change ((fval ([a, b].map canon)).isSome || conjOk ([a, b].map canon)) = true at hc
  rw [fval_canon, Bool.or_eq_true] at hc
  rcases hv : cval [a, b] with _ | v
  · have hlo : 2 ≤ sg (board a b) := by
      rw [board_eq_ofGaps]
      exact two_le_of_conjOk canonOK_checked (by simpa [hv] using hc)
    omega
  · have hsv := thmA canonOK_checked [a, b] v hv
    rw [← board_eq_ofGaps] at hsv
    have hvle : v ≤ 1 := by omega
    change val1 (ninfo a) (ninfo b) = some v at hv
    unfold val1 at hv
    simp only [ninfo_res] at hv
    split at hv
    · left
      apply Or.inl
      rename_i hab
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hab
      apply mul_ne_zero
      · rw [chi2_table, hab.1]
        simp only [Bool.false_eq_true, ite_false]
        split <;> decide
      · rw [chi2_table, hab.2]
        simp only [Bool.false_eq_true, ite_false]
        split <;> decide
    · split at hv
      · left
        rename_i h6
        simp only [Bool.or_eq_true, Bool.and_eq_true, ninfo_isZ, beq_iff_eq] at h6
        rcases h6 with h6 | h6
        · exact Or.inr (Or.inl ⟨h6.1, Or.inr h6.2⟩)
        · exact Or.inr (Or.inr ⟨h6.1, Or.inr h6.2⟩)
      · split at hv
        · left
          rename_i h1
          simp only [Bool.or_eq_true, Bool.and_eq_true, ninfo_isZ, beq_iff_eq] at h1
          rcases h1 with h1 | h1
          · exact Or.inr (Or.inl ⟨h1.1, Or.inl h1.2⟩)
          · exact Or.inr (Or.inr ⟨h1.1, Or.inl h1.2⟩)
        · split at hv
          · split at hv <;> simp only [Option.some.injEq] at hv <;> omega
          · split at hv
            · right
              rename_i he
              simp only [Bool.and_eq_true, Bool.or_eq_true, ninfo_isS _ 1 (by decide), ninfo_isS _ 4 (by decide)] at he
              rcases he with ⟨rfl | rfl, rfl | rfl⟩ <;> decide
            · cases hv

theorem four_exceptions (p : ℕ × ℕ) (hp : p ∈ [(1,1),(1,4),(4,1),(4,4)]) :
    sg (board p.1 p.2) = 1 ∧ ¬ InR_one p.1 p.2 := by
  have e (a b : ℕ) (hv : cval [a,b] = some 1) : sg (board a b) = 1 := by
    rw [board_eq_ofGaps]
    exact thmA canonOK_checked [a,b] 1 hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> exact ⟨e _ _ (by decide), by unfold InR_one; decide⟩

/-- The gap-length formulation explicitly requested in the pre-Lean review. -/
theorem conj_5_1 :
    (∀ n, sg (emptyBoard n) ≤ 1 → InR_empty n) ∧
    (∀ a b, sg (board a b) ≤ 1 → InR_one a b ∨ (a,b) ∈ [(1,1),(1,4),(4,1),(4,4)]) ∧
    (∀ p ∈ [(1,1),(1,4),(4,1),(4,4)], sg (board p.1 p.2) ≤ 1 ∧ ¬ InR_one p.1 p.2) := by
  refine ⟨?_, fun _ _ h => low_single h, ?_⟩
  · intro n _
    unfold InR_empty chi1
    split <;> simp
  · intro p hp
    exact ⟨(four_exceptions p hp).1.le, (four_exceptions p hp).2⟩

/-- Conjecture 5.1 with literal cell lists and the complete source regular set. -/
theorem conjecture_5_1 : Conjecture51 := by
  constructor
  · intro s hcount hsg
    rcases at_most_one hcount with ⟨a, rfl⟩ | ⟨a, b, rfl⟩
    · exact Or.inl (empty_regular a)
    · rcases low_single hsg with hr | he
      · exact Or.inl ((inR_board_iff a b).mpr hr)
      · right
        simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at he
        rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  · intro s hs
    change s ∈ [(1,1),(1,4),(4,1),(4,4)].map (fun p : ℕ × ℕ => board p.1 p.2) at hs
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs
    obtain ⟨hsg, hr⟩ := four_exceptions p hp
    exact ⟨(count_board p.1 p.2).le, hsg.le, mt (inR_board_iff p.1 p.2).mp hr⟩

#print axioms conj_5_1
#print axioms conjecture_5_1

end ITB
```

