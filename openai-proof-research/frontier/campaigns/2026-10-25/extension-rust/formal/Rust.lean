import Mathlib

namespace RustCounterexample
open Finset
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- A finite, computable least-excluded integer. -/
def holes (s : Finset ℕ) : Finset ℕ := (range (s.sup id + 2)).filter fun n => n ∉ s

theorem holes_nonempty (s : Finset ℕ) : (holes s).Nonempty := by
  refine ⟨s.sup id + 1, ?_⟩
  simp only [holes, mem_filter, mem_range]
  constructor
  · omega
  · intro h
    have hh := le_sup (f := id) h
    dsimp at hh
    omega

def mex (s : Finset ℕ) : ℕ := (holes s).min' (holes_nonempty s)

theorem mex_not_mem (s : Finset ℕ) : mex s ∉ s := by
  have h := min'_mem (holes s) (holes_nonempty s)
  exact (mem_filter.mp h).2

theorem mex_le (s : Finset ℕ) {n : ℕ} (hn : n ∉ s) : mex s ≤ n := by
  by_cases hb : n < s.sup id + 2
  · exact min'_le (holes s) n (by simp [holes, hb, hn])
  · have h := (mem_range.mp (mem_filter.mp (min'_mem (holes s) (holes_nonempty s))).1)
    change mex s < s.sup id + 2 at h
    omega

theorem mem_of_lt_mex (s : Finset ℕ) {n : ℕ} (hn : n < mex s) : n ∈ s := by
  by_contra h
  have hh := mex_le s h
  omega

abbrev State := Finset ℕ × Finset ℕ

def nextPair (s : State) : ℕ × ℕ :=
  let x := mex s.1
  let d := mex (s.2 ∪ s.1.image (fun u => u-x))
  (x,x+d)

def advance (s : State) : State :=
  let p := nextPair s
  (insert p.1 (insert p.2 s.1), insert (p.2-p.1) (insert (p.2+p.1) s.2))

def state : ℕ → State
  | 0 => ({0},{0})
  | n+1 => advance (state n)

def pair : ℕ → ℕ × ℕ
  | 0 => (0,0)
  | n+1 => nextPair (state n)

def X (n : ℕ) : ℕ := (pair n).1

def Y (n : ℕ) : ℕ := (pair n).2

def Admissible (U D : Finset ℕ) (x y : ℕ) : Prop :=
  0 < x ∧ x < y ∧ x ∉ U ∧ y ∉ U ∧ y-x ∉ D

def LeastPair (U D : Finset ℕ) (x y : ℕ) : Prop :=
  Admissible U D x y ∧ ∀ u v, Admissible U D u v → x ≤ u ∧ (u=x → y ≤ v)

theorem nextPair_least (U D : Finset ℕ) (hU : 0 ∈ U) (hD : 0 ∈ D) :
    LeastPair U D (nextPair (U,D)).1 (nextPair (U,D)).2 := by
  let x := mex U
  let E := D ∪ U.image (fun u => u-x)
  let d := mex E
  have hx : x ∉ U := mex_not_mem U
  have hd : d ∉ E := mex_not_mem E
  have hxpos : 0 < x := by
    by_contra h
    have : x=0 := by omega
    exact hx (this ▸ hU)
  have hdpos : 0 < d := by
    by_contra h
    have : d=0 := by omega
    apply hd
    simp [this, E, hD]
  have hdD : d ∉ D := by intro h; exact hd (mem_union_left _ h)
  have hy : x+d ∉ U := by
    intro h
    apply hd
    apply mem_union_right
    exact mem_image.mpr ⟨x+d,h,by omega⟩
  change LeastPair U D x (x+d)
  refine ⟨⟨hxpos,by omega,hx,hy,by simpa using hdD⟩,?_⟩
  intro u v hv
  refine ⟨mex_le U hv.2.2.1,?_⟩
  intro hu
  subst u
  have he : v-x ∉ E := by
    intro h
    rcases mem_union.mp h with h | h
    · exact hv.2.2.2.2 h
    · obtain ⟨w,hw,he⟩ := mem_image.mp h
      change w-x = v-x at he
      have hvx : x<v := hv.2.1
      have : w=v := by omega
      exact hv.2.2.2.1 (this ▸ hw)
  have hh := mex_le E he
  change d ≤ v-x at hh
  omega

theorem leastPair_unique {U D : Finset ℕ} {x y u v : ℕ}
    (h : LeastPair U D x y) (h' : LeastPair U D u v) : x=u ∧ y=v := by
  have hxu := (h.2 u v h'.1).1
  have hux := (h'.2 x y h.1).1
  have he : x=u := by omega
  have hyv := (h.2 u v h'.1).2 he.symm
  have hvy := (h'.2 x y h.1).2 he
  exact ⟨he,by omega⟩

def usedHistory (F G : ℕ → ℕ) (n : ℕ) : Finset ℕ :=
  (range (n+1)).image F ∪ (range (n+1)).image G

def differenceHistory (F G : ℕ → ℕ) (n : ℕ) : Finset ℕ :=
  (range (n+1)).image (fun k => G k-F k) ∪
    (range (n+1)).image (fun k => G k+F k)

theorem state_successor (n : ℕ) :
    state (n+1) =
    (insert (X (n+1)) (insert (Y (n+1)) (state n).1),
     insert (Y (n+1)-X (n+1)) (insert (Y (n+1)+X (n+1)) (state n).2)) := rfl

theorem state_history (n : ℕ) :
    (state n).1 = usedHistory X Y n ∧ (state n).2 = differenceHistory X Y n := by
  induction n with
  | zero => simp [state,usedHistory,differenceHistory,X,Y,pair]
  | succ n ih =>
    rw [state_successor]
    dsimp only
    rw [ih.1,ih.2]
    constructor <;>
      simp only [usedHistory,differenceHistory,range_add_one,image_insert]
    all_goals ext k; simp only [mem_insert,mem_union]; tauto

theorem histories_zero (n : ℕ) :
    0 ∈ usedHistory X Y n ∧ 0 ∈ differenceHistory X Y n := by
  constructor
  · apply mem_union_left
    exact mem_image.mpr ⟨0,by simp,by rfl⟩
  · apply mem_union_left
    exact mem_image.mpr ⟨0,by simp,by rfl⟩

def SourceRule (F G : ℕ → ℕ) : Prop :=
  F 0=0 ∧ G 0=0 ∧ ∀ n, LeastPair (usedHistory F G n) (differenceHistory F G n)
    (F (n+1)) (G (n+1))

theorem actual_source_rule : SourceRule X Y := by
  refine ⟨rfl,rfl,?_⟩
  intro n
  have h := nextPair_least (state n).1 (state n).2
    (by rw [(state_history n).1]; exact (histories_zero n).1)
    (by rw [(state_history n).2]; exact (histories_zero n).2)
  change LeastPair (usedHistory X Y n) (differenceHistory X Y n)
    (nextPair (state n)).1 (nextPair (state n)).2
  rw [← (state_history n).1,← (state_history n).2]
  exact h

theorem source_rule_unique (F G : ℕ → ℕ) (h : SourceRule F G) :
    ∀ n, F n = X n ∧ G n = Y n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact ⟨h.1,h.2.1⟩
    | succ k =>
      have hU : usedHistory F G k = usedHistory X Y k := by
        unfold usedHistory
        have hF : (range (k+1)).image F = (range (k+1)).image X := by
          apply image_congr
          intro i hi
          exact (ih i (mem_range.mp hi)).1
        have hG : (range (k+1)).image G = (range (k+1)).image Y := by
          apply image_congr
          intro i hi
          exact (ih i (mem_range.mp hi)).2
        rw [hF,hG]
      have hD : differenceHistory F G k = differenceHistory X Y k := by
        unfold differenceHistory
        have hd : (range (k+1)).image (fun i => G i-F i) =
            (range (k+1)).image (fun i => Y i-X i) := by
          apply image_congr
          intro i hi
          dsimp only
          rw [(ih i (mem_range.mp hi)).1,(ih i (mem_range.mp hi)).2]
        have hs : (range (k+1)).image (fun i => G i+F i) =
            (range (k+1)).image (fun i => Y i+X i) := by
          apply image_congr
          intro i hi
          dsimp only
          rw [(ih i (mem_range.mp hi)).1,(ih i (mem_range.mp hi)).2]
        rw [hd,hs]
      have hh := h.2.2 k
      rw [hU,hD] at hh
      exact leastPair_unique hh (actual_source_rule.2.2 k)

theorem initial_values : X 0=0 ∧ Y 0=0 ∧ X 1=1 ∧ Y 1=2 := by decide

def positiveUsedHistory (n : ℕ) : Finset ℕ :=
  (Icc 1 n).image X ∪ (Icc 1 n).image Y

def positiveDifferenceHistory (n : ℕ) : Finset ℕ :=
  (Icc 1 n).image (fun k => Y k-X k) ∪
    (Icc 1 n).image (fun k => Y k+X k)

theorem range_with_origin (n : ℕ) : range (n+1) = insert 0 (Icc 1 n) := by
  ext k
  simp only [mem_range,mem_insert,mem_Icc]
  omega

theorem histories_with_origin (n : ℕ) :
    usedHistory X Y n = insert 0 (positiveUsedHistory n) ∧
    differenceHistory X Y n = insert 0 (positiveDifferenceHistory n) := by
  have hx := initial_values.1
  have hy := initial_values.2.1
  constructor
  · simp [usedHistory,positiveUsedHistory,range_with_origin,hx,hy]
  · simp [differenceHistory,positiveDifferenceHistory,range_with_origin,hx,hy]

theorem admissible_insert_origin (U D : Finset ℕ) (x y : ℕ) :
    Admissible (insert 0 U) (insert 0 D) x y ↔ Admissible U D x y := by
  simp only [Admissible,mem_insert,not_or]
  constructor
  · rintro ⟨hx,hxy,⟨_,hxu⟩,⟨_,hyu⟩,⟨_,hdd⟩⟩
    exact ⟨hx,hxy,hxu,hyu,hdd⟩
  · rintro ⟨hx,hxy,hxu,hyu,hdd⟩
    exact ⟨hx,hxy,⟨by omega,hxu⟩,⟨by omega,hyu⟩,⟨by omega,hdd⟩⟩

theorem leastPair_insert_origin (U D : Finset ℕ) (x y : ℕ) :
    LeastPair (insert 0 U) (insert 0 D) x y ↔ LeastPair U D x y := by
  simp only [LeastPair,admissible_insert_origin]

theorem original_definition_bridge :
    (X 0=0 ∧ Y 0=0 ∧ X 1=1 ∧ Y 1=2) ∧
    ∀ n, 1 ≤ n → LeastPair (positiveUsedHistory n) (positiveDifferenceHistory n)
      (X (n+1)) (Y (n+1)) := by
  refine ⟨initial_values,?_⟩
  intro n _
  have h := actual_source_rule.2.2 n
  rw [(histories_with_origin n).1,(histories_with_origin n).2] at h
  exact (leastPair_insert_origin _ _ _ _).mp h

theorem exact_values : X 20 = 30 ∧ Y 20 = 56 ∧ X 56 = 86 ∧ Y 30 = 84 := by
  decide

theorem rust_counterexample :
    SourceRule X Y ∧ (X 0=0 ∧ Y 0=0 ∧ X 1=1 ∧ Y 1=2) ∧ 1 ≤ (20 : ℕ) ∧
    X (Y 20) + Y (X 20) ≠ 2*X 20+2*Y 20-1 := by
  obtain ⟨hx,hy,hxy,hyx⟩ := exact_values
  refine ⟨actual_source_rule,initial_values,by norm_num,?_⟩
  rw [hx,hy,hxy,hyx]
  norm_num

end RustCounterexample
