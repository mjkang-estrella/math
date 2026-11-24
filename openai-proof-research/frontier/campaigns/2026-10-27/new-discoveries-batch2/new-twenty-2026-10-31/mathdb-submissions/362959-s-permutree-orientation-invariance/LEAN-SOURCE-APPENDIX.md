# Lean source appendix for MathDB 362959

### `SArc.lean`

```lean
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Logic.Function.Basic

namespace Permutree

variable {n : ℕ}

def between (i j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun h => i < h ∧ h < j

@[simp] theorem mem_between {i j h : Fin n} : h ∈ between i j ↔ i < h ∧ h < j := by
  simp [between]

def positiveInterior (s : Fin n → ℕ) (i j : Fin n) : Finset (Fin n) :=
  (between i j).filter fun h => s h ≠ 0

@[simp] theorem mem_positiveInterior {s : Fin n → ℕ} {i j h : Fin n} :
    h ∈ positiveInterior s i j ↔ i < h ∧ h < j ∧ s h ≠ 0 := by
  simp [positiveInterior, and_assoc]

/-- The set of points passed on the left is recovered from the partition in Definition 46. -/
structure SArc (s : Fin n → ℕ) where
  start : Fin n
  finish : Fin n
  right : Finset (Fin n)
  label : Fin (s start)
  start_lt_finish : start < finish
  right_subset : right ⊆ positiveInterior s start finish

namespace SArc

variable {s : Fin n → ℕ}

def r (a : SArc s) : ℕ := a.label.val + 1

def left (a : SArc s) : Finset (Fin n) :=
  positiveInterior s a.start a.finish \ a.right

@[simp] theorem mem_left {a : SArc s} {h : Fin n} :
    h ∈ a.left ↔ h ∈ positiveInterior s a.start a.finish ∧ h ∉ a.right :=
  Finset.mem_sdiff

theorem start_pos (a : SArc s) : s a.start ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt a.label.isLt)

@[simp] theorem right_union_left (a : SArc s) :
    a.right ∪ a.left = positiveInterior s a.start a.finish := by
  ext h
  by_cases hh : h ∈ a.right
  · simp [hh, a.right_subset hh]
  · simp [hh]

theorem right_disjoint_left (a : SArc s) : Disjoint a.right a.left := by
  simp [left, Finset.disjoint_sdiff]

instance : Finite (SArc s) := by
  refine Finite.of_injective
    (fun a : SArc s => ((⟨a.start, a.label⟩, a.finish, a.right) :
      (Σ i, Fin (s i)) × Fin n × Finset (Fin n))) ?_
  rintro ⟨i,j,A,r,h,hA⟩ ⟨i',j',A',r',h',hA'⟩ e
  obtain ⟨e₁,e₂₃⟩ := Prod.mk.inj e
  obtain ⟨e₂,e₃⟩ := Prod.mk.inj e₂₃
  obtain ⟨ei,er⟩ := Sigma.mk.inj_iff.mp e₁
  change i = i' at ei
  change j = j' at e₂
  change A = A' at e₃
  subst i' j' A'
  cases er
  rfl

noncomputable instance : Fintype (SArc s) := Fintype.ofFinite _

def key (a : SArc s) : Σ i, Fin (s i) := ⟨a.start, a.label⟩

/-- Definition 55 with ends in increasing order. -/
def orderedNoncrossing (a b : SArc s) : Prop :=
  let aRight := a.right ∩ between b.start b.finish
  let bRight := b.right ∩ between a.start a.finish
  a.finish < b.finish ∧
    (a.finish ≤ b.start ∨
     (a.start < b.start ∧ b.start < a.finish ∧ b.start ∈ a.right ∧
       a.finish ∉ b.right ∧ bRight ⊆ aRight) ∨
     (a.start < b.start ∧ b.start < a.finish ∧ b.start ∈ a.left ∧
       a.finish ∉ b.left ∧ aRight ⊆ bRight) ∨
     (a.start = b.start ∧ a.r < b.r ∧ a.finish ∉ b.right ∧ bRight ⊆ aRight) ∨
     (a.start = b.start ∧ a.r = b.r ∧ s a.finish = 0 ∧ bRight = aRight) ∨
     (a.start = b.start ∧ b.r < a.r ∧ a.finish ∉ b.left ∧ aRight ⊆ bRight) ∨
     (b.start < a.start ∧ a.start ∈ b.right ∧ a.finish ∉ b.left ∧ aRight ⊆ bRight) ∨
     (b.start < a.start ∧ a.start ∈ b.left ∧ a.finish ∉ b.right ∧ bRight ⊆ aRight))

def Noncrossing (a b : SArc s) : Prop := a.orderedNoncrossing b ∨ b.orderedNoncrossing a

theorem noncrossing_symm {a b : SArc s} : a.Noncrossing b → b.Noncrossing a := Or.symm

theorem finish_ne_of_noncrossing {a b : SArc s} (h : a.Noncrossing b) :
    a.finish ≠ b.finish := h.elim (fun h => h.1.ne) (fun h => h.1.ne.symm)

end SArc

inductive Deco
  | none | up | down | updown
  deriving DecidableEq

abbrev Decoration (s : Fin n → ℕ) := {i // s i ≠ 0} → Deco

def Deco.allowsRight (d : Deco) : Prop := d ≠ .up ∧ d ≠ .updown

def Deco.allowsLeft (d : Deco) : Prop := d ≠ .down ∧ d ≠ .updown

def Allowed {s : Fin n → ℕ} (d : Decoration s) (a : SArc s) : Prop :=
  ∀ h : {i // s i ≠ 0},
    (h.val ∈ a.right → (d h).allowsRight) ∧ (h.val ∈ a.left → (d h).allowsLeft)

def IsDiagram {s : Fin n → ℕ} (d : Decoration s) (D : Finset (SArc s)) : Prop :=
  (∀ a ∈ D, Allowed d a) ∧ (D : Set (SArc s)).Pairwise SArc.Noncrossing

def DiagramOfSize {s : Fin n → ℕ} (d : Decoration s) (m : ℕ) :=
  {D : Finset (SArc s) // IsDiagram d D ∧ D.card = m}

noncomputable instance {s : Fin n → ℕ} (d : Decoration s) (m : ℕ) :
    Fintype (DiagramOfSize d m) := by
  classical
  unfold DiagramOfSize
  infer_instance

#print axioms SArc.right_union_left
#print axioms SArc.finish_ne_of_noncrossing

end Permutree
```

### `SweepCode.lean`

```lean
import SArc

namespace Permutree

/-- A cut in the list remaining after any end has been removed. -/
def Placement (d : Deco) (through : ℕ) :=
  {p : Fin (through + 1) //
    (0 < p.val → d.allowsLeft) ∧ (p.val < through → d.allowsRight)}

noncomputable instance (d : Deco) (b : ℕ) : Fintype (Placement d b) := by
  classical
  unfold Placement
  infer_instance

/-- The leftmost cut and the rightmost cut are interchanged. -/
def Placement.flip (b : ℕ) : Placement .up b ≃ Placement .down b where
  toFun _ := ⟨0, by simp [Deco.allowsRight]⟩
  invFun _ := ⟨⟨b, Nat.lt_succ_self b⟩, by simp [Deco.allowsLeft]⟩
  left_inv p := by
    apply Subtype.ext
    apply Fin.ext
    exact le_antisymm (le_of_not_gt (fun h => (p.property.2 h).1 rfl)) (Nat.le_of_lt_succ p.val.isLt)
  right_inv p := by
    apply Subtype.ext
    apply Fin.ext
    exact (Nat.eq_zero_of_not_pos (fun h => (p.property.1 h).1 rfl)).symm

abbrev Level := ℕ × Deco

/-- The end flag and mark flag cannot both be set. An end needs an active entry,
and a mark also needs an active entry and a zero level. -/
def Event (level : Level) (active : ℕ) :=
  {flags : Bool × Bool //
    (flags.1 = true → 0 < active) ∧
    (flags.2 = true → 0 < active ∧ level.1 = 0 ∧ flags.1 = false)}

noncomputable instance (l : Level) (b : ℕ) : Fintype (Event l b) := by
  classical
  unfold Event
  infer_instance

namespace Event

variable {l : Level} {b : ℕ}

def through (e : Event l b) : ℕ := b - e.val.1.toNat

def weight (e : Event l b) : ℕ := e.val.1.toNat + e.val.2.toNat

/-- At a positive level the cut determines the chosen gap or ending entry.
At zero, an end or mark chooses an old entry and no event has a unique choice. -/
def Choice (e : Event l b) : Type :=
  if l.1 = 0 then
    Fin (if e.val.1 || e.val.2 then b else 1)
  else
    Placement l.2 e.through

noncomputable instance (e : Event l b) : Fintype e.Choice := by
  unfold Choice
  split <;> infer_instance

end Event

/-- Complete sweeps indexed by the number of active entries initially and the
number of ends plus marks. Finite subsets select the starting labels. -/
def Sweep : List Level → ℕ → ℕ → Type
  | [], b, m => {_u : Unit // b = 0 ∧ m = 0}
  | l :: ls, b, m =>
      Σ e : Event l b, e.Choice ×
        (Σ starts : Finset (Fin l.1),
         {_u : Sweep ls (e.through + starts.card) (m - e.weight) // e.weight ≤ m})

noncomputable instance sweepFintype (ls : List Level) (b m : ℕ) :
    Fintype (Sweep ls b m) := by
  classical
  induction ls generalizing b m with
  | nil =>
    unfold Sweep
    infer_instance
  | cons l ls ih =>
    unfold Sweep
    letI (b m : ℕ) := ih b m
    infer_instance

def Switch (a b : Level) : Prop :=
  a.1 = b.1 ∧ (a.2 = b.2 ∨ a.2 = .up ∧ b.2 = .down)

def eventEquiv (s b : ℕ) (d d' : Deco) : Event (s,d) b ≃ Event (s,d') b := Equiv.refl _

theorem choiceEquiv {s b : ℕ} {d d' : Deco} (h : d = d' ∨ d = .up ∧ d' = .down)
    (e : Event (s,d) b) : Nonempty (e.Choice ≃ ((eventEquiv s b d d') e).Choice) := by
  rcases h with rfl | ⟨rfl, rfl⟩
  · exact ⟨Equiv.refl _⟩
  · apply Nonempty.intro
    change (if s = 0 then Fin (if e.val.1 || e.val.2 then b else 1)
      else Placement .up e.through) ≃
      (if s = 0 then Fin (if e.val.1 || e.val.2 then b else 1)
      else Placement .down e.through)
    split
    · exact Equiv.refl _
    · exact Placement.flip _

theorem sweepEquiv {ls ls' : List Level} (h : List.Forall₂ Switch ls ls') (b m : ℕ) :
    Nonempty (Sweep ls b m ≃ Sweep ls' b m) := by
  induction h generalizing b m with
  | nil => exact ⟨Equiv.refl _⟩
  | @cons l l' ls ls' hl _ ih =>
    obtain ⟨s,d⟩ := l
    obtain ⟨s',d'⟩ := l'
    obtain ⟨hs,hd⟩ := hl
    change s = s' at hs
    subst s'
    change d = d' ∨ d = .up ∧ d' = .down at hd
    refine ⟨Equiv.sigmaCongr (eventEquiv s b d d') fun e =>
      Equiv.prodCongr (Classical.choice (choiceEquiv hd e)) ?_⟩
    refine Equiv.sigmaCongrRight fun starts => ?_
    exact (Classical.choice (ih _ _)).subtypeEquiv fun _ => Iff.rfl

theorem sweep_card_invariance {ls ls' : List Level} (h : List.Forall₂ Switch ls ls') (m : ℕ) :
    Fintype.card (Sweep ls 0 m) = Fintype.card (Sweep ls' 0 m) :=
  Fintype.card_congr (Classical.choice (sweepEquiv h 0 m))

def levels {n : ℕ} {s : Fin n → ℕ} (d : Decoration s) : List Level :=
  List.ofFn (fun i => (s i, if hi : s i ≠ 0 then d ⟨i,hi⟩ else .none))

private theorem forall₂_ofFn {n : ℕ} {f g : Fin n → Level}
    (h : ∀ i, Switch (f i) (g i)) : List.Forall₂ Switch (List.ofFn f) (List.ofFn g) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    exact .cons (h 0) (ih (fun i => h i.succ))

theorem levels_switch {n : ℕ} {s : Fin n → ℕ} (d : Decoration s)
    (k : {i // s i ≠ 0}) (hk : d k = .up) :
    List.Forall₂ Switch (levels d) (levels (Function.update d k .down)) := by
  unfold levels
  apply forall₂_ofFn
  intro i
  refine ⟨rfl, ?_⟩
  by_cases hi : s i ≠ 0
  · simp only [dite_eq_left hi]
    by_cases e : (⟨i,hi⟩ : {i // s i ≠ 0}) = k
    · exact Or.inr ⟨e ▸ hk, by simp [e]⟩
    · exact Or.inl (by simp [Function.update_of_ne e])
  · simp [hi]

theorem up_to_down_sweep_card {n : ℕ} {s : Fin n → ℕ} (d : Decoration s)
    (k : {i // s i ≠ 0}) (hk : d k = .up) (m : ℕ) :
    Fintype.card (Sweep (levels d) 0 m) =
      Fintype.card (Sweep (levels (Function.update d k .down)) 0 m) :=
  sweep_card_invariance (levels_switch d k hk) m

#check up_to_down_sweep_card
#print axioms up_to_down_sweep_card

end Permutree
```

### `ArcCompatibility.lean`

```lean
import SArc

namespace Permutree.SArc

variable {n : ℕ} {s : Fin n → ℕ}

def SameKey (a b : SArc s) : Prop := a.start = b.start ∧ a.r = b.r

theorem sameKey_iff_key_eq {a b : SArc s} : a.SameKey b ↔ a.key = b.key := by
  cases a with
  | mk i j A r h hA =>
    cases b with
    | mk i' j' A' r' h' hA' =>
      constructor
      · rintro ⟨e, er⟩
        change i = i' at e
        subst i'
        exact congrArg (Sigma.mk i) (Fin.ext (Nat.add_right_cancel er))
      · intro e
        obtain ⟨ei, er⟩ := Sigma.mk.inj_iff.mp e
        change i = i' at ei
        subst i'
        cases er
        exact ⟨rfl, rfl⟩

/-- The order in the overlap is determined when the later of the two keys starts. -/
def LeftOf (a b : SArc s) : Prop :=
  (a.start < b.start ∧ b.start ∈ a.left) ∨
  (a.start = b.start ∧ b.r < a.r) ∨
  (b.start < a.start ∧ a.start ∈ b.right)

def InBoth (a b : SArc s) (h : Fin n) : Prop :=
  h ∈ between a.start a.finish ∧ h ∈ between b.start b.finish

def SideIncl (a b : SArc s) : Prop :=
  ∀ h, a.InBoth b h → h ∈ a.right → h ∈ b.right

theorem sideIncl_iff_subset (a b : SArc s) :
    a.SideIncl b ↔ a.right ∩ between b.start b.finish ⊆
      b.right ∩ between a.start a.finish := by
  constructor
  · intro h i hi
    rw [Finset.mem_inter] at hi ⊢
    have hr := mem_positiveInterior.mp (a.right_subset hi.1)
    have ha : i ∈ between a.start a.finish := mem_between.mpr ⟨hr.1, hr.2.1⟩
    exact ⟨h i ⟨ha, hi.2⟩ hi.1, ha⟩
  · intro h i hi hr
    exact (Finset.mem_inter.mp (h (Finset.mem_inter.mpr ⟨hr, hi.2⟩))).1

theorem leftOf_trichotomy {a b : SArc s}
    (hab : a.start < b.finish) (hba : b.start < a.finish) :
    a.LeftOf b ∨ a.SameKey b ∨ b.LeftOf a := by
  rcases lt_trichotomy a.start b.start with h | h | h
  · by_cases hr : b.start ∈ a.right
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h,hr⟩)))
    · exact Or.inl (Or.inl ⟨h, mem_left.mpr ⟨
        mem_positiveInterior.mpr ⟨h, hba, b.start_pos⟩, hr⟩⟩)
  · rcases lt_trichotomy a.r b.r with hr | hr | hr
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.symm,hr⟩)))
    · exact Or.inr (Or.inl ⟨h,hr⟩)
    · exact Or.inl (Or.inr (Or.inl ⟨h,hr⟩))
  · by_cases hr : a.start ∈ b.right
    · exact Or.inl (Or.inr (Or.inr ⟨h,hr⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨h, mem_left.mpr ⟨
        mem_positiveInterior.mpr ⟨h, hab, a.start_pos⟩, hr⟩⟩))

theorem leftOf_exclusive {a b : SArc s} (h : a.LeftOf b) : ¬ b.LeftOf a := by
  intro h'
  have disjA : ∀ i, i ∈ a.left → i ∉ a.right := fun _ hi => (mem_left.mp hi).2
  have disjB : ∀ i, i ∈ b.left → i ∉ b.right := fun _ hi => (mem_left.mp hi).2
  rcases h with h | h | h <;> rcases h' with h' | h' | h'
  all_goals first | exact disjA _ h.2 h'.2 | exact disjB _ h'.2 h.2 | omega

theorem not_sameKey_of_leftOf {a b : SArc s} (h : a.LeftOf b) : ¬ a.SameKey b := by
  rintro ⟨hi, hr⟩
  rcases h with h | h | h <;> omega

/-- The sweep compatibility test for arcs whose ends are in increasing order. -/
theorem orderedNoncrossing_iff (a b : SArc s) :
    a.orderedNoncrossing b ↔
      a.finish < b.finish ∧
        (a.finish ≤ b.start ∨
        (b.LeftOf a ∧ b.SideIncl a ∧ a.finish ∉ b.right) ∨
        (a.LeftOf b ∧ a.SideIncl b ∧ a.finish ∉ b.left) ∨
        (a.SameKey b ∧ s a.finish = 0 ∧ b.SideIncl a ∧ a.SideIncl b)) := by
  rw [sideIncl_iff_subset b a, sideIncl_iff_subset a b]
  constructor
  · rintro ⟨e, h | h | h | h | h | h | h | h⟩
    · exact ⟨e, Or.inl h⟩
    · exact ⟨e, Or.inr (Or.inl ⟨Or.inr (Or.inr ⟨h.1,h.2.2.1⟩),h.2.2.2.2,h.2.2.2.1⟩)⟩
    · exact ⟨e, Or.inr (Or.inr (Or.inl ⟨Or.inl ⟨h.1,h.2.2.1⟩,h.2.2.2.2,h.2.2.2.1⟩))⟩
    · exact ⟨e, Or.inr (Or.inl ⟨Or.inr (Or.inl ⟨h.1.symm,h.2.1⟩),h.2.2.2,h.2.2.1⟩)⟩
    · exact ⟨e, Or.inr (Or.inr (Or.inr ⟨⟨h.1,h.2.1⟩,h.2.2.1,
        h.2.2.2.le, h.2.2.2.ge⟩))⟩
    · exact ⟨e, Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inl ⟨h.1,h.2.1⟩),h.2.2.2,h.2.2.1⟩))⟩
    · exact ⟨e, Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inr ⟨h.1,h.2.1⟩),h.2.2.2,h.2.2.1⟩))⟩
    · exact ⟨e, Or.inr (Or.inl ⟨Or.inl ⟨h.1,h.2.1⟩,h.2.2.2,h.2.2.1⟩)⟩
  · rintro ⟨e, h | ⟨hl, hs, he⟩ | ⟨hl, hs, he⟩ | ⟨⟨hi,hr⟩, hz, h₁, h₂⟩⟩
    · exact ⟨e, Or.inl h⟩
    · rcases hl with hl | hl | hl
      · exact ⟨e, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hl.1,hl.2,he,hs⟩))))))⟩
      · exact ⟨e, Or.inr (Or.inr (Or.inr (Or.inl ⟨hl.1.symm,hl.2,he,hs⟩)))⟩
      · have hstart := (mem_positiveInterior.mp (a.right_subset hl.2)).2.1
        exact ⟨e, Or.inr (Or.inl ⟨hl.1,hstart,hl.2,he,hs⟩)⟩
    · rcases hl with hl | hl | hl
      · have hstart := (mem_positiveInterior.mp (mem_left.mp hl.2).1).2.1
        exact ⟨e, Or.inr (Or.inr (Or.inl ⟨hl.1,hstart,hl.2,he,hs⟩))⟩
      · exact ⟨e, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hl.1,hl.2,he,hs⟩)))))⟩
      · exact ⟨e, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hl.1,hl.2,he,hs⟩))))))⟩
    · exact ⟨e, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hi,hr,hz,Finset.Subset.antisymm h₁ h₂⟩))))⟩

theorem ordered_of_noncrossing_of_lt {a b : SArc s} (h : a.Noncrossing b)
    (he : a.finish < b.finish) : a.orderedNoncrossing b :=
  h.elim id (fun h => (lt_asymm he h.1).elim)

theorem sameKey_earlier_end {a b : SArc s} (h : a.Noncrossing b)
    (he : a.finish < b.finish) (hk : a.SameKey b) :
    s a.finish = 0 ∧ b.SideIncl a ∧ a.SideIncl b := by
  rcases ((orderedNoncrossing_iff a b).mp (ordered_of_noncrossing_of_lt h he)).2 with
    h | ⟨h, _, _⟩ | ⟨h, _, _⟩ | ⟨_, h⟩
  · have := a.start_lt_finish
    have := hk.1
    omega
  · exact (not_sameKey_of_leftOf h ⟨hk.1.symm,hk.2.symm⟩).elim
  · exact (not_sameKey_of_leftOf h hk).elim
  · exact h

#print axioms orderedNoncrossing_iff
#print axioms sameKey_earlier_end

end Permutree.SArc
```

### `ArcShortening.lean`

```lean
import ArcCompatibility

namespace Permutree.SArc

variable {n : ℕ} {s : Fin n → ℕ}

/-- Restrict the side assignments to the strict interior of the new end. -/
def shorten (a : SArc s) (j : Fin n) (h : a.start < j) (_hle : j ≤ a.finish) : SArc s where
  start := a.start
  finish := j
  label := a.label
  right := a.right ∩ between a.start j
  start_lt_finish := h
  right_subset := fun h hh => by
    obtain ⟨ha,hj⟩ := Finset.mem_inter.mp hh
    exact mem_positiveInterior.mpr ⟨(mem_between.mp hj).1,(mem_between.mp hj).2,
      (mem_positiveInterior.mp (a.right_subset ha)).2.2⟩

@[simp] theorem shorten_start (a : SArc s) (j : Fin n) (h : a.start < j) (hle : j ≤ a.finish) :
    (a.shorten j h hle).start = a.start := rfl
@[simp] theorem shorten_finish (a : SArc s) (j : Fin n) (h : a.start < j) (hle : j ≤ a.finish) :
    (a.shorten j h hle).finish = j := rfl
@[simp] theorem shorten_r (a : SArc s) (j : Fin n) (h : a.start < j) (hle : j ≤ a.finish) :
    (a.shorten j h hle).r = a.r := rfl

theorem eq_of_key_finish_right {a b : SArc s} (hk : a.SameKey b)
    (hf : a.finish = b.finish) (hr : a.right = b.right) : a = b := by
  cases a with
  | mk i j A r hj hA =>
    cases b with
    | mk i' j' A' r' hj' hA' =>
      have hi : i = i' := hk.1
      change j = j' at hf
      change A = A' at hr
      subst i' j' A'
      have e : r = r' := Fin.ext (Nat.add_right_cancel hk.2)
      cases e
      rfl

@[simp] theorem shorten_self (a : SArc s) :
    a.shorten a.finish a.start_lt_finish le_rfl = a := by
  refine eq_of_key_finish_right (a := a.shorten _ _ _) (b := a) ⟨rfl,rfl⟩ rfl ?_
  apply Finset.inter_eq_left.mpr
  intro i hi
  obtain ⟨h₁,h₂,_⟩ := mem_positiveInterior.mp (a.right_subset hi)
  exact mem_between.mpr ⟨h₁,h₂⟩

@[simp] theorem mem_shorten_right {a : SArc s} {j k : Fin n} {h : a.start < j} {hle : j ≤ a.finish} :
    k ∈ (a.shorten j h hle).right ↔ k ∈ a.right ∧ k < j := by
  constructor
  · intro hk
    exact ⟨(Finset.mem_inter.mp hk).1,(mem_between.mp (Finset.mem_inter.mp hk).2).2⟩
  · rintro ⟨hk,hkj⟩
    exact Finset.mem_inter.mpr ⟨hk,mem_between.mpr ⟨(mem_positiveInterior.mp (a.right_subset hk)).1,hkj⟩⟩

@[simp] theorem mem_shorten_left {a : SArc s} {j k : Fin n} {h : a.start < j} {hle : j ≤ a.finish} :
    k ∈ (a.shorten j h hle).left ↔ k ∈ a.left ∧ k < j := by
  simp only [mem_left, mem_positiveInterior, shorten_start, shorten_finish, mem_shorten_right]
  constructor
  · rintro ⟨⟨h₁,h₂,h₃⟩,hn⟩
    exact ⟨⟨⟨h₁,h₂.trans_le hle,h₃⟩,fun ha => hn ⟨ha,h₂⟩⟩,h₂⟩
  · rintro ⟨⟨⟨h₁,_,h₃⟩,hn⟩,h₂⟩
    exact ⟨⟨h₁,h₂,h₃⟩,fun hc => hn hc.1⟩

theorem allowed_shorten {d : Decoration s} {a : SArc s} (ha : Allowed d a) {j : Fin n}
    (h : a.start < j) (hle : j ≤ a.finish) : Allowed d (a.shorten j h hle) :=
  fun i => ⟨fun hi => (ha i).1 (mem_shorten_right.mp hi).1,
    fun hi => (ha i).2 (mem_shorten_left.mp hi).1⟩

theorem eq_shorten_of_sameKey {a b : SArc s} (h : a.Noncrossing b) (he : a.finish < b.finish)
    (hk : a.SameKey b) :
    a = b.shorten a.finish (hk.1 ▸ a.start_lt_finish) he.le := by
  obtain ⟨_, hba, hab⟩ := sameKey_earlier_end h he hk
  refine eq_of_key_finish_right (a := a) (b := b.shorten _ _ _) hk rfl ?_
  ext k
  rw [mem_shorten_right]
  constructor
  · intro hr
    have ha := mem_positiveInterior.mp (a.right_subset hr)
    have hb : b.start < k := hk.1 ▸ ha.1
    exact ⟨hab k ⟨mem_between.mpr ⟨ha.1,ha.2.1⟩,mem_between.mpr ⟨hb,ha.2.1.trans he⟩⟩ hr,ha.2.1⟩
  · rintro ⟨hr,hj⟩
    have hb := mem_positiveInterior.mp (b.right_subset hr)
    have ha : a.start < k := hk.1.symm ▸ hb.1
    exact hba k ⟨mem_between.mpr ⟨hb.1,hb.2.1⟩,mem_between.mpr ⟨ha,hj⟩⟩ hr

private theorem sideIncl_shorten {a b : SArc s} (hs : a.SideIncl b)
    {i j : Fin n} {hi : a.start < i} {hj : b.start < j}
    {hia : i ≤ a.finish} {hjb : j ≤ b.finish} :
    (a.shorten i hi hia).SideIncl (b.shorten j hj hjb) := by
  intro k hk ha
  obtain ⟨hk₁,hk₂⟩ := hk
  simp only [shorten_start,shorten_finish,mem_between] at hk₁ hk₂
  exact mem_shorten_right.mpr ⟨hs k ⟨mem_between.mpr ⟨hk₁.1,hk₁.2.trans_le hia⟩,
    mem_between.mpr ⟨hk₂.1,hk₂.2.trans_le hjb⟩⟩ (mem_shorten_right.mp ha).1,hk₂.2⟩

private theorem leftOf_shorten {a b : SArc s} (hs : a.LeftOf b)
    {i j : Fin n} {hi : a.start < i} {hj : b.start < j}
    {hia : i ≤ a.finish} {hjb : j ≤ b.finish} (hob : b.start < i) (hoa : a.start < j) :
    (a.shorten i hi hia).LeftOf (b.shorten j hj hjb) := by
  rcases hs with hs | hs | hs
  · exact Or.inl ⟨hs.1,mem_shorten_left.mpr ⟨hs.2,hob⟩⟩
  · exact Or.inr (Or.inl hs)
  · exact Or.inr (Or.inr ⟨hs.1,mem_shorten_right.mpr ⟨hs.2,hoa⟩⟩)

private theorem end_outside_of_zero {a : SArc s} {k : Fin n} (h : s k = 0) :
    k ∉ a.right ∧ k ∉ a.left :=
  ⟨fun ha => (mem_positiveInterior.mp (a.right_subset ha)).2.2 h,
    fun ha => (mem_positiveInterior.mp (mem_left.mp ha).1).2.2 h⟩

theorem noncrossing_shorten_same (a : SArc s) {i j : Fin n}
    (hi : a.start < i) (hj : a.start < j) (hia : i ≤ a.finish) (hja : j ≤ a.finish)
    (hij : i < j) (hz : s i = 0) : (a.shorten i hi hia).Noncrossing (a.shorten j hj hja) := by
  refine Or.inl ((orderedNoncrossing_iff _ _).mpr ⟨hij,Or.inr (Or.inr (Or.inr ?_))⟩)
  have hs : a.SideIncl a := fun _ _ h => h
  exact ⟨⟨rfl,rfl⟩,hz,sideIncl_shorten hs,sideIncl_shorten hs⟩

private theorem shorten_distinct_ordered {a b : SArc s}
    (hab : a.Noncrossing b) (hne : ¬ a.SameKey b)
    {i j : Fin n} (hi : a.start < i) (hj : b.start < j) (hia : i ≤ a.finish) (hjb : j ≤ b.finish)
    (hij : i < j) (hzero : i < a.finish → s i = 0) :
    (a.shorten i hi hia).orderedNoncrossing (b.shorten j hj hjb) := by
  apply (orderedNoncrossing_iff _ _).mpr
  refine ⟨hij,?_⟩
  by_cases hgap : i ≤ b.start
  · exact Or.inl hgap
  have hbi := lt_of_not_ge hgap
  have haj := hi.trans hij
  have needEnd : i = a.finish ∨ s i = 0 :=
    hia.eq_or_lt.imp_right hzero
  have transferLeft (h : b.LeftOf a) (hs : b.SideIncl a)
      (he : i = a.finish → i ∉ b.right) :
      (b.shorten j hj hjb).LeftOf (a.shorten i hi hia) ∧
      (b.shorten j hj hjb).SideIncl (a.shorten i hi hia) ∧ i ∉ (b.shorten j hj hjb).right :=
    ⟨leftOf_shorten h haj hbi,sideIncl_shorten hs,
      fun hr => needEnd.elim (fun h => he h (mem_shorten_right.mp hr).1)
        (fun hz => (end_outside_of_zero hz).1 hr)⟩
  have transferRight (h : a.LeftOf b) (hs : a.SideIncl b)
      (he : i = a.finish → i ∉ b.left) :
      (a.shorten i hi hia).LeftOf (b.shorten j hj hjb) ∧
      (a.shorten i hi hia).SideIncl (b.shorten j hj hjb) ∧ i ∉ (b.shorten j hj hjb).left :=
    ⟨leftOf_shorten h hbi haj,sideIncl_shorten hs,
      fun hr => needEnd.elim (fun h => he h (mem_shorten_left.mp hr).1)
        (fun hz => (end_outside_of_zero hz).2 hr)⟩
  rcases hab with h | h
  · rcases ((orderedNoncrossing_iff _ _).mp h).2 with h | ⟨hl,hs,he⟩ | ⟨hl,hs,he⟩ | ⟨hk,_⟩
    · exact (hbi.not_ge (hia.trans h)).elim
    · exact Or.inr (Or.inl (transferLeft hl hs (fun h => h ▸ he)))
    · exact Or.inr (Or.inr (Or.inl (transferRight hl hs (fun h => h ▸ he))))
    · exact (hne hk).elim
  · have hlt := h.1
    have him : i ≠ a.finish := (hij.trans_le hjb).trans hlt |>.ne
    rcases ((orderedNoncrossing_iff _ _).mp h).2 with h | ⟨hl,hs,_⟩ | ⟨hl,hs,_⟩ | ⟨hk,_⟩
    · exact (haj.not_ge (hjb.trans h)).elim
    · exact Or.inr (Or.inr (Or.inl (transferRight hl hs (fun h => (him h).elim))))
    · exact Or.inr (Or.inl (transferLeft hl hs (fun h => (him h).elim)))
    · exact (hne ⟨hk.1.symm,hk.2.symm⟩).elim

theorem noncrossing_shorten_distinct {a b : SArc s} (hab : a.Noncrossing b) (hne : ¬ a.SameKey b)
    {i j : Fin n} (hi : a.start < i) (hj : b.start < j) (hia : i ≤ a.finish) (hjb : j ≤ b.finish)
    (hij : i ≠ j) (hza : i < a.finish → s i = 0) (hzb : j < b.finish → s j = 0) :
    (a.shorten i hi hia).Noncrossing (b.shorten j hj hjb) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact Or.inl (shorten_distinct_ordered hab hne hi hj hia hjb h hza)
  · exact Or.inr (shorten_distinct_ordered (noncrossing_symm hab)
      (fun hk => hne ⟨hk.1.symm,hk.2.symm⟩) hj hi hjb hia h hzb)

#print axioms eq_shorten_of_sameKey
#print axioms noncrossing_shorten_distinct

end Permutree.SArc
```

### `MarkedDiagrams.lean`

```lean
import ArcShortening
import Mathlib.Data.Finset.Max

namespace Permutree

open SArc

variable {n : ℕ} {s : Fin n → ℕ}

abbrev EndEvent (s : Fin n → ℕ) := SArc s × Fin n

/-- Each arc is present at its own end. A second event on that arc is a
mark strictly inside it at a zero level. -/
def IsMarked (d : Decoration s) (M : Finset (EndEvent s)) : Prop :=
  (∀ e ∈ M, Allowed d e.1 ∧ e.1.start < e.2 ∧ e.2 ≤ e.1.finish ∧
    (e.2 < e.1.finish → s e.2 = 0) ∧ (e.1,e.1.finish) ∈ M) ∧
  (M : Set (EndEvent s)).Pairwise fun a b =>
    a.2 ≠ b.2 ∧ (a.1 ≠ b.1 → a.1.Noncrossing b.1 ∧ a.1.key ≠ b.1.key)

def MarkedOfSize (d : Decoration s) (m : ℕ) :=
  {M : Finset (EndEvent s) // IsMarked d M ∧ M.card = m}

noncomputable instance (d : Decoration s) (m : ℕ) : Fintype (MarkedOfSize d m) := by
  classical
  unfold MarkedOfSize
  infer_instance

private theorem exists_leader (D : Finset (SArc s)) {a : SArc s} (ha : a ∈ D) :
    ∃ b ∈ D, b.key = a.key ∧ ∀ c ∈ D, c.key = a.key → c.finish ≤ b.finish := by
  classical
  let F := D.filter (fun b => b.key = a.key)
  obtain ⟨b,hb,hmax⟩ := Finset.exists_max_image F SArc.finish
    ⟨a,Finset.mem_filter.mpr ⟨ha,rfl⟩⟩
  obtain ⟨hbD,hba⟩ := Finset.mem_filter.mp hb
  exact ⟨b,hbD,hba,fun c hc hca => hmax c (Finset.mem_filter.mpr ⟨hc,hca⟩)⟩

noncomputable def leader (D : Finset (SArc s)) (a : {a // a ∈ D}) : SArc s :=
  (exists_leader D a.property).choose

theorem leader_mem (D : Finset (SArc s)) (a : {a // a ∈ D}) : leader D a ∈ D :=
  (exists_leader D a.property).choose_spec.1

theorem leader_key (D : Finset (SArc s)) (a : {a // a ∈ D}) : (leader D a).key = a.val.key :=
  (exists_leader D a.property).choose_spec.2.1

theorem le_leader_end (D : Finset (SArc s)) (a : {a // a ∈ D})
    {b : SArc s} (hb : b ∈ D) (hk : b.key = a.val.key) : b.finish ≤ (leader D a).finish :=
  (exists_leader D a.property).choose_spec.2.2 b hb hk

theorem diagram_finish_inj {d : Decoration s} {D : Finset (SArc s)} (hD : IsDiagram d D)
    {a b : SArc s} (ha : a ∈ D) (hb : b ∈ D) (he : a.finish = b.finish) : a = b := by
  by_contra hne
  exact (finish_ne_of_noncrossing (hD.2 ha hb hne)) he

theorem leader_eq_of_key {d : Decoration s} {D : Finset (SArc s)} (hD : IsDiagram d D)
    (a b : {a // a ∈ D}) (hk : a.val.key = b.val.key) : leader D a = leader D b := by
  apply diagram_finish_inj hD (leader_mem D a) (leader_mem D b)
  exact le_antisymm (le_leader_end D b (leader_mem D a) ((leader_key D a).trans hk))
    (le_leader_end D a (leader_mem D b) ((leader_key D b).trans hk.symm))

noncomputable def group (D : Finset (SArc s)) : Finset (EndEvent s) := by
  classical
  exact D.attach.image (fun a => (leader D a, a.val.finish))

theorem mem_group {D : Finset (SArc s)} {e : EndEvent s} :
    e ∈ group D ↔ ∃ a : {a // a ∈ D}, (leader D a,a.val.finish) = e := by
  classical
  simp [group]

theorem group_card {d : Decoration s} {D : Finset (SArc s)} (hD : IsDiagram d D) :
    (group D).card = D.card := by
  classical
  rw [group, Finset.card_image_of_injective, Finset.card_attach]
  intro a b h
  exact Subtype.ext (diagram_finish_inj hD a.property b.property (congrArg Prod.snd h))

theorem isMarked_group {d : Decoration s} {D : Finset (SArc s)} (hD : IsDiagram d D) :
    IsMarked d (group D) := by
  constructor
  · intro e he
    obtain ⟨a,rfl⟩ := mem_group.mp he
    have hk := sameKey_iff_key_eq.mpr (leader_key D a)
    have hf := le_leader_end D a a.property rfl
    refine ⟨hD.1 _ (leader_mem D a), hk.1.symm ▸ a.val.start_lt_finish, hf, ?_, ?_⟩
    · intro hlt
      have hne : a.val ≠ leader D a := fun he => hlt.ne (congrArg SArc.finish he)
      exact (sameKey_earlier_end (hD.2 a.property (leader_mem D a) hne) hlt
        ⟨hk.1.symm,hk.2.symm⟩).1
    · exact mem_group.mpr ⟨⟨leader D a,leader_mem D a⟩,by
        rw [leader_eq_of_key hD _ a (leader_key D a)]⟩
  · intro e he f hf hne
    obtain ⟨a,rfl⟩ := mem_group.mp he
    obtain ⟨b,rfl⟩ := mem_group.mp hf
    refine ⟨?_,fun hab => ⟨hD.2 (leader_mem D a) (leader_mem D b) hab,?_⟩⟩
    · intro he
      exact hne (congrArg (fun a : {a // a ∈ D} => (leader D a,a.val.finish))
        (Subtype.ext (diagram_finish_inj hD a.property b.property he)))
    · intro hk
      apply hab
      exact leader_eq_of_key hD a b ((leader_key D a).symm.trans (hk.trans (leader_key D b)))

def restoreEvent {d : Decoration s} {M : Finset (EndEvent s)} (hM : IsMarked d M)
    (e : {e // e ∈ M}) : SArc s :=
  e.val.1.shorten e.val.2 (hM.1 _ e.property).2.1 (hM.1 _ e.property).2.2.1

noncomputable def restore {d : Decoration s} {M : Finset (EndEvent s)} (hM : IsMarked d M) :
    Finset (SArc s) := by
  classical
  exact M.attach.image (restoreEvent hM)

theorem mem_restore {d : Decoration s} {M : Finset (EndEvent s)} {hM : IsMarked d M} {a : SArc s} :
    a ∈ restore hM ↔ ∃ e : {e // e ∈ M}, restoreEvent hM e = a := by
  classical
  simp [restore]

theorem restoreEvent_injective {d : Decoration s} {M : Finset (EndEvent s)}
    (hM : IsMarked d M) : Function.Injective (restoreEvent hM) := by
  intro a b e
  apply Subtype.ext
  by_contra hne
  exact (hM.2 a.property b.property hne).1 (congrArg SArc.finish e)

theorem restore_card {d : Decoration s} {M : Finset (EndEvent s)} (hM : IsMarked d M) :
    (restore hM).card = M.card := by
  classical
  rw [restore,Finset.card_image_of_injective _ (restoreEvent_injective hM),Finset.card_attach]

theorem isDiagram_restore {d : Decoration s} {M : Finset (EndEvent s)} (hM : IsMarked d M) :
    IsDiagram d (restore hM) := by
  constructor
  · intro a ha
    obtain ⟨e,rfl⟩ := mem_restore.mp ha
    exact allowed_shorten (hM.1 _ e.property).1 _ _
  · intro a ha b hb hne
    obtain ⟨⟨⟨a,i⟩,heM⟩,rfl⟩ := mem_restore.mp ha
    obtain ⟨⟨⟨b,j⟩,hfM⟩,rfl⟩ := mem_restore.mp hb
    let e : {e // e ∈ M} := ⟨(a,i),heM⟩
    let f : {e // e ∈ M} := ⟨(b,j),hfM⟩
    have hdiff : e.val ≠ f.val := fun h => hne (congrArg (restoreEvent hM) (Subtype.ext h))
    obtain ⟨hends,hkeys⟩ := hM.2 e.property f.property hdiff
    have he := hM.1 _ e.property
    have hf := hM.1 _ f.property
    unfold restoreEvent
    by_cases hsame : e.val.1 = f.val.1
    · change a = b at hsame
      subst b
      rcases lt_or_gt_of_ne hends with h | h
      · exact noncrossing_shorten_same _ _ _ _ _ h (he.2.2.2.1 (h.trans_le hf.2.2.1))
      · exact noncrossing_symm
          (noncrossing_shorten_same _ _ _ _ _ h (hf.2.2.2.1 (h.trans_le he.2.2.1)))
    · exact noncrossing_shorten_distinct (hkeys hsame).1
        (fun h => (hkeys hsame).2 (sameKey_iff_key_eq.mp h))
        _ _ _ _ hends he.2.2.2.1 hf.2.2.2.1

theorem restore_group {d : Decoration s} {D : Finset (SArc s)} (hD : IsDiagram d D) :
    restore (isMarked_group hD) = D := by
  have event_eq (a : {a // a ∈ D}) :
      restoreEvent (isMarked_group hD) ⟨(leader D a,a.val.finish),mem_group.mpr ⟨a,rfl⟩⟩ = a.val := by
    have he := le_leader_end D a a.property rfl
    rcases he.eq_or_lt with h | h
    · have hEq := diagram_finish_inj hD a.property (leader_mem D a) h
      simp [restoreEvent,← hEq]
    · have hk := sameKey_iff_key_eq.mpr (leader_key D a).symm
      exact (eq_shorten_of_sameKey (hD.2 a.property (leader_mem D a)
        (fun he => h.ne (congrArg SArc.finish he))) h hk).symm
  ext a
  rw [mem_restore]
  constructor
  · rintro ⟨⟨e,he⟩,rfl⟩
    obtain ⟨b,rfl⟩ := mem_group.mp he
    rw [event_eq b]
    exact b.property
  · intro ha
    exact ⟨_,event_eq ⟨a,ha⟩⟩

theorem group_restore {d : Decoration s} {M : Finset (EndEvent s)} (hM : IsMarked d M) :
    group (restore hM) = M := by
  let D := restore hM
  have hD := isDiagram_restore hM
  have retained_mem (e : {e // e ∈ M}) : e.val.1 ∈ D := by
    apply mem_restore.mpr
    exact ⟨⟨(e.val.1,e.val.1.finish),(hM.1 _ e.property).2.2.2.2⟩,shorten_self _⟩
  have event_leader (e : {e // e ∈ M}) (a : {a // a ∈ D}) (he : restoreEvent hM e = a.val) :
      leader D a = e.val.1 := by
    obtain ⟨f,hf⟩ := mem_restore.mp (leader_mem D a)
    have kf : f.val.1.key = (restoreEvent hM f).key := rfl
    have ke : e.val.1.key = (restoreEvent hM e).key := rfl
    have hk : f.val.1.key = e.val.1.key := by
      rw [kf,ke,hf,he,leader_key]
    have heq : f.val.1 = e.val.1 := by
      by_contra hn
      exact ((hM.2 f.property e.property (fun h => hn (congrArg Prod.fst h))).2 hn).2 hk
    have hle : (leader D a).finish ≤ e.val.1.finish := by
      rw [← hf, ← heq]
      exact (hM.1 _ f.property).2.2.1
    have hge := le_leader_end D a (retained_mem e) (ke.trans (congrArg SArc.key he))
    exact diagram_finish_inj hD (leader_mem D a) (retained_mem e) (le_antisymm hle hge)
  ext e
  rw [mem_group]
  constructor
  · rintro ⟨a,rfl⟩
    obtain ⟨f,hf⟩ := mem_restore.mp a.property
    rw [event_leader f a hf, ← hf]
    exact f.property
  · intro he
    have hf : restoreEvent hM ⟨e,he⟩ ∈ D := mem_restore.mpr ⟨⟨e,he⟩,rfl⟩
    exact ⟨⟨_,hf⟩, Prod.ext (event_leader ⟨e,he⟩ ⟨_,hf⟩ rfl) rfl⟩

/-- Grouping equal keys and restoring all marks are inverse and preserve size. -/
noncomputable def groupEquiv (d : Decoration s) (m : ℕ) :
    DiagramOfSize d m ≃ MarkedOfSize d m where
  toFun X := ⟨group X.val, isMarked_group X.property.1, (group_card X.property.1).trans X.property.2⟩
  invFun Y := ⟨restore Y.property.1, isDiagram_restore Y.property.1,
    (restore_card Y.property.1).trans Y.property.2⟩
  left_inv X := Subtype.ext (restore_group X.property.1)
  right_inv Y := Subtype.ext (group_restore Y.property.1)

#print axioms groupEquiv

end Permutree
```

### `ActiveOrder.lean`

```lean
import MarkedDiagrams
import Mathlib.Data.Finset.Sort

namespace Permutree

open SArc

variable {n : ℕ} {s : Fin n → ℕ}

theorem sideIncl_of_overlap_leftOf {a b : SArc s} (hn : a.Noncrossing b)
    (hl : a.LeftOf b) (hab : a.start < b.finish) (hba : b.start < a.finish) :
    a.SideIncl b := by
  rcases hn with h | h
  · rcases ((orderedNoncrossing_iff _ _).mp h).2 with h | ⟨h,_,_⟩ | ⟨_,h,_⟩ | ⟨h,_⟩
    · exact (hba.not_ge h).elim
    · exact (leftOf_exclusive hl h).elim
    · exact h
    · exact (not_sameKey_of_leftOf hl h).elim
  · rcases ((orderedNoncrossing_iff _ _).mp h).2 with h | ⟨_,h,_⟩ | ⟨h,_,_⟩ | ⟨h,_⟩
    · exact (hab.not_ge h).elim
    · exact h
    · exact (leftOf_exclusive hl h).elim
    · exact (not_sameKey_of_leftOf hl ⟨h.1.symm,h.2.symm⟩).elim

theorem no_reversed_sides {a b : SArc s} {h : Fin n}
    (hn : a.Noncrossing b) (hl : a.LeftOf b) (ha : h ∈ a.right) (hb : h ∈ b.left) :
    False := by
  obtain ⟨has,haf,_⟩ := mem_positiveInterior.mp (a.right_subset ha)
  obtain ⟨hbs,hbf,_⟩ := mem_positiveInterior.mp (mem_left.mp hb).1
  exact (mem_left.mp hb).2 (sideIncl_of_overlap_leftOf hn hl (has.trans hbf) (hbs.trans haf)
    h ⟨mem_between.mpr ⟨has,haf⟩,mem_between.mpr ⟨hbs,hbf⟩⟩ ha)

/-- Three pairwise compatible arcs cannot have cyclic overlap order. -/
theorem no_cycle {a b c : SArc s} (hab : a.Noncrossing b) (hbc : b.Noncrossing c)
    (hca : c.Noncrossing a) (ab : a.LeftOf b) (bc : b.LeftOf c) (ca : c.LeftOf a) : False := by
  have hab' := ab
  have hbc' := bc
  have hca' := ca
  rcases ab with ab | ab | ab <;> rcases bc with bc | bc | bc <;> rcases ca with ca | ca | ca
  all_goals
    first
    | exact no_reversed_sides hab hab' ca.2 bc.2
    | exact no_reversed_sides hbc hbc' ab.2 ca.2
    | exact no_reversed_sides hca hca' bc.2 ab.2
    | exact (mem_left.mp ab.2).2 (bc.1.symm ▸ ca.2)
    | exact (mem_left.mp bc.2).2 (ca.1.symm ▸ ab.2)
    | exact (mem_left.mp ca.2).2 (ab.1.symm ▸ bc.2)
    | omega

/-- Distinct retained arcs live on a common cut, so the overlap order
on the active set is a strict total order. -/
def ActiveAt {M : Finset (EndEvent s)} (h : Fin n) (a : SArc s) : Prop :=
  (a,a.finish) ∈ M ∧ a.start < h ∧ h ≤ a.finish

theorem active_trichotomy {d : Decoration s} {M : Finset (EndEvent s)} (hM : IsMarked d M)
    {h : Fin n} {a b : SArc s} (ha : ActiveAt (M := M) h a) (hb : ActiveAt (M := M) h b)
    (hne : a ≠ b) : a.LeftOf b ∨ b.LeftOf a := by
  have h := hM.2 ha.1 hb.1 (fun h => hne (congrArg Prod.fst h))
  rcases leftOf_trichotomy (ha.2.1.trans_le hb.2.2) (hb.2.1.trans_le ha.2.2) with hl | hk | hr
  · exact Or.inl hl
  · exact ((h.2 hne).2 (sameKey_iff_key_eq.mp hk)).elim
  · exact Or.inr hr

theorem active_transitive {d : Decoration s} {M : Finset (EndEvent s)} (hM : IsMarked d M)
    {h : Fin n} {a b c : SArc s} (ha : ActiveAt (M := M) h a) (hb : ActiveAt (M := M) h b)
    (hc : ActiveAt (M := M) h c) (hab : a.LeftOf b) (hbc : b.LeftOf c) : a.LeftOf c := by
  have ab : a ≠ b := fun e => not_sameKey_of_leftOf hab ⟨congrArg SArc.start e,congrArg SArc.r e⟩
  have bc : b ≠ c := fun e => not_sameKey_of_leftOf hbc ⟨congrArg SArc.start e,congrArg SArc.r e⟩
  have ac : a ≠ c := fun e => leftOf_exclusive hab (e.symm ▸ hbc)
  rcases active_trichotomy hM ha hc ac with hl | hl
  · exact hl
  · have hn {x y : SArc s} (hx : ActiveAt (M := M) h x) (hy : ActiveAt (M := M) h y)
        (hxy : x ≠ y) : x.Noncrossing y :=
      (hM.2 hx.1 hy.1 (fun e => hxy (congrArg Prod.fst e))).2 hxy |>.1
    exact (no_cycle (hn ha hb ab) (hn hb hc bc) (hn hc ha ac.symm) hab hbc hl).elim

theorem end_side_of_leftOf {a b : SArc s} (hn : a.Noncrossing b)
    (he : a.finish < b.finish) (hs : b.start < a.finish) (hp : s a.finish ≠ 0) :
    (b.LeftOf a → a.finish ∈ b.left) ∧ (a.LeftOf b → a.finish ∈ b.right) := by
  have hinterior := mem_positiveInterior.mpr ⟨hs,he,hp⟩
  rcases ((orderedNoncrossing_iff a b).mp (ordered_of_noncrossing_of_lt hn he)).2 with
    h | ⟨hl,_,hnr⟩ | ⟨hl,_,hnl⟩ | ⟨_,hz,_⟩
  · exact (hs.not_ge h).elim
  · exact ⟨fun _ => mem_left.mpr ⟨hinterior,hnr⟩,fun h => (leftOf_exclusive hl h).elim⟩
  · refine ⟨fun h => (leftOf_exclusive hl h).elim, fun _ => ?_⟩
    by_contra hr
    exact hnl (mem_left.mpr ⟨hinterior,hr⟩)
  · exact (hp hz).elim

#print axioms active_transitive
#print axioms end_side_of_leftOf

end Permutree
```

### `ActiveCut.lean`

```lean
import ActiveOrder
import SweepCode

namespace Permutree

open SArc

variable {n : ℕ} {s : Fin n → ℕ}

private theorem prefix_of_no_inversions {A : Type*} (P : A → Prop) (L : List A)
    (h : L.Pairwise fun a b => P b → P a) :
    ∃ left right, L = left ++ right ∧ (∀ a ∈ left, P a) ∧ (∀ a ∈ right, ¬ P a) := by
  classical
  induction L with
  | nil => exact ⟨[],[],by simp⟩
  | cons a tail ih =>
    obtain ⟨h₁,h₂⟩ := List.pairwise_cons.mp h
    by_cases ha : P a
    · obtain ⟨l,r,e,hl,hr⟩ := ih h₂
      refine ⟨a :: l,r,congrArg (List.cons a) e,?_,hr⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ha
      · exact hl b hb
    · exact ⟨[],a :: tail,rfl,by simp,fun b hb => by
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ha
        · exact fun hp => ha (h₁ b hb hp)⟩

/-- Positive-level cut: a gap if no arc ends, and the unique ending entry
otherwise. Only the through arcs are assigned sides. -/
def IsPositiveCut (h : Fin n) (ends : Option (SArc s)) (active left right : List (SArc s)) : Prop :=
  active = left ++ ends.toList ++ right ∧
    (∀ a ∈ left, h ∈ a.left) ∧ (∀ a ∈ right, h ∈ a.right)

theorem positiveCut_exists {d : Decoration s} {M : Finset (EndEvent s)} (hM : IsMarked d M)
    (h : Fin n) (hp : s h ≠ 0) (active : List (SArc s))
    (hactive : ∀ a ∈ active, ActiveAt (M := M) h a) (horder : active.Pairwise SArc.LeftOf)
    (ends : Option (SArc s))
    (he : ∀ a, ends = some a ↔ a ∈ active ∧ a.finish = h) :
    ∃ left right, IsPositiveCut h ends active left right := by
  have hnc {a b : SArc s} (ha : a ∈ active) (hb : b ∈ active) (hl : a.LeftOf b) :
      a.Noncrossing b := by
    have hne : a ≠ b := fun e => not_sameKey_of_leftOf hl ⟨congrArg SArc.start e,congrArg SArc.r e⟩
    have hma := (hactive a ha).1
    have hmb := (hactive b hb).1
    exact ((hM.2 hma hmb (fun e => hne (congrArg Prod.fst e))).2 hne).1
  cases ends with
  | none =>
    have hinter (a : SArc s) (ha : a ∈ active) : h ∈ positiveInterior s a.start a.finish := by
      have hae := hactive a ha
      have hf : a.finish ≠ h := fun e => by simpa using (he a).mpr ⟨ha,e⟩
      exact mem_positiveInterior.mpr ⟨hae.2.1,lt_of_le_of_ne hae.2.2 (Ne.symm hf),hp⟩
    have ho : active.Pairwise fun a b => h ∈ b.left → h ∈ a.left := by
      refine horder.imp_of_mem ?_
      intro a b ha hb hl hbl
      by_contra hn
      have har : h ∈ a.right := by
        by_contra hnr
        exact hn (mem_left.mpr ⟨hinter a ha,hnr⟩)
      exact no_reversed_sides (hnc ha hb hl) hl har hbl
    obtain ⟨l,r,e,hl,hr⟩ := prefix_of_no_inversions (fun a => h ∈ a.left) active ho
    refine ⟨l,r,by simpa using e,hl,?_⟩
    intro a ha
    have hal : a ∈ active := e ▸ List.mem_append_right l ha
    by_contra hn
    exact hr a ha (mem_left.mpr ⟨hinter a hal,hn⟩)
  | some a =>
    obtain ⟨ha,haend⟩ := (he a).mp rfl
    obtain ⟨l,r,rfl⟩ := List.mem_iff_append.mp ha
    have hc := List.pairwise_append.mp horder
    have hcl := hc.2.2
    have hcr := (List.pairwise_cons.mp hc.2.1).1
    refine ⟨l,r,by simp,?_,?_⟩
    · intro b hb
      have hba := hcl b hb a (by simp)
      have hbm := List.mem_append_left (a :: r) hb
      have hn := noncrossing_symm (hnc hbm ha hba)
      have hf : h < b.finish := by
        have hle := (hactive b hbm).2.2
        exact lt_of_le_of_ne hle (haend ▸ finish_ne_of_noncrossing hn)
      have hbs := (hactive b hbm).2.1
      exact haend ▸ (end_side_of_leftOf hn (haend.symm ▸ hf)
        (haend.symm ▸ hbs) (haend.symm ▸ hp)).1 hba
    · intro b hb
      have hab := hcr b hb
      have hbm := List.mem_append_right l (List.mem_cons_of_mem a hb)
      have hn := hnc ha hbm hab
      have hf : h < b.finish := by
        have hle := (hactive b hbm).2.2
        exact lt_of_le_of_ne hle (haend ▸ finish_ne_of_noncrossing hn)
      have hbs := (hactive b hbm).2.1
      exact haend ▸ (end_side_of_leftOf hn (haend.symm ▸ hf)
        (haend.symm ▸ hbs) (haend.symm ▸ hp)).2 hab

theorem positiveCut_unique {h : Fin n} {ends : Option (SArc s)}
    {active l r l' r' : List (SArc s)}
    (hc : IsPositiveCut h ends active l r) (hc' : IsPositiveCut h ends active l' r')
    (he : ∀ a, ends = some a → a.finish = h) : l = l' ∧ r = r' := by
  classical
  have noLeft (a : SArc s) (ha : a ∈ ends.toList) : h ∉ a.left := by
    intro hside
    have hf := he a (by cases ends <;> simp_all)
    have hh := (mem_positiveInterior.mp (mem_left.mp hside).1).2.1
    exact (lt_irrefl h) (hf ▸ hh)
  have noRight (a : SArc s) (ha : a ∈ ends.toList) : h ∉ a.right := by
    intro hside
    have hf := he a (by cases ends <;> simp_all)
    have hh := (mem_positiveInterior.mp (a.right_subset hside)).2.1
    exact (lt_irrefl h) (hf ▸ hh)
  have left_is_filter {l r : List (SArc s)} (hcut : IsPositiveCut h ends active l r) :
      active.filter (fun a => decide (h ∈ a.left)) = l := by
    have hl : l.filter (fun a => decide (h ∈ a.left)) = l :=
      List.filter_eq_self.mpr (fun a ha => decide_eq_true (hcut.2.1 a ha))
    have he : ends.toList.filter (fun a => decide (h ∈ a.left)) = [] :=
      List.filter_eq_nil_iff.mpr (fun a ha => by simpa using noLeft a ha)
    have hr : r.filter (fun a => decide (h ∈ a.left)) = [] :=
      List.filter_eq_nil_iff.mpr (fun a ha => by
        simpa using (show h ∉ a.left from fun h => (mem_left.mp h).2 (hcut.2.2 a ha)))
    rw [hcut.1, List.filter_append, List.filter_append, hl, he, hr]
    simp
  have right_is_filter {l r : List (SArc s)} (hcut : IsPositiveCut h ends active l r) :
      active.filter (fun a => decide (h ∈ a.right)) = r := by
    have hl : l.filter (fun a => decide (h ∈ a.right)) = [] :=
      List.filter_eq_nil_iff.mpr (fun a ha => by simpa using (mem_left.mp (hcut.2.1 a ha)).2)
    have he : ends.toList.filter (fun a => decide (h ∈ a.right)) = [] :=
      List.filter_eq_nil_iff.mpr (fun a ha => by simpa using noRight a ha)
    have hr : r.filter (fun a => decide (h ∈ a.right)) = r :=
      List.filter_eq_self.mpr (fun a ha => decide_eq_true (hcut.2.2 a ha))
    rw [hcut.1, List.filter_append, List.filter_append, hl, he, hr]
    simp
  exact ⟨(left_is_filter hc).symm.trans (left_is_filter hc'),
    (right_is_filter hc).symm.trans (right_is_filter hc')⟩

/-- For a marked diagram, the cut rank satisfies the decoration restrictions. -/
def placementOfCut {d : Decoration s} {M : Finset (EndEvent s)} (hM : IsMarked d M)
    {h : Fin n} (hp : s h ≠ 0) {ends : Option (SArc s)} {active left right : List (SArc s)}
    (hc : IsPositiveCut h ends active left right)
    (hactive : ∀ a ∈ active, ActiveAt (M := M) h a) :
    Placement (d ⟨h,hp⟩) (left.length + right.length) := by
  refine ⟨⟨left.length,by omega⟩, ?_, ?_⟩
  · intro hl
    cases left with
    | nil => exact (Nat.lt_irrefl _ hl).elim
    | cons a tail =>
      have ha : a ∈ a :: tail := by simp
      have hma : a ∈ active := hc.1 ▸ List.mem_append_left _ (List.mem_append_left _ ha)
      exact ((hM.1 _ (hactive _ hma).1).1 ⟨h,hp⟩).2 (hc.2.1 _ ha)
  · intro hr
    cases right with
    | nil => simp at hr
    | cons a tail =>
      have ha : a ∈ a :: tail := by simp
      have hma : a ∈ active := hc.1 ▸ List.mem_append_right _ ha
      exact ((hM.1 _ (hactive _ hma).1).1 ⟨h,hp⟩).1 (hc.2.2 _ ha)

#print axioms positiveCut_exists
#print axioms positiveCut_unique
#print axioms placementOfCut

end Permutree
```

### `SweepStep.lean`

```lean
import ActiveCut
import Mathlib.Data.List.Nodup

namespace Permutree

namespace SweepStep

variable {n : ℕ} {s : Fin n → ℕ}

abbrev Key (s : Fin n → ℕ) := Σ i, Fin (s i)

def level (d : Decoration s) (i : Fin n) : Level :=
  (s i, if h : s i ≠ 0 then d ⟨i,h⟩ else .none)

noncomputable def startsAt (i : Fin n) (S : Finset (Fin (s i))) : List (Key s) :=
  (S.sort (· ≥ ·)).map (Sigma.mk i)

theorem mem_startsAt {i : Fin n} {S : Finset (Fin (s i))} {k : Key s} :
    k ∈ startsAt i S ↔ ∃ t ∈ S, (⟨i,t⟩ : Key s) = k := by
  simp [startsAt]

theorem startsAt_length (i : Fin n) (S : Finset (Fin (s i))) :
    (startsAt i S).length = S.card := by simp [startsAt]

theorem startsAt_nodup (i : Fin n) (S : Finset (Fin (s i))) : (startsAt i S).Nodup := by
  unfold startsAt
  exact (Finset.sort_nodup _ _).map (fun _ _ e => eq_of_heq (Sigma.mk.inj_iff.mp e).2)

theorem startsAt_pairwise (i : Fin n) (S : Finset (Fin (s i))) :
    (startsAt i S).Pairwise (fun a b => b.2.val < a.2.val) := by
  rw [startsAt, List.pairwise_map]
  exact S.sortedGT_sort.pairwise

variable {d : Decoration s} {i : Fin n} {old : List (Key s)}

def Event.hasPivot {l : Level} {b : ℕ} (e : Permutree.Event l b) : Bool :=
  e.val.1 || e.val.2

/-- Split the incoming list at the point. A distinguished entry is either
an end or a mark. The zero level with no event uses the unique empty prefix. -/
structure Cut (d : Decoration s) (i : Fin n) (old : List (Key s))
    (e : Permutree.Event (level d i) old.length) where
  left : List (Key s)
  pivot : List (Key s)
  right : List (Key s)
  split : old = left ++ pivot ++ right
  pivot_length : pivot.length = (Event.hasPivot e).toNat
  zero_idle : s i = 0 → Event.hasPivot e = false → left = []
  left_allowed : s i ≠ 0 → 0 < left.length → (level d i).2.allowsLeft
  right_allowed : s i ≠ 0 → 0 < right.length → (level d i).2.allowsRight

theorem Cut.right_eq {e : Permutree.Event (level d i) old.length} (c : Cut d i old e) :
    c.right = old.drop (c.left.length + c.pivot.length) := by
  calc
    _ = (c.left ++ c.pivot ++ c.right).drop (c.left.length + c.pivot.length) := by simp
    _ = _ := congrArg (List.drop _) c.split.symm

theorem Cut.left_eq {e : Permutree.Event (level d i) old.length} (c : Cut d i old e) :
    c.left = old.take c.left.length := by
  calc
    _ = (c.left ++ c.pivot ++ c.right).take c.left.length := by simp [List.append_assoc]
    _ = _ := congrArg (List.take _) c.split.symm

theorem Cut.pivot_eq {e : Permutree.Event (level d i) old.length} (c : Cut d i old e) :
    c.pivot = (old.drop c.left.length).take (Event.hasPivot e).toNat := by
  calc
    _ = ((c.left ++ c.pivot ++ c.right).drop c.left.length).take (Event.hasPivot e).toNat := by
      rw [List.append_assoc, List.drop_left, ← c.pivot_length, List.take_left]
    _ = _ := congrArg (fun l : List (Key s) => (l.drop c.left.length).take (Event.hasPivot e).toNat) c.split.symm

theorem Cut.eq_of_rank {e : Permutree.Event (level d i) old.length} (c c' : Cut d i old e)
    (h : c.left.length = c'.left.length) : c = c' := by
  have hl := c.left_eq.trans (h.symm ▸ c'.left_eq.symm)
  have hp := c.pivot_eq.trans (h.symm ▸ c'.pivot_eq.symm)
  have hr : c.right = c'.right := by rw [c.right_eq, c'.right_eq, c.pivot_length, c'.pivot_length, h]
  cases c; cases c'; cases hl; cases hp; cases hr; rfl

theorem Cut.total_length {e : Permutree.Event (level d i) old.length} (c : Cut d i old e) :
    c.left.length + (Event.hasPivot e).toNat + c.right.length = old.length := by
  conv_rhs => rw [c.split, List.length_append, List.length_append, c.pivot_length]

private theorem mark_false {e : Permutree.Event (level d i) old.length}
    (hi : s i ≠ 0) : e.val.2 = false := by
  cases h : e.val.2
  · rfl
  · exact (hi (e.property.2 h).2.1).elim

theorem pivot_pos {e : Permutree.Event (level d i) old.length}
    (hi : s i ≠ 0) : Event.hasPivot e = e.val.1 := by
  simp [Event.hasPivot, mark_false hi]

theorem choice_zero {e : Permutree.Event (level d i) old.length} (hi : s i = 0) :
    e.Choice = Fin (if Event.hasPivot e then old.length else 1) := by
  simp [Permutree.Event.Choice, level, hi, Event.hasPivot]

theorem choice_pos {e : Permutree.Event (level d i) old.length} (hi : s i ≠ 0) :
    e.Choice = Placement (level d i).2 e.through := by
  simp [Permutree.Event.Choice, level, hi]

private theorem through_length {e : Permutree.Event (level d i) old.length} :
    e.through + e.val.1.toNat = old.length := by
  cases h : e.val.1
  · simp [Permutree.Event.through, h]
  · have := e.property.1 h
    simp [Permutree.Event.through, h]
    omega

def Cut.ofRank {e : Permutree.Event (level d i) old.length}
    (r : ℕ) (h : r + (Event.hasPivot e).toNat ≤ old.length)
    (hz : s i = 0 → Event.hasPivot e = false → r = 0)
    (hl : s i ≠ 0 → 0 < r → (level d i).2.allowsLeft)
    (hr : s i ≠ 0 → r + (Event.hasPivot e).toNat < old.length → (level d i).2.allowsRight) :
    Cut d i old e where
  left := old.take r
  pivot := (old.drop r).take (Event.hasPivot e).toNat
  right := (old.drop r).drop (Event.hasPivot e).toNat
  split := by rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
  pivot_length := by simp [List.length_take, List.length_drop, Nat.min_eq_left (by omega : (Event.hasPivot e).toNat ≤ old.length - r)]
  zero_idle hi he := by simp [hz hi he]
  left_allowed hi hp := hl hi (by simpa [List.length_take, Nat.min_eq_left (by omega : r ≤ old.length)] using hp)
  right_allowed hi hp := hr hi (by simp [List.length_drop] at hp; omega)

@[simp] theorem Cut.ofRank_rank {e : Permutree.Event (level d i) old.length}
    (r h hz hl hr) : (Cut.ofRank (e := e) r h hz hl hr).left.length = r := by
  simp [Cut.ofRank, List.length_take, Nat.min_eq_left (by omega : r ≤ old.length)]

def Cut.ofZero {e : Permutree.Event (level d i) old.length} (hi : s i = 0)
    (p : Fin (if Event.hasPivot e then old.length else 1)) : Cut d i old e :=
  Cut.ofRank p.val (by
    have hp := p.isLt
    by_cases hb : Event.hasPivot e = true <;> simp [hb] at hp ⊢ <;> omega)
    (by intro _ hb; have := p.isLt; simp [hb] at this; omega)
    (fun hn => (hn hi).elim) (fun hn => (hn hi).elim)

def Cut.ofPositive {e : Permutree.Event (level d i) old.length} (hi : s i ≠ 0)
    (p : Placement (level d i).2 e.through) : Cut d i old e :=
  Cut.ofRank p.val.val (by
    have := p.val.isLt
    have ht := through_length (e := e)
    rw [pivot_pos hi]
    omega)
    (fun hz => (hi hz).elim) (fun _ h => p.property.1 h)
    (by
      intro _ h
      apply p.property.2
      have ht := through_length (e := e)
      rw [pivot_pos hi] at h
      omega)

def Cut.toZero {e : Permutree.Event (level d i) old.length} (c : Cut d i old e) (hi : s i = 0) :
    Fin (if Event.hasPivot e then old.length else 1) :=
  ⟨c.left.length, by
    have ht := c.total_length
    cases hp : Event.hasPivot e
    · simp [c.zero_idle hi hp]
    · simp [hp] at ht ⊢
      omega⟩

def Cut.toPositive {e : Permutree.Event (level d i) old.length} (c : Cut d i old e)
    (hi : s i ≠ 0) : Placement (level d i).2 e.through := by
  have h := c.total_length
  have ht := through_length (e := e)
  rw [pivot_pos hi] at h
  exact ⟨⟨c.left.length, by omega⟩, c.left_allowed hi, fun hr => c.right_allowed hi (by change c.left.length < e.through at hr; omega)⟩

/-- The code rank and the admissible ordered split are interchangeable. -/
def step_bijection_on_active_keys (e : Permutree.Event (level d i) old.length) :
    e.Choice ≃ Cut d i old e := by
  by_cases hi : s i = 0
  · refine (Equiv.cast (choice_zero hi)).trans
      ⟨Cut.ofZero hi, (·.toZero hi), ?_, ?_⟩
    · intro p
      exact Fin.ext (Cut.ofRank_rank ..)
    · intro c
      exact Cut.eq_of_rank _ _ (Cut.ofRank_rank ..)
  · refine (Equiv.cast (choice_pos hi)).trans
      ⟨Cut.ofPositive hi, (·.toPositive hi), ?_, ?_⟩
    · intro p
      apply Subtype.ext
      apply Fin.ext
      change (Cut.ofPositive hi p).left.length = p.val.val
      exact Cut.ofRank_rank ..
    · intro c
      apply Cut.eq_of_rank
      change (Cut.ofPositive hi (c.toPositive hi)).left.length = c.left.length
      exact Cut.ofRank_rank ..

def Cut.ends {e : Permutree.Event (level d i) old.length} (c : Cut d i old e) : List (Key s) :=
  if e.val.1 then c.pivot else []

def Cut.marks {e : Permutree.Event (level d i) old.length} (c : Cut d i old e) : List (Key s) :=
  if e.val.2 then c.pivot else []

def Cut.passesRight {e : Permutree.Event (level d i) old.length} (c : Cut d i old e) : List (Key s) :=
  if s i = 0 then [] else c.right

noncomputable def Cut.next {e : Permutree.Event (level d i) old.length} (c : Cut d i old e)
    (starts : Finset (Fin (s i))) : List (Key s) :=
  c.left ++ c.marks ++ startsAt i starts ++ c.right

theorem Cut.next_length {e : Permutree.Event (level d i) old.length} (c : Cut d i old e)
    (starts : Finset (Fin (s i))) :
    (c.next starts).length = e.through + starts.card := by
  have h := c.total_length
  have hp := c.pivot_length
  have ht := through_length (e := e)
  have hc : e.val.2 = true → e.val.1 = false := fun hm => (e.property.2 hm).2.2
  cases he : e.val.1 <;> cases hm : e.val.2 <;>
    simp [Cut.next, Cut.marks, startsAt_length, Event.hasPivot, he, hm] at h hp ht hc ⊢ <;> omega

#print axioms step_bijection_on_active_keys
#print axioms Cut.next_length

end SweepStep

end Permutree
```

### `SweepHistory.lean`

```lean
import SweepStep

namespace Permutree.SweepStep

set_option backward.isDefEq.respectTransparency false

variable {n t : ℕ} {s : Fin n → ℕ} {d : Decoration s} {i : Fin n}
variable {old : List (Key s)}

/-- One local transition with its source list fixed. -/
structure Move (d : Decoration s) (i : Fin n) (old : List (Key s)) where
  event : Permutree.Event (level d i) old.length
  cut : Cut d i old event
  starts : Finset (Fin (s i))

noncomputable def Move.next (u : Move d i old) : List (Key s) := u.cut.next u.starts
def Move.weight (u : Move d i old) : ℕ := u.event.weight

@[simp] theorem Move.next_length (u : Move d i old) :
    u.next.length = u.event.through + u.starts.card := u.cut.next_length _

/-- The complete list-valued history across consecutive cuts. -/
structure History (d : Decoration s) (f : Fin t → Fin n) (old : List (Key s)) (m : ℕ) where
  active : Fin (t + 1) → List (Key s)
  grade : Fin (t + 1) → ℕ
  move : ∀ j : Fin t, Move d (f j) (active j.castSucc)
  first : active 0 = old
  first_grade : grade 0 = m
  last : active (Fin.last t) = []
  last_grade : grade (Fin.last t) = 0
  next : ∀ j : Fin t, (move j).next = active j.succ
  next_grade : ∀ j : Fin t, grade j.castSucc = (move j).weight + grade j.succ

namespace History

variable {f : Fin t → Fin n} {m : ℕ}

theorem ext {H J : History d f old m}
    (ha : H.active = J.active) (hg : H.grade = J.grade) (hm : HEq H.move J.move) : H = J := by
  cases H
  cases J
  cases ha
  cases hg
  cases hm
  rfl

def head {g : Fin (t+1) → Fin n} (H : History d g old m) : Move d (g 0) old :=
  H.first ▸ H.move 0

private theorem move_cast {a b : List (Key s)} (h : a = b) (u : Move d i a) :
    (h ▸ u : Move d i b).weight = u.weight ∧
    (h ▸ u : Move d i b).next = u.next ∧ HEq (h ▸ u : Move d i b) u := by
  subst b
  exact ⟨rfl,rfl,HEq.rfl⟩

theorem head_weight {g : Fin (t+1) → Fin n} (H : History d g old m) :
    H.head.weight = (H.move 0).weight :=
  (move_cast H.first (H.move 0)).1

theorem head_next {g : Fin (t+1) → Fin n} (H : History d g old m) :
    H.head.next = H.active (0 : Fin (t+1)).succ :=
  (move_cast H.first (H.move 0)).2.1.trans (H.next 0)

def tail {g : Fin (t+1) → Fin n} (H : History d g old m) :
    History d (g ∘ Fin.succ) H.head.next (m - H.head.weight) where
  active j := H.active j.succ
  grade j := H.grade j.succ
  move j := H.move j.succ
  first := H.head_next.symm
  first_grade := by
    have h := H.next_grade 0
    change H.grade 0 = _ at h
    rw [H.first_grade, ← H.head_weight] at h
    exact (Nat.sub_eq_of_eq_add (Nat.add_comm _ _ ▸ h)).symm
  last := H.last
  last_grade := H.last_grade
  next j := H.next j.succ
  next_grade j := H.next_grade j.succ

private def prepend {A : Type*} (x : A) (xs : Fin (t + 1) → A) (j : Fin (t + 2)) : A :=
  match h : j.val with
  | 0 => x
  | k + 1 => xs ⟨k, by have := j.isLt; omega⟩

def cons {g : Fin (t+1) → Fin n} (u : Move d (g 0) old) (hu : u.weight ≤ m)
    (H : History d (g ∘ Fin.succ) u.next (m - u.weight)) : History d g old m :=
  let A : Fin (t + 2) → List (Key s) := prepend old H.active
  let G : Fin (t + 2) → ℕ := prepend m H.grade
  let U : ∀ j : Fin (t + 1), Move d (g j) (A j.castSucc) :=
    Fin.cases (motive := fun j => Move d (g j) (A j.castSucc)) u H.move
  { active := A
    grade := G
    move := U
    first := rfl
    first_grade := rfl
    last := H.last
    last_grade := H.last_grade
    next := fun j => Fin.cases (motive := fun j => (U j).next = A j.succ) H.first.symm H.next j
    next_grade := fun j => Fin.cases (motive := fun j =>
      G j.castSucc = (U j).weight + G j.succ)
        (by change m = u.weight + H.grade 0
            rw [H.first_grade, Nat.add_sub_of_le hu]) H.next_grade j }

theorem head_le {g : Fin (t+1) → Fin n} (H : History d g old m) : H.head.weight ≤ m := by
  have h := H.next_grade 0
  change H.grade 0 = _ at h
  rw [H.first_grade, ← H.head_weight] at h
  omega

/-- The records are recovered by prefixing the head transition to the tail. -/
def split {g : Fin (t+1) → Fin n} :
    History d g old m ≃ Σ u : Move d (g 0) old,
      {_H : History d (g ∘ Fin.succ) u.next (m - u.weight) // u.weight ≤ m} where
  toFun H := ⟨H.head, H.tail, H.head_le⟩
  invFun H := cons H.1 H.2.property H.2.val
  left_inv H := by
    have e₁ : (cons H.head H.head_le H.tail).active = H.active := by
      funext j
      refine Fin.cases H.first.symm (fun _ => rfl) j
    have e₂ : (cons H.head H.head_le H.tail).grade = H.grade := by
      funext j
      refine Fin.cases H.first_grade.symm (fun _ => rfl) j
    refine ext e₁ e₂ ?_
    apply Function.hfunext rfl
    intro j k e
    have h : j = k := eq_of_heq e
    subst k
    refine Fin.cases (motive := fun j => HEq ((cons H.head H.head_le H.tail).move j) (H.move j))
        (move_cast H.first (H.move 0)).2.2 (fun _ => HEq.rfl) j
  right_inv H := by
    obtain ⟨u,H,hu⟩ := H
    rfl

def nilEquiv (f : Fin 0 → Fin n) :
    History d f old m ≃ {_u : Unit // old.length = 0 ∧ m = 0} where
  toFun H := ⟨(), by rw [← H.first]; change (H.active (Fin.last 0)).length = 0; rw [H.last]; rfl, H.first_grade.symm.trans H.last_grade⟩
  invFun H := {
    active := fun _ => old
    grade := fun _ => m
    move := fun j => j.elim0
    first := rfl
    first_grade := rfl
    last := List.length_eq_zero_iff.mp H.property.1
    last_grade := H.property.2
    next := fun j => j.elim0
    next_grade := fun j => j.elim0 }
  left_inv H := by
    have e₁ : (fun _ : Fin 1 => old) = H.active := funext fun j =>
      (Subsingleton.elim j 0 : j = 0) ▸ H.first.symm
    have e₂ : (fun _ : Fin 1 => m) = H.grade := funext fun j =>
      (Subsingleton.elim j 0 : j = 0) ▸ H.first_grade.symm
    refine ext e₁ e₂ ?_
    exact Function.hfunext rfl (fun j => j.elim0)
  right_inv _ := Subsingleton.elim _ _

end History

noncomputable def historyEquiv (d : Decoration s) (f : Fin t → Fin n)
    (old : List (Key s)) (m : ℕ) :
    History d f old m ≃ Sweep (List.ofFn (level d ∘ f)) old.length m := by
  induction t generalizing old m with
  | zero => exact History.nilEquiv f
  | succ t ih =>
    rw [List.ofFn_succ]
    change _ ≃ Σ e : Permutree.Event (level d (f 0)) old.length, e.Choice ×
      (Σ starts : Finset (Fin (s (f 0))),
        {_u : Sweep (List.ofFn (level d ∘ (f ∘ Fin.succ))) (e.through + starts.card)
          (m - e.weight) // e.weight ≤ m})
    refine History.split.trans ?_
    let input : Move d (f 0) old ≃ Σ e : Permutree.Event (level d (f 0)) old.length,
        e.Choice × Finset (Fin (s (f 0))) := {
      toFun u := ⟨u.event, (step_bijection_on_active_keys u.event).symm u.cut, u.starts⟩
      invFun u := ⟨u.1, step_bijection_on_active_keys u.1 u.2.1, u.2.2⟩
      left_inv := by rintro ⟨e,c,S⟩; simp
      right_inv := by rintro ⟨e,c,S⟩; simp }
    let F (v : Σ e : Permutree.Event (level d (f 0)) old.length, e.Choice × Finset (Fin (s (f 0)))) :=
      {H : Sweep (List.ofFn (level d ∘ (f ∘ Fin.succ))) (v.1.through + v.2.2.card)
        (m - v.1.weight) // v.1.weight ≤ m}
    have tailEquiv (u : Move d (f 0) old) : _ ≃ F (input u) :=
      ((ih (f ∘ Fin.succ) u.next (m - u.weight)).trans
        (Equiv.cast (congrArg (fun b => Sweep (List.ofFn (level d ∘ (f ∘ Fin.succ))) b
          (m - u.weight)) u.next_length))).subtypeEquiv (fun _ => Iff.rfl)
    refine (Equiv.sigmaCongr input tailEquiv).trans ?_
    exact {
        toFun := fun ⟨⟨e,c,S⟩,H⟩ => ⟨e,c,S,H⟩
        invFun := fun ⟨e,c,S,H⟩ => ⟨⟨e,c,S⟩,H⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }

#print axioms historyEquiv

end Permutree.SweepStep
```

### `SweepLifetimes.lean`

```lean
import SweepHistory

namespace Permutree.SweepStep

variable {n : ℕ} {s : Fin n → ℕ} {d : Decoration s} {i : Fin n}
variable {old : List (Key s)} {k a b : Key s}

namespace Move

variable (u : Move d i old)

theorem pivot_partition : u.cut.pivot = u.cut.ends ++ u.cut.marks := by
  have h := u.cut.pivot_length
  have hc : u.event.val.2 = true → u.event.val.1 = false := fun hm => (u.event.property.2 hm).2.2
  cases he : u.event.val.1 <;> cases hm : u.event.val.2 <;>
    simp_all [Cut.ends, Cut.marks, Event.hasPivot]

theorem old_split : old = u.cut.left ++ u.cut.ends ++ u.cut.marks ++ u.cut.right := by
  simpa [u.pivot_partition, List.append_assoc] using u.cut.split

theorem occupied_length : u.cut.pivot.length = u.weight := by
  have h := u.cut.pivot_length
  have hc : u.event.val.2 = true → u.event.val.1 = false := fun hm => (u.event.property.2 hm).2.2
  cases he : u.event.val.1 <;> cases hm : u.event.val.2 <;>
    simp [Event.hasPivot, Move.weight, Permutree.Event.weight, he, hm] at h hc ⊢ <;> assumption

theorem length_pivot_le_one : u.cut.pivot.length ≤ 1 := by
  rw [u.cut.pivot_length]
  cases Event.hasPivot u.event <;> decide

theorem pivot_mem_unique {a b : Key s} (ha : a ∈ u.cut.pivot) (hb : b ∈ u.cut.pivot) : a = b := by
  obtain ⟨as,bs,h⟩ := List.mem_iff_append.mp ha
  have hl := u.length_pivot_le_one
  rw [h] at hl hb
  simp only [List.length_append, List.length_cons] at hl
  have ea : as = [] := List.length_eq_zero_iff.mp (by omega)
  have eb : bs = [] := List.length_eq_zero_iff.mp (by omega)
  simp [ea,eb] at hb
  exact hb.symm

theorem starts_fresh (h : ∀ a ∈ old, a.1 < i) {k : Key s} (hk : k ∈ startsAt i u.starts) :
    k ∉ old := by
  obtain ⟨r,_,rfl⟩ := mem_startsAt.mp hk
  exact fun hm => (lt_irrefl i) (h _ hm)

theorem mem_ends_old (h : k ∈ u.cut.ends) : k ∈ old := by
  rw [u.old_split]
  simp [h]

theorem mem_marks_old (h : k ∈ u.cut.marks) : k ∈ old := by
  rw [u.old_split]
  simp [h]

theorem mem_passesRight_old (h : k ∈ u.cut.passesRight) : k ∈ old := by
  have hr : k ∈ u.cut.right := by
    by_cases hz : s i = 0
    · simp [Cut.passesRight, hz] at h
    · simpa [Cut.passesRight, hz] using h
  rw [u.old_split]
  simp [hr]

theorem mark_zero (h : k ∈ u.cut.marks) : s i = 0 := by
  have he : u.event.val.2 = true := by
    cases he : u.event.val.2 <;> simp_all [Cut.marks]
  exact (u.event.property.2 he).2.1

theorem marks_ends_disjoint : u.cut.marks = [] ∨ u.cut.ends = [] := by
  cases he : u.event.val.2
  · exact Or.inl (by simp [Cut.marks, he])
  · exact Or.inr (by simp [Cut.ends, (u.event.property.2 he).2.2])

theorem cross_new (h : ∀ a ∈ old, a.1 < i)
    (ha : a ∈ old) (hb : b ∈ startsAt i u.starts) : b ≠ a := fun e =>
  u.starts_fresh h hb (e.symm ▸ ha)

theorem next_nodup (hn : old.Nodup) (h : ∀ a ∈ old, a.1 < i) : u.next.Nodup := by
  rw [u.old_split, List.nodup_iff_pairwise_ne] at hn
  simp only [List.pairwise_append, List.nodup_iff_pairwise_ne, Move.next, Cut.next] at hn ⊢
  have hl : ∀ k ∈ u.cut.left, k ∈ old := fun k hk => by rw [u.old_split]; simp [hk]
  have hm : ∀ k ∈ u.cut.marks, k ∈ old := fun _ hk => u.mem_marks_old hk
  have hr : ∀ k ∈ u.cut.right, k ∈ old := fun k hk => by rw [u.old_split]; simp [hk]
  have hs := List.nodup_iff_pairwise_ne.mp (startsAt_nodup i u.starts)
  grind [starts_fresh]

theorem mem_next (hn : old.Nodup) :
    k ∈ u.next ↔ (k ∈ old ∧ k ∉ u.cut.ends) ∨ k ∈ startsAt i u.starts := by
  have hm : k ∈ old ↔ k ∈ u.cut.left ∨ k ∈ u.cut.ends ∨ k ∈ u.cut.marks ∨ k ∈ u.cut.right := by
    simpa only [List.mem_append, or_assoc] using Iff.of_eq (congrArg (fun l => k ∈ l) u.old_split)
  rw [u.old_split, List.nodup_iff_pairwise_ne] at hn
  simp only [List.pairwise_append, List.mem_append] at hn
  simp only [Move.next, Cut.next, List.mem_append]
  grind [starts_fresh]

theorem end_not_next (hn : old.Nodup) (h : ∀ a ∈ old, a.1 < i)
    (hk : k ∈ u.cut.ends) : k ∉ u.next := by
  intro hm
  rcases (u.mem_next hn).mp hm with ⟨_,he⟩ | he
  · exact he hk
  · exact u.starts_fresh h he (u.mem_ends_old hk)

theorem right_mem_iff (hi : s i ≠ 0) : k ∈ u.cut.passesRight ↔ k ∈ u.cut.right := by
  simp [Cut.passesRight, hi]

theorem survives_right (hk : k ∈ u.cut.passesRight) : k ∈ u.next := by
  by_cases hz : s i = 0
  · simp [Cut.passesRight, hz] at hk
  · have hr := (u.right_mem_iff hz).mp hk
    simp [Move.next, Cut.next, hr]

/-- Ignore insertions and removals when projecting to keys that survive the step. -/
theorem filter_persist (p : Key s → Bool)
    (he : ∀ k ∈ u.cut.ends, p k = false)
    (hs : ∀ k ∈ startsAt i u.starts, p k = false) :
    u.next.filter p = old.filter p := by
  have eqn := congrArg (List.filter p) u.old_split
  have h₁ : u.cut.ends.filter p = [] := List.filter_eq_nil_iff.mpr (fun k hk => by simp [he k hk])
  have h₂ : (startsAt i u.starts).filter p = [] := List.filter_eq_nil_iff.mpr (fun k hk => by simp [hs k hk])
  simpa [Move.next, Cut.next, List.filter_append, h₁, h₂, List.append_assoc] using eqn.symm

end Move

namespace History

variable {m : ℕ} (H : History d (id : Fin n → Fin n) [] m)

/-- Incoming cuts only contain earlier starts, with at most one copy of each key. -/
theorem active_invariant (j : Fin (n+1)) :
    (H.active j).Nodup ∧ ∀ k ∈ H.active j, k.1.val < j.val := by
  induction j using Fin.induction with
  | zero => simp [H.first]
  | succ i ih =>
    let u := H.move i
    have hr : ∀ k ∈ H.active i.castSucc, k.1 < i := ih.2
    rw [← H.next i]
    refine ⟨u.next_nodup ih.1 hr, ?_⟩
    intro k hk
    rcases (u.mem_next ih.1).mp hk with ⟨ho,_⟩ | hs
    · exact Nat.lt_succ_of_lt (ih.2 k ho)
    · obtain ⟨r,_,rfl⟩ := mem_startsAt.mp hs
      exact Nat.lt_succ_self _

theorem mem_active_succ (i : Fin n) :
    k ∈ H.active i.succ ↔ (k ∈ H.active i.castSucc ∧ k ∉ (H.move i).cut.ends) ∨
      k ∈ startsAt i (H.move i).starts := by
  rw [← H.next i]
  exact (H.move i).mem_next (H.active_invariant i.castSucc).1

theorem end_exits (i : Fin n) (hk : k ∈ (H.move i).cut.ends) : k ∉ H.active i.succ := by
  rw [← H.next i]
  exact (H.move i).end_not_next (H.active_invariant i.castSucc).1 (H.active_invariant i.castSucc).2 hk

theorem exists_end (j : Fin (n+1)) (hk : k ∈ H.active j) :
    ∃ i : Fin n, j.val ≤ i.val ∧ k ∈ (H.move i).cut.ends := by
  induction j using Fin.reverseInduction with
  | last => simp [H.last] at hk
  | cast i ih =>
    by_cases he : k ∈ (H.move i).cut.ends
    · exact ⟨i, le_rfl, he⟩
    · obtain ⟨q,hq,heq⟩ := ih ((H.mem_active_succ i).mpr (Or.inl ⟨hk,he⟩))
      exact ⟨q,(Nat.le_succ i.val).trans hq,heq⟩

/-- Once a key has passed its start and is absent, it cannot enter again. -/
theorem absent_later {j q : Fin (n+1)} (hj : k.1.val < j.val) (hjq : j ≤ q)
    (hk : k ∉ H.active j) : k ∉ H.active q := by
  induction q using Fin.induction with
  | zero =>
    intro he
    simp [H.first] at he
  | succ i ih =>
    intro he
    by_cases hle : j ≤ i.castSucc
    · rcases (H.mem_active_succ i).mp he with ⟨ho,_⟩ | hs
      · exact ih hle ho
      · obtain ⟨r,_,hEq⟩ := mem_startsAt.mp hs
        have hstart : i = k.1 := congrArg Sigma.fst hEq
        exact (not_lt_of_ge hle) (show i.castSucc < j from hstart.symm ▸ hj)
    · have hEq : j = i.succ := Fin.ext (by
        simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at hjq hle ⊢
        omega)
      exact hk (hEq.symm ▸ he)

theorem end_unique {i j : Fin n} (hi : k ∈ (H.move i).cut.ends)
    (hj : k ∈ (H.move j).cut.ends) : i = j := by
  have aux (p q : Fin n) (hp : k ∈ (H.move p).cut.ends)
      (hq : k ∈ (H.move q).cut.ends) (hlt : p < q) : False := by
    have hmem := (H.move p).mem_ends_old hp
    have hs := (H.active_invariant p.castSucc).2 k hmem
    exact H.absent_later (Nat.lt_succ_of_lt hs)
      (show p.succ ≤ q.castSucc by exact hlt) (H.end_exits p hp) ((H.move q).mem_ends_old hq)
  exact le_antisymm (le_of_not_gt (aux j i hj hi)) (le_of_not_gt (aux i j hi hj))

theorem live_iff {j : Fin (n+1)} {i : Fin n} (he : k ∈ (H.move i).cut.ends) :
    k ∈ H.active j ↔ k.1.val < j.val ∧ j.val ≤ i.val := by
  constructor
  · intro hk
    obtain ⟨q,hq,heq⟩ := H.exists_end j hk
    exact ⟨(H.active_invariant j).2 k hk, H.end_unique heq he ▸ hq⟩
  · rintro ⟨hs,hj⟩
    by_contra ha
    exact H.absent_later hs (show j ≤ i.castSucc from hj) ha ((H.move i).mem_ends_old he)

end History

#print axioms History.active_invariant
#print axioms History.live_iff

end Permutree.SweepStep
```

### `SweepOrder.lean`

```lean
import SweepLifetimes

namespace Permutree.SweepStep
open scoped List

variable {A : Type*} {L R : List A} {x y : A}

theorem pair_sublist_append (hx : x ∈ L) (hy : y ∈ R) : [x,y] <+ L ++ R :=
  (List.singleton_sublist.mpr hx).append (List.singleton_sublist.mpr hy)

theorem sublist_filter_of_kept {p : A → Bool} {l r : List A}
    (hp : ∀ k ∈ l, p k = true) : l <+ r.filter p ↔ l <+ r :=
  ⟨fun h => h.trans List.filter_sublist, fun h => by
    simpa only [List.filter_eq_self.mpr hp] using h.filter p⟩

theorem pair_sublist_exclusive (hn : L.Nodup) (h : [x,y] <+ L) (h' : [y,x] <+ L) : False := by
  classical
  let p (a : A) := decide (a = x ∨ a = y)
  have sub : (L.filter p).toFinset ⊆ {x,y} := by
    intro a ha
    simpa [p] using (List.mem_filter.mp (List.mem_toFinset.mp ha)).2
  have hlen : (L.filter p).length ≤ 2 := by
    rw [← List.toFinset_card_of_nodup (hn.filter _)]
    exact (Finset.card_le_card sub).trans (Finset.card_insert_le _ _)
  have e : [x,y] = L.filter p :=
    ((sublist_filter_of_kept (p := p) (l := [x,y]) (by simp [p])).mpr h).eq_of_length_le hlen
  have e' : [y,x] = L.filter p :=
    ((sublist_filter_of_kept (p := p) (l := [y,x]) (by simp [p])).mpr h').eq_of_length_le hlen
  have hxy := congrArg List.head? (e.trans e'.symm)
  exact (List.nodup_cons.mp (hn.sublist h)).1 (by simpa using hxy)

variable {n : ℕ} {s : Fin n → ℕ} {d : Decoration s} {i : Fin n}
variable {old : List (Key s)} {a b k : Key s}

namespace Move

variable (u : Move d i old)

theorem positive_through (hi : s i ≠ 0) (ho : k ∈ old) (he : k ∉ u.cut.ends) :
    k ∈ u.cut.left ∨ k ∈ u.cut.right := by
  have hm : k ∉ u.cut.marks := fun h => hi (u.mark_zero h)
  rw [u.old_split] at ho
  simpa [he,hm] using ho

theorem left_not_right (hn : old.Nodup) (hl : k ∈ u.cut.left) : k ∉ u.cut.right := by
  rw [u.cut.split,List.nodup_iff_pairwise_ne,List.pairwise_append] at hn
  exact fun hr => hn.2.2 k (List.mem_append_left _ hl) k hr rfl

theorem old_left_new (ha : a ∈ u.cut.left) (hb : b ∈ startsAt i u.starts) : [a,b] <+ u.next := by
  exact List.sublist_append_of_sublist_left (pair_sublist_append (List.mem_append_left u.cut.marks ha) hb)

theorem new_old_right (ha : a ∈ startsAt i u.starts) (hb : b ∈ u.cut.right) : [a,b] <+ u.next := by
  exact pair_sublist_append (List.mem_append_right _ ha) hb

theorem starts_pair (hf : ∀ k ∈ old, k.1 < i)
    (ha : a ∈ startsAt i u.starts) (hb : b ∈ startsAt i u.starts) :
    [a,b] <+ u.next ↔ b.2.val < a.2.val := by
  classical
  let p (k : Key s) := decide (k = a ∨ k = b)
  have filterOld (l : List (Key s)) (hmem : ∀ k ∈ l, k ∈ old) : l.filter p = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro k hk
    have hka : k ≠ a := fun e => u.starts_fresh hf ha (e ▸ hmem _ hk)
    have hkb : k ≠ b := fun e => u.starts_fresh hf hb (e ▸ hmem _ hk)
    simp [p,hka,hkb]
  have hfilter : u.next.filter p = (startsAt i u.starts).filter p := by
    unfold Move.next Cut.next
    rw [List.filter_append,List.filter_append,List.filter_append,
        filterOld u.cut.left (fun k hk => u.old_split ▸ (by simp [hk])),
        filterOld u.cut.marks (fun k hk => u.mem_marks_old hk),
        filterOld u.cut.right (fun k hk => u.old_split ▸ (by simp [hk]))]
    simp
  constructor
  · intro hab
    have hsub := (sublist_filter_of_kept (p := p) (l := [a,b]) (by simp [p])).mpr hab
    rw [hfilter] at hsub
    exact (startsAt_pairwise i u.starts).forall_sublist (hsub.trans List.filter_sublist)
  · intro hab
    -- The two entries occur in one of the two orders in the inserted list.
    have hpair {p q : Key s} (hn : p ≠ q) {L : List (Key s)} (hp : p ∈ L) (hq : q ∈ L) :
        [p,q] <+ L ∨ [q,p] <+ L := by
      induction L with
      | nil => simp at hp
      | cons x L ih =>
        rcases List.mem_cons.mp hp with rfl | hp
        · exact Or.inl ((List.singleton_sublist.mpr ((List.mem_cons.mp hq).resolve_left (Ne.symm hn))).cons_cons _)
        · rcases List.mem_cons.mp hq with rfl | hq
          · exact Or.inr ((show [p] <+ L from List.singleton_sublist.mpr ((List.mem_cons.mp hp).resolve_left hn)).cons_cons q)
          · exact (ih hp hq).imp (List.Sublist.cons _) (List.Sublist.cons _)
    rcases hpair (fun e => (Nat.ne_of_gt hab) (congrArg (fun k : Key s => k.2.val) e)) ha hb with hp | hp
    · exact List.sublist_append_of_sublist_left (List.sublist_append_of_sublist_right hp)
    · exact (Nat.lt_asymm hab ((startsAt_pairwise i u.starts).forall_sublist hp)).elim

end Move

namespace History

variable {m : ℕ} (H : History d (id : Fin n → Fin n) [] m)

theorem starts_iff {i : Fin n} (he : k ∈ (H.move i).cut.ends) :
    ∀ j : Fin n, k ∈ startsAt j (H.move j).starts ↔ j = k.1 := by
  intro j
  constructor
  · intro hj
    obtain ⟨r,_,h⟩ := mem_startsAt.mp hj
    exact congrArg Sigma.fst h
  · rintro rfl
    have hk := (H.active_invariant i.castSucc).2 k ((H.move i).mem_ends_old he)
    have ho : k ∈ H.active k.1.succ := (H.live_iff he).mpr ⟨Nat.lt_succ_self _,hk⟩
    rcases (H.mem_active_succ k.1).mp ho with ⟨hp,_⟩ | hp
    · exact (lt_irrefl _ ((H.active_invariant k.1.castSucc).2 k hp)).elim
    · exact hp

theorem pair_persist {p q : Fin (n+1)} (hpq : p ≤ q)
    (hsa : a.1.val < p.val) (hsb : b.1.val < p.val)
    {i j : Fin n} (hea : a ∈ (H.move i).cut.ends) (heb : b ∈ (H.move j).cut.ends)
    (hai : q.val ≤ i.val) (hbj : q.val ≤ j.val) :
    [a,b] <+ H.active p ↔ [a,b] <+ H.active q := by
  classical
  induction q using Fin.induction with
  | zero =>
    have h := le_antisymm hpq (Fin.zero_le _)
    subst p
    rfl
  | succ h ih =>
    by_cases hp : p ≤ h.castSucc
    · refine (ih hp (Nat.le_of_succ_le hai) (Nat.le_of_succ_le hbj)).trans ?_
      let P (k : Key s) := decide (k = a ∨ k = b)
      have hstart (k : Key s) (hk : k ∈ startsAt h (H.move h).starts) : P k = false := by
        obtain ⟨r,_,rfl⟩ := mem_startsAt.mp hk
        have hl : p.val ≤ h.val := hp
        have hn₁ : h ≠ a.1 := fun e => (not_lt_of_ge hl) (e.symm ▸ hsa)
        have hn₂ : h ≠ b.1 := fun e => (not_lt_of_ge hl) (e.symm ▸ hsb)
        exact decide_eq_false (fun e => e.elim
          (fun e => hn₁ (congrArg Sigma.fst e)) (fun e => hn₂ (congrArg Sigma.fst e)))
      have hend (k : Key s) (hk : k ∈ (H.move h).cut.ends) : P k = false := by
        exact decide_eq_false (fun e => e.elim
          (fun e => (Nat.not_succ_le_self h.val) ((H.end_unique (e ▸ hk) hea).symm ▸ hai))
          (fun e => (Nat.not_succ_le_self h.val) ((H.end_unique (e ▸ hk) heb).symm ▸ hbj)))
      have heq := (H.move h).filter_persist P hend hstart
      rw [H.next h] at heq
      have hf₁ : ∀ k ∈ [a,b], P k = true := by simp [P]
      simpa only [sublist_filter_of_kept hf₁] using
        (Iff.of_eq (congrArg (fun l => [a,b] <+ l) heq.symm))
    · have hEq : p = h.succ := Fin.ext (by
        simp only [Fin.le_def,Fin.val_castSucc,Fin.val_succ] at hp hpq ⊢
        omega)
      subst p
      rfl

end History

#print axioms History.pair_persist

end Permutree.SweepStep
```

### `SweepDecode.lean`

```lean
import SweepOrder

namespace Permutree.SweepStep.History

open scoped List
open SArc

variable {n m : ℕ} {s : Fin n → ℕ} {d : Decoration s}

abbrev Complete (d : Decoration s) (m : ℕ) :=
  History d (id : Fin n → Fin n) [] m

def levelsFrom (q : Fin (n+1)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => q.val ≤ i.val)

@[simp] theorem mem_levelsFrom {q : Fin (n+1)} {i : Fin n} :
    i ∈ levelsFrom q ↔ q.val ≤ i.val := by simp [levelsFrom]

theorem levelsFrom_step (i : Fin n) :
    levelsFrom i.castSucc = insert i (levelsFrom i.succ) := by
  ext j
  simp only [mem_levelsFrom,Finset.mem_insert,Fin.val_castSucc,Fin.val_succ]
  rw [Fin.ext_iff]
  omega

variable (H : Complete d m)

noncomputable def arcOf (k : Key s) (j : Fin n) (he : k ∈ (H.move j).cut.ends) : SArc s := by
  classical
  refine ⟨k.1,j,Finset.univ.filter (fun i => k ∈ (H.move i).cut.passesRight),k.2,?_,?_⟩
  · exact (H.active_invariant j.castSucc).2 k ((H.move j).mem_ends_old he)
  · intro i hi
    have hr := (Finset.mem_filter.mp hi).2
    have hold := (H.live_iff he).mp ((H.move i).mem_passesRight_old hr)
    have hnext := (H.live_iff he).mp ((H.next i) ▸ (H.move i).survives_right hr)
    have hp : s i ≠ 0 := by
      intro hz
      simp [Cut.passesRight,hz] at hr
    exact mem_positiveInterior.mpr ⟨hold.1, hnext.2, hp⟩

@[simp] theorem arcOf_key (k : Key s) (j : Fin n) (he : k ∈ (H.move j).cut.ends) :
    (H.arcOf k j he).key = k := by cases k; rfl

theorem arcOf_right {k : Key s} {j i : Fin n} (he : k ∈ (H.move j).cut.ends) :
    i ∈ (H.arcOf k j he).right ↔ k ∈ (H.move i).cut.passesRight := by
  classical
  simp [arcOf]

theorem arcOf_left {k : Key s} {j i : Fin n} (he : k ∈ (H.move j).cut.ends)
    (hp : s i ≠ 0) (hs : k.1 < i) (hi : i < j) :
    i ∈ (H.arcOf k j he).left ↔ k ∈ (H.move i).cut.left := by
  have hn := (H.active_invariant i.castSucc).1
  have ha := (H.live_iff (j := i.castSucc) he).mpr ⟨hs,hi.le⟩
  have he' : k ∉ (H.move i).cut.ends := fun h => hi.ne (H.end_unique h he)
  have ht := (H.move i).positive_through hp ha he'
  rw [mem_left, H.arcOf_right he, (H.move i).right_mem_iff hp]
  exact ⟨fun h => ht.resolve_right h.2, fun h =>
    ⟨mem_positiveInterior.mpr ⟨hs,hi,hp⟩, (H.move i).left_not_right hn h⟩⟩

theorem arcOf_allowed {k : Key s} {j : Fin n} (he : k ∈ (H.move j).cut.ends) :
    Allowed d (H.arcOf k j he) := by
  intro ⟨i,hp⟩
  have ed : (level d i).2 = d ⟨i,hp⟩ := by simp [level,hp]
  rw [← ed]
  constructor
  · intro h
    have hr := ((H.move i).right_mem_iff hp).mp ((H.arcOf_right he).mp h)
    exact (H.move i).cut.right_allowed hp (List.length_pos_of_mem hr)
  · intro h
    have hi := mem_positiveInterior.mp (mem_left.mp h).1
    have hl := (H.arcOf_left he hp hi.1 hi.2.1).mp h
    exact (H.move i).cut.left_allowed hp (List.length_pos_of_mem hl)

theorem pair_at_overlap {a b : Key s} {i j q : Fin n}
    (hea : a ∈ (H.move i).cut.ends) (heb : b ∈ (H.move j).cut.ends)
    (ha : a.1 < q) (hb : b.1 < q) (hqi : q ≤ i) (hqj : q ≤ j) :
    (H.arcOf a i hea).LeftOf (H.arcOf b j heb) → [a,b] <+ H.active q.castSucc := by
  intro hl
  have persist (p : Fin n) (hpa : a.1 ≤ p) (hpb : b.1 ≤ p) (hpq : p < q) :
      [a,b] <+ H.active p.succ → [a,b] <+ H.active q.castSucc :=
    (H.pair_persist (p := p.succ) hpq (Nat.lt_succ_of_le hpa) (Nat.lt_succ_of_le hpb) hea heb hqi hqj).mp
  rcases hl with ⟨hst,hside⟩ | ⟨hst,hr⟩ | ⟨hst,hside⟩
  · change a.1 < b.1 at hst
    apply persist b.1 hst.le le_rfl hb
    rw [← H.next b.1]
    have hbp : s b.1 ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt b.2.isLt)
    exact (H.move b.1).old_left_new ((H.arcOf_left hea hbp hst (hb.trans_le hqi)).mp hside)
      ((H.starts_iff heb _).mpr rfl)
  · change a.1 = b.1 at hst
    apply persist a.1 le_rfl hst.ge ha
    rw [← H.next a.1]
    apply ((H.move a.1).starts_pair (H.active_invariant a.1.castSucc).2
      ((H.starts_iff hea _).mpr rfl) ((H.starts_iff heb _).mpr hst)).mpr
    change b.2.val + 1 < a.2.val + 1 at hr
    omega
  · change b.1 < a.1 at hst
    apply persist a.1 le_rfl hst.le ha
    rw [← H.next a.1]
    have hap : s a.1 ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt a.2.isLt)
    exact (H.move a.1).new_old_right ((H.starts_iff hea _).mpr rfl)
      (((H.move a.1).right_mem_iff hap).mp ((H.arcOf_right heb).mp hside))

theorem overlap_leftOf {a b : Key s} {i j q : Fin n}
    (hea : a ∈ (H.move i).cut.ends) (heb : b ∈ (H.move j).cut.ends)
    (ha : a.1 < q) (hb : b.1 < q) (hqi : q ≤ i) (hqj : q ≤ j)
    (hp : [a,b] <+ H.active q.castSucc) :
    (H.arcOf a i hea).LeftOf (H.arcOf b j heb) := by
  have hn := (H.active_invariant q.castSucc).1
  rcases leftOf_trichotomy (a := H.arcOf a i hea) (b := H.arcOf b j heb) (ha.trans_le hqj) (hb.trans_le hqi) with hl | hk | hr
  · exact hl
  · have e := (H.arcOf_key a i hea).symm.trans
      ((sameKey_iff_key_eq.mp hk).trans (H.arcOf_key b j heb))
    subst b
    exact (List.nodup_cons.mp (hn.sublist hp)).1 (by simp) |>.elim
  · exact (pair_sublist_exclusive hn hp (H.pair_at_overlap heb hea hb ha hqj hqi hr)).elim

theorem arcOf_sideIncl {a b : Key s} {i j : Fin n}
    (hea : a ∈ (H.move i).cut.ends) (heb : b ∈ (H.move j).cut.ends)
    (hl : (H.arcOf a i hea).LeftOf (H.arcOf b j heb)) :
    (H.arcOf a i hea).SideIncl (H.arcOf b j heb) := by
  intro q hq har
  obtain ⟨has,haf⟩ := mem_between.mp hq.1
  obtain ⟨hbs,hbf⟩ := mem_between.mp hq.2
  have hp := (mem_positiveInterior.mp ((H.arcOf a i hea).right_subset har)).2.2
  have hactive := H.pair_at_overlap hea heb has hbs haf.le hbf.le hl
  have hr := ((H.move q).right_mem_iff hp).mp ((H.arcOf_right hea).mp har)
  by_contra hbr
  have hbl := (H.arcOf_left heb hp hbs hbf).mp (mem_left.mpr ⟨mem_positiveInterior.mpr ⟨hbs,hbf,hp⟩, hbr⟩)
  have hr' : [b,a] <+ H.active q.castSucc := by
    rw [(H.move q).cut.split]
    exact pair_sublist_append (List.mem_append_left _ hbl) hr
  exact pair_sublist_exclusive (H.active_invariant q.castSucc).1 hactive hr'

theorem arcOf_noncrossing_of_lt {a b : Key s} {i j : Fin n}
    (hea : a ∈ (H.move i).cut.ends) (heb : b ∈ (H.move j).cut.ends) (hij : i < j) :
    (H.arcOf a i hea).orderedNoncrossing (H.arcOf b j heb) := by
  rw [orderedNoncrossing_iff]
  refine ⟨hij,?_⟩
  by_cases hb : i ≤ b.1
  · exact Or.inl hb
  have hbs : b.1 < i := lt_of_not_ge hb
  have has : a.1 < i := (H.arcOf a i hea).start_lt_finish
  have hne : a ≠ b := fun e => hij.ne (H.end_unique (e ▸ hea) heb)
  have notSame : ¬ (H.arcOf a i hea).SameKey (H.arcOf b j heb) := by
    rw [sameKey_iff_key_eq,H.arcOf_key,H.arcOf_key]
    exact hne
  rcases leftOf_trichotomy (a := H.arcOf a i hea) (b := H.arcOf b j heb) (has.trans hij) hbs with hl | hk | hl
  · refine Or.inr (Or.inr (Or.inl ⟨hl,H.arcOf_sideIncl hea heb hl,?_⟩))
    intro hs
    have hp := (mem_positiveInterior.mp (mem_left.mp hs).1).2.2
    have hbl := (H.arcOf_left heb hp hbs hij).mp hs
    have hap : a ∈ (H.move i).cut.pivot := by rw [(H.move i).pivot_partition]; simp [hea]
    have hpair : [b,a] <+ H.active i.castSucc := by
      rw [(H.move i).cut.split]
      exact List.sublist_append_of_sublist_left (pair_sublist_append hbl hap)
    exact pair_sublist_exclusive (H.active_invariant i.castSucc).1
      (H.pair_at_overlap hea heb has hbs le_rfl hij.le hl) hpair
  · exact (notSame hk).elim
  · refine Or.inr (Or.inl ⟨hl,H.arcOf_sideIncl heb hea hl,?_⟩)
    intro hs
    have hp := (mem_positiveInterior.mp ((H.arcOf b j heb).right_subset hs)).2.2
    have hbr := ((H.move i).right_mem_iff hp).mp ((H.arcOf_right heb).mp hs)
    have hap : a ∈ (H.move i).cut.pivot := by rw [(H.move i).pivot_partition]; simp [hea]
    have hpair : [a,b] <+ H.active i.castSucc := by
      rw [(H.move i).cut.split]
      exact pair_sublist_append (List.mem_append_right _ hap) hbr
    exact pair_sublist_exclusive (H.active_invariant i.castSucc).1
      (H.pair_at_overlap heb hea hbs has hij.le le_rfl hl) hpair

/-- At most one event at each level, including a mark on a retained key. -/
noncomputable def occupied : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => (H.move i).cut.pivot ≠ [])

theorem mem_occupied {i : Fin n} : i ∈ H.occupied ↔ ∃ k, k ∈ (H.move i).cut.pivot := by
  classical
  rw [occupied, Finset.mem_filter]
  simp only [Finset.mem_univ,true_and]
  apply not_iff_comm.mp
  simpa only [not_exists] using List.eq_nil_iff_forall_not_mem.symm

theorem pivot_old {i : Fin n} {k : Key s} (hk : k ∈ (H.move i).cut.pivot) :
    k ∈ H.active i.castSucc := by
  have e := (H.move i).cut.split
  exact e ▸ (by simp [hk])

theorem occupied_grade (q : Fin (n+1)) : (H.occupied ∩ levelsFrom q).card = H.grade q := by
  classical
  induction q using Fin.reverseInduction with
  | last =>
    rw [H.last_grade]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    exact (not_le_of_gt i.isLt) (mem_levelsFrom.mp (Finset.mem_inter.mp hi).2)
  | cast i ih =>
    rw [H.next_grade i, levelsFrom_step, ← ih]
    have hsize := (H.move i).length_pivot_le_one
    have hweight := (H.move i).occupied_length
    by_cases hi : i ∈ H.occupied
    · have e : H.occupied ∩ insert i (levelsFrom i.succ) =
          insert i (H.occupied ∩ levelsFrom i.succ) := by
        ext j
        simp only [Finset.mem_inter,Finset.mem_insert]
        aesop
      have hnot : i ∉ H.occupied ∩ levelsFrom i.succ := by simp
      have hw : (H.move i).weight = 1 := by
        obtain ⟨k,hk⟩ := H.mem_occupied.mp hi
        have := List.length_pos_of_mem hk
        omega
      rw [e,Finset.card_insert_of_notMem hnot,hw,Nat.add_comm]
    · have e : H.occupied ∩ insert i (levelsFrom i.succ) =
          H.occupied ∩ levelsFrom i.succ := by
        ext j
        simp only [Finset.mem_inter,Finset.mem_insert]
        aesop
      have hw : (H.move i).weight = 0 := by
        rw [← hweight,List.length_eq_zero_iff]
        exact List.eq_nil_iff_forall_not_mem.mpr (fun k hk => hi (H.mem_occupied.mpr ⟨k,hk⟩))
      rw [e,hw,Nat.zero_add]

noncomputable def keyAt (i : {i // i ∈ H.occupied}) : Key s :=
  (H.mem_occupied.mp i.property).choose

theorem keyAt_mem (i : {i // i ∈ H.occupied}) :
    H.keyAt i ∈ (H.move i.val).cut.pivot :=
  (H.mem_occupied.mp i.property).choose_spec

noncomputable def endAt (i : {i // i ∈ H.occupied}) : Fin n :=
  (H.exists_end i.val.castSucc (H.pivot_old (H.keyAt_mem i))).choose

theorem endAt_spec (i : {i // i ∈ H.occupied}) :
    i.val ≤ H.endAt i ∧ H.keyAt i ∈ (H.move (H.endAt i)).cut.ends :=
  (H.exists_end i.val.castSucc (H.pivot_old (H.keyAt_mem i))).choose_spec

noncomputable def eventAt (i : {i // i ∈ H.occupied}) : EndEvent s :=
  (H.arcOf (H.keyAt i) (H.endAt i) (H.endAt_spec i).2, i.val)

noncomputable def decoded : Finset (EndEvent s) :=
  H.occupied.attach.map ⟨H.eventAt, fun _ _ e => Subtype.ext (congrArg Prod.snd e)⟩

theorem decoded_card : H.decoded.card = m := by
  rw [decoded,Finset.card_map,Finset.card_attach]
  refine Eq.trans ?_ H.first_grade
  have h := H.occupied_grade 0
  rwa [show levelsFrom (0 : Fin (n+1)) = Finset.univ by ext i; simp,Finset.inter_univ] at h

theorem mem_decoded {a : SArc s} {i : Fin n} :
    (a,i) ∈ H.decoded ↔ ∃ k ∈ (H.move i).cut.pivot,
      ∃ j : Fin n, ∃ he : k ∈ (H.move j).cut.ends, H.arcOf k j he = a := by
  constructor
  · intro h
    obtain ⟨x,_,he⟩ := Finset.mem_map.mp h
    have hxi : x.val = i := congrArg Prod.snd he
    exact ⟨H.keyAt x,hxi ▸ H.keyAt_mem x,H.endAt x,(H.endAt_spec x).2,congrArg Prod.fst he⟩
  · rintro ⟨k,hk,j,he,rfl⟩
    let x : {i // i ∈ H.occupied} := ⟨i,H.mem_occupied.mpr ⟨k,hk⟩⟩
    have hkey : H.keyAt x = k := (H.move i).pivot_mem_unique (H.keyAt_mem x) hk
    have hend := H.end_unique (hkey ▸ (H.endAt_spec x).2) he
    apply Finset.mem_map.mpr
    refine ⟨x,Finset.mem_attach _ _,?_⟩
    change H.eventAt x = _
    refine Prod.ext ?_ (show x.val = i from rfl)
    change H.arcOf (H.keyAt x) (H.endAt x) (H.endAt_spec x).2 = _
    have congrArc {k l : Key s} {j q : Fin n} (hk : k = l) (hj : j = q)
        (he : k ∈ (H.move j).cut.ends) (hf : l ∈ (H.move q).cut.ends) :
        H.arcOf k j he = H.arcOf l q hf := by
      subst l q
      rfl
    exact congrArc hkey hend (H.endAt_spec x).2 he

theorem decode_sweep_is_marked : IsMarked d H.decoded := by
  constructor
  · rintro ⟨a,i⟩ hi
    obtain ⟨k,hk,j,he,rfl⟩ := H.mem_decoded.mp hi
    have h := (H.live_iff he).mp (H.pivot_old hk)
    refine ⟨H.arcOf_allowed he,h.1,h.2,?_,?_⟩
    · intro hlt
      have hn : k ∉ (H.move i).cut.ends := fun h => hlt.ne (H.end_unique h he)
      rw [(H.move i).pivot_partition,List.mem_append] at hk
      exact (H.move i).mark_zero (hk.resolve_left hn)
    · have jp : k ∈ (H.move j).cut.pivot := by rw [(H.move j).pivot_partition]; simp [he]
      exact H.mem_decoded.mpr ⟨k,jp,j,he,rfl⟩
  · rintro ⟨a,i⟩ ha ⟨b,j⟩ hb hne
    obtain ⟨k,hk,p,hep,rfl⟩ := H.mem_decoded.mp ha
    obtain ⟨l,hl,q,heq,rfl⟩ := H.mem_decoded.mp hb
    change (H.arcOf k p hep,i) ≠ (H.arcOf l q heq,j) at hne
    have sameEnd {x y : Key s} {f : Fin n} (hx : x ∈ (H.move f).cut.ends)
        (hy : y ∈ (H.move f).cut.ends) : H.arcOf x f hx = H.arcOf y f hy := by
      have h (z : Key s) (hz : z ∈ (H.move f).cut.ends) : z ∈ (H.move f).cut.pivot := by
        rw [(H.move f).pivot_partition]; simp [hz]
      have hkey := (H.move f).pivot_mem_unique (h x hx) (h y hy)
      subst y
      rfl
    constructor
    · rintro rfl
      have hkey := (H.move i).pivot_mem_unique hk hl
      subst l
      have hEnd := H.end_unique hep heq
      subst q
      exact hne rfl
    · intro hab
      have hEnd : p ≠ q := fun e => hab (by subst q; exact sameEnd hep heq)
      refine ⟨?_,?_⟩
      · rcases lt_or_gt_of_ne hEnd with hlt | hlt
        · exact Or.inl (H.arcOf_noncrossing_of_lt hep heq hlt)
        · exact Or.inr (H.arcOf_noncrossing_of_lt heq hep hlt)
      · simpa only [H.arcOf_key] using (fun e => hEnd (H.end_unique (e ▸ hep) heq) : k ≠ l)

noncomputable def decode : MarkedOfSize d m :=
  ⟨H.decoded,H.decode_sweep_is_marked,H.decoded_card⟩

#print axioms arcOf_noncrossing_of_lt
#print axioms decode_sweep_is_marked
#print axioms decoded_card

end Permutree.SweepStep.History
```

### `SweepEncode.lean`

```lean
import SweepDecode
import Mathlib.Data.List.Sort

namespace Permutree.SweepStep

open SArc
open scoped List

variable {n m : ℕ} {s : Fin n → ℕ} {d : Decoration s} {M : Finset (EndEvent s)}

def Live (M : Finset (EndEvent s)) (q : Fin (n+1)) (a : SArc s) : Prop :=
  (a,a.finish) ∈ M ∧ a.start.val < q.val ∧ q.val ≤ a.finish.val

theorem live_key_injective (hM : IsMarked d M) {a b : SArc s}
    (ha : (a,a.finish) ∈ M) (hb : (b,b.finish) ∈ M) (hk : a.key = b.key) : a = b := by
  by_contra h
  exact ((hM.2 ha hb (fun e => h (congrArg Prod.fst e))).2 h).2 hk

theorem marked_event_unique (hM : IsMarked d M) {a b : SArc s} {i : Fin n}
    (ha : (a,i) ∈ M) (hb : (b,i) ∈ M) : a = b := by
  by_contra h
  exact (hM.2 ha hb (fun e => h (congrArg Prod.fst e))).1 rfl

instance : Std.Antisymm (LeftOf (s := s)) :=
  ⟨fun _ _ h h' => (leftOf_exclusive h h').elim⟩

instance : Std.Irrefl (LeftOf (s := s)) :=
  ⟨fun _ h => leftOf_exclusive h h⟩

private theorem exists_activeList (hM : IsMarked d M) (q : Fin (n+1)) :
    ∃ L : List (SArc s), L.Pairwise LeftOf ∧ ∀ a, a ∈ L ↔ Live M q a := by
  classical
  by_cases hq : q.val < n
  · let i : Fin n := ⟨q.val,hq⟩
    let rel (a b : {a : SArc s // Live M q a}) := a.val = b.val ∨ a.val.LeftOf b.val
    let : IsTrans _ rel := ⟨fun a b c h h' => by
      rcases h with h | h <;> rcases h' with h' | h'
      · exact Or.inl (h.trans h')
      · exact Or.inr (h ▸ h')
      · exact Or.inr (h' ▸ h)
      · exact Or.inr (active_transitive hM (h := i) a.property b.property c.property h h')⟩
    let : Std.Total rel := ⟨fun a b => by
      by_cases h : a.val = b.val
      · exact Or.inl (Or.inl h)
      · exact (active_trichotomy hM (h := i) a.property b.property h).imp Or.inr Or.inr⟩
    let : Std.Antisymm rel := ⟨fun a b h h' => by
      apply Subtype.ext
      rcases h with h | h
      · exact h
      · rcases h' with h' | h'
        · exact h'.symm
        · exact (leftOf_exclusive h h').elim⟩
    let L := (Finset.univ.sort rel : List {a : SArc s // Live M q a})
    have hs : L.Pairwise rel := Finset.pairwise_sort _ _
    have hn : L.Nodup := Finset.sort_nodup _ _
    refine ⟨L.map Subtype.val, List.pairwise_map.mpr ?_,?_⟩
    · exact hs.imp₂ (fun a b h hne => h.resolve_left (fun e => hne (Subtype.ext e)))
        (List.nodup_iff_pairwise_ne.mp hn)
    · intro a
      constructor
      · rintro ha
        obtain ⟨b,_,rfl⟩ := List.mem_map.mp ha
        exact b.property
      · intro ha
        exact List.mem_map.mpr ⟨⟨a,ha⟩,by simp [L],rfl⟩
  · refine ⟨[],by simp,fun a => ?_⟩
    have hf := a.finish.isLt
    simp only [List.not_mem_nil, false_iff, Live]
    omega

noncomputable def activeList (hM : IsMarked d M) (q : Fin (n+1)) :=
  (exists_activeList hM q).choose

theorem activeList_sorted (hM : IsMarked d M) (q : Fin (n+1)) :
    (activeList hM q).Pairwise LeftOf :=
  (exists_activeList hM q).choose_spec.1

theorem mem_activeList (hM : IsMarked d M) {q : Fin (n+1)} {a : SArc s} :
    a ∈ activeList hM q ↔ Live M q a :=
  (exists_activeList hM q).choose_spec.2 a

private theorem exists_pointEvent (hM : IsMarked d M) (i : Fin n) :
    ∃ e : Option (SArc s), ∀ a, e = some a ↔ (a,i) ∈ M := by
  classical
  by_cases h : ∃ a, (a,i) ∈ M
  · obtain ⟨a,ha⟩ := h
    exact ⟨some a, fun b => ⟨fun e => Option.some.inj e ▸ ha,
      fun hb => congrArg some (marked_event_unique hM ha hb)⟩⟩
  · exact ⟨none, fun a => by simp [show (a,i) ∉ M from fun ha => h ⟨a,ha⟩]⟩

noncomputable def pointEvent (hM : IsMarked d M) (i : Fin n) : Option (SArc s) :=
  (exists_pointEvent hM i).choose

theorem pointEvent_spec (hM : IsMarked d M) {i : Fin n} {a : SArc s} :
    pointEvent hM i = some a ↔ (a,i) ∈ M :=
  (exists_pointEvent hM i).choose_spec a

theorem pointEvent_active (hM : IsMarked d M) {i : Fin n} {a : SArc s}
    (ha : pointEvent hM i = some a) : a ∈ activeList hM i.castSucc := by
  obtain ⟨_,hs,he,_,hr⟩ := hM.1 _ ((pointEvent_spec hM).mp ha)
  exact (mem_activeList hM).mpr ⟨hr,hs,he⟩

theorem pointEvent_pos (hM : IsMarked d M) {i : Fin n} (hp : s i ≠ 0)
    {a : SArc s} (ha : pointEvent hM i = some a) : a.finish = i := by
  have h := hM.1 _ ((pointEvent_spec hM).mp ha)
  exact h.2.2.1.eq_or_lt.elim Eq.symm (fun he => (hp (h.2.2.2.1 he)).elim)

theorem pointEvent_end_iff (hM : IsMarked d M) {i : Fin n} (hp : s i ≠ 0) (a : SArc s) :
    pointEvent hM i = some a ↔ a ∈ activeList hM i.castSucc ∧ a.finish = i := by
  constructor
  · exact fun h => ⟨pointEvent_active hM h, pointEvent_pos hM hp h⟩
  · rintro ⟨ha,e⟩
    have hm := ((mem_activeList hM).mp ha).1
    rw [e] at hm
    exact (pointEvent_spec hM).mpr hm

structure ArcSplit (hM : IsMarked d M) (i : Fin n) where
  left : List (SArc s)
  right : List (SArc s)
  split : activeList hM i.castSucc = left ++ (pointEvent hM i).toList ++ right
  positive : s i ≠ 0 → IsPositiveCut i (pointEvent hM i) (activeList hM i.castSucc) left right
  idle : s i = 0 → pointEvent hM i = none → left = []

theorem exists_arcSplit (hM : IsMarked d M) (i : Fin n) : Nonempty (ArcSplit hM i) := by
  by_cases hp : s i = 0
  · cases he : pointEvent hM i with
    | none => exact ⟨⟨[],activeList hM i.castSucc,by simp [he],fun h => (h hp).elim,fun _ _ => rfl⟩⟩
    | some a =>
      obtain ⟨l,r,heq⟩ := List.mem_iff_append.mp (pointEvent_active hM he)
      exact ⟨⟨l,r,by simpa [he] using heq,fun h => (h hp).elim,fun _ hn => by simp [he] at hn⟩⟩
  · obtain ⟨l,r,hc⟩ := positiveCut_exists hM i hp _ (fun a ha => show Live M i.castSucc a from (mem_activeList hM).mp ha)
      (activeList_sorted hM _) _ (pointEvent_end_iff hM hp)
    exact ⟨⟨l,r,hc.1,fun _ => hc,fun h => (hp h).elim⟩⟩

noncomputable def arcSplit (hM : IsMarked d M) (i : Fin n) : ArcSplit hM i :=
  Classical.choice (exists_arcSplit hM i)

noncomputable def startList (hM : IsMarked d M) (i : Fin n) : List (SArc s) :=
  (activeList hM i.succ).filter (fun a => a.start == i)

theorem mem_startList (hM : IsMarked d M) {i : Fin n} {a : SArc s} :
    a ∈ startList hM i ↔ (a,a.finish) ∈ M ∧ a.start = i := by
  rw [startList,List.mem_filter,beq_iff_eq,mem_activeList hM]
  exact ⟨fun h => ⟨h.1.1,h.2⟩,fun ⟨ha,h⟩ => ⟨⟨ha, h ▸ Nat.lt_succ_self _,
    Nat.succ_le_of_lt (h ▸ a.start_lt_finish)⟩,h⟩⟩

theorem startList_order (hM : IsMarked d M) (i : Fin n) :
    (startList hM i).Pairwise LeftOf :=
  (activeList_sorted hM i.succ).sublist List.filter_sublist

theorem keys_startList (hM : IsMarked d M) (i : Fin n) :
    ∃ S : Finset (Fin (s i)), startsAt i S = (startList hM i).map SArc.key := by
  classical
  let L := startList hM i
  let label (a : {a // a ∈ L}) : Fin (s i) :=
    ((mem_startList hM).mp a.property).2 ▸ a.val.label
  let S := (L.attach.map label).toFinset
  refine ⟨S,?_⟩
  let rel (a b : Key s) := b.2.val < a.2.val
  let : Std.Irrefl rel := ⟨fun _ => Nat.lt_irrefl _⟩
  let : Std.Antisymm rel := ⟨fun _ _ h h' => (Nat.lt_asymm h h').elim⟩
  refine List.Pairwise.eq_of_mem_iff (r := rel) (startsAt_pairwise i S) ?_ ?_
  · rw [List.pairwise_map]
    refine (startList_order hM i).imp_of_mem ?_
    intro a b ha hb h
    have ha' := ((mem_startList hM).mp ha).2
    have hb' := ((mem_startList hM).mp hb).2
    rcases h with h | h | h
    · exact (h.1.ne (ha'.trans hb'.symm)).elim
    · exact Nat.lt_of_succ_lt_succ h.2
    · exact (h.1.ne (hb'.trans ha'.symm)).elim
  · intro k
    simp only [mem_startsAt,List.mem_map,List.mem_toFinset,S]
    have he (a : {a // a ∈ L}) : (⟨i,label a⟩ : Key s) = a.val.key := by
      unfold label
      have aux {x y : Fin n} (h : x = y) (r : Fin (s x)) :
          (⟨y,h ▸ r⟩ : Key s) = ⟨x,r⟩ := by subst y; rfl
      exact aux ((mem_startList hM).mp a.property).2 a.val.label
    constructor
    · rintro ⟨t,⟨a,_,rfl⟩,rfl⟩
      exact ⟨a.val,a.property,(he a).symm⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨label ⟨a,ha⟩,⟨⟨a,ha⟩,by simp,rfl⟩,he ⟨a,ha⟩⟩

namespace ArcSplit

variable {hM : IsMarked d M} {i : Fin n} (c : ArcSplit hM i)

noncomputable def ends (_c : ArcSplit hM i) : List (SArc s) := by
  classical
  exact (pointEvent hM i).toList.filter (fun a => decide (a.finish = i))

noncomputable def marks (_c : ArcSplit hM i) : List (SArc s) := by
  classical
  exact (pointEvent hM i).toList.filter (fun a => decide (a.finish ≠ i))

theorem mem_ends {a : SArc s} : a ∈ c.ends ↔ (a,i) ∈ M ∧ a.finish = i := by
  classical
  simp [ends, List.mem_filter, Option.mem_toList, pointEvent_spec hM, eq_comm]

theorem mem_marks {a : SArc s} : a ∈ c.marks ↔ (a,i) ∈ M ∧ a.finish ≠ i := by
  classical
  rw [marks,List.mem_filter,decide_eq_true_eq,Option.mem_toList]
  rw [pointEvent_spec hM]

theorem partition : (pointEvent hM i).toList = c.ends ++ c.marks := by
  classical
  cases he : pointEvent hM i with
  | none => simp [ends,marks,he]
  | some a => by_cases h : a.finish = i <;> simp [ends,marks,he,h]

theorem left_old {a : SArc s} (h : a ∈ c.left) : a ∈ activeList hM i.castSucc :=
  c.split ▸ List.mem_append_left _ (List.mem_append_left _ h)

theorem right_old {a : SArc s} (h : a ∈ c.right) : a ∈ activeList hM i.castSucc :=
  c.split ▸ List.mem_append_right _ h

theorem marks_empty_positive (hi : s i ≠ 0) : c.marks = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro a ha
  obtain ⟨ha,hn⟩ := c.mem_marks.mp ha
  exact hn (pointEvent_pos hM hi ((pointEvent_spec hM).mpr ha))

theorem starts_empty_zero (hM : IsMarked d M) (hi : s i = 0) : startList hM i = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro a ha
  exact a.start_pos (((mem_startList hM).mp ha).2.symm ▸ hi)

/-- Delete the end, keep a mark in place and splice in all simultaneous starts. -/
theorem next_arcs :
    c.left ++ c.marks ++ startList hM i ++ c.right = activeList hM i.succ := by
  have hOld := activeList_sorted hM i.castSucc
  have hp : (c.left ++ c.marks ++ c.right).Pairwise LeftOf := by
    apply List.Pairwise.sublist _ hOld
    rw [c.split,c.partition]
    simp only [List.append_assoc]
    exact List.Sublist.append (List.Sublist.refl _) (List.sublist_append_right _ _)
  refine List.Pairwise.eq_of_mem_iff (r := LeftOf) ?_ (activeList_sorted hM i.succ) ?_
  · by_cases hz : s i = 0
    · simpa [starts_empty_zero hM hz] using hp
    rw [c.marks_empty_positive hz,List.append_nil] at hp ⊢
    have hc := c.positive hz
    obtain ⟨hl,hr,hlr⟩ := List.pairwise_append.mp hp
    apply List.pairwise_append.mpr
    refine ⟨List.pairwise_append.mpr ⟨hl,startList_order hM i,?_⟩,hr,?_⟩
    · intro a ha b hb
      have hs := ((mem_startList hM).mp hb).2
      have hside := hc.2.1 a ha
      exact Or.inl ⟨hs ▸ (mem_positiveInterior.mp (mem_left.mp hside).1).1,hs ▸ hside⟩
    · intro a ha b hb
      rcases List.mem_append.mp ha with ha | ha
      · exact hlr a ha b hb
      · have hs := ((mem_startList hM).mp ha).2
        have hside := hc.2.2 b hb
        exact Or.inr (Or.inr ⟨hs ▸ (mem_positiveInterior.mp (b.right_subset hside)).1,hs ▸ hside⟩)
  · intro a
    rw [mem_activeList hM]
    have old : a ∈ activeList hM i.castSucc ↔
        a ∈ c.left ∨ a ∈ (pointEvent hM i).toList ∨ a ∈ c.right := by
      rw [c.split]
      simp
    have excl (hp : a ∈ (pointEvent hM i).toList) : a ∉ c.left ∧ a ∉ c.right := by
      have hn := hOld.nodup
      rw [c.split,List.nodup_iff_pairwise_ne,List.pairwise_append,List.pairwise_append] at hn
      exact ⟨fun h => hn.1.2.2 _ h _ hp rfl,fun h => hn.2.2 _ (List.mem_append_right _ hp) _ h rfl⟩
    have till (ha : a ∈ activeList hM i.castSucc) (he : a.finish ≠ i) :
        Live M i.succ a := by
      obtain ⟨hm,hs,hf⟩ := (mem_activeList hM).mp ha
      have h : i < a.finish := lt_of_le_of_ne hf he.symm
      exact ⟨hm,Nat.lt_succ_of_lt hs,h⟩
    simp only [List.mem_append,mem_startList hM,c.mem_marks]
    constructor
    · rintro (((ha | ⟨hm,he⟩) | ⟨hm,hs⟩) | ha)
      · apply till (c.left_old ha)
        intro he
        have hm := ((mem_activeList hM).mp (c.left_old ha)).1
        have hpi : (a,i) ∈ M := by simpa only [he] using hm
        have hpoint := (pointEvent_spec hM).mpr hpi
        exact (excl (by simp [hpoint])).1 ha
      · exact till (pointEvent_active hM ((pointEvent_spec hM).mpr hm)) he
      · exact ⟨hm,hs ▸ Nat.lt_succ_self _,hs ▸ a.start_lt_finish⟩
      · apply till (c.right_old ha)
        intro he
        have hm := ((mem_activeList hM).mp (c.right_old ha)).1
        have hpi : (a,i) ∈ M := by simpa only [he] using hm
        have hpoint := (pointEvent_spec hM).mpr hpi
        exact (excl (by simp [hpoint])).2 ha
    · rintro ⟨hm,hs,hf⟩
      by_cases he : a.start = i
      · exact Or.inl (Or.inr ⟨hm,he⟩)
      · have hst : a.start < i := by
          have hl : a.start ≤ i := Nat.le_of_lt_succ hs
          exact lt_of_le_of_ne hl he
        have hh : i < a.finish := hf
        rcases old.mp ((mem_activeList hM).mpr ⟨hm,hst,hh.le⟩) with hl | hp | hr
        · exact Or.inl (Or.inl (Or.inl hl))
        · have ho : pointEvent hM i = some a := by
            cases h : pointEvent hM i <;> simp_all
          exact Or.inl (Or.inl (Or.inr ⟨(pointEvent_spec hM).mp ho,hh.ne.symm⟩))
        · exact Or.inr hr

end ArcSplit

namespace ArcSplit

variable {hM : IsMarked d M} {i : Fin n} (c : ArcSplit hM i)

noncomputable def endFlag : Bool := !c.ends.isEmpty
noncomputable def markFlag : Bool := !c.marks.isEmpty

theorem flagEnd {a : SArc s} (ha : pointEvent hM i = some a) :
    c.endFlag = decide (a.finish = i) := by
  classical
  by_cases he : a.finish = i <;> simp [endFlag,ends,ha,he]

theorem flagMark {a : SArc s} (ha : pointEvent hM i = some a) :
    c.markFlag = decide (a.finish ≠ i) := by
  classical
  by_cases he : a.finish = i <;> simp [markFlag,marks,ha,he]

theorem flagIdle (he : pointEvent hM i = none) : c.endFlag = false ∧ c.markFlag = false := by
  simp [endFlag,markFlag,ends,marks,he]

theorem positive_length {a : SArc s} (h : pointEvent hM i = some a) :
    0 < ((activeList hM i.castSucc).map SArc.key).length := by
  rw [List.length_map]
  exact List.length_pos_of_mem (pointEvent_active hM h)

noncomputable def event : Permutree.Event (level d i) ((activeList hM i.castSucc).map SArc.key).length :=
  ⟨(c.endFlag,c.markFlag),by
    classical
    cases he : pointEvent hM i with
    | none => simp [(c.flagIdle he).1,(c.flagIdle he).2]
    | some a =>
      have ha := hM.1 _ ((pointEvent_spec hM).mp he)
      have hl := positive_length he
      rw [List.length_map] at hl
      by_cases hf : a.finish = i
      · simp [c.flagEnd he,c.flagMark he,hf,hl]
      · have hzero : (level d i).1 = 0 := ha.2.2.2.1 (lt_of_le_of_ne ha.2.2.1 (Ne.symm hf))
        simp [c.flagEnd he,c.flagMark he,hf,hl,hzero]⟩

theorem event_weight : c.event.weight = (pointEvent hM i).toList.length := by
  classical
  change c.endFlag.toNat + c.markFlag.toNat = _
  cases he : pointEvent hM i with
  | none => simp [(c.flagIdle he).1,(c.flagIdle he).2]
  | some a =>
    by_cases hf : a.finish = i <;> simp [c.flagEnd he,c.flagMark he,hf]

noncomputable def cut : Cut d i ((activeList hM i.castSucc).map SArc.key) c.event where
  left := c.left.map SArc.key
  pivot := (pointEvent hM i).toList.map SArc.key
  right := c.right.map SArc.key
  split := by simpa only [List.map_append] using congrArg (List.map SArc.key) c.split
  pivot_length := by
    classical
    change _ = (c.endFlag || c.markFlag).toNat
    cases he : pointEvent hM i with
    | none => simp [(c.flagIdle he).1,(c.flagIdle he).2]
    | some a => by_cases hf : a.finish = i <;> simp [c.flagEnd he,c.flagMark he,hf]
  zero_idle hi he := by
    have hn : pointEvent hM i = none := by
      classical
      cases ho : pointEvent hM i with
      | none => rfl
      | some a =>
        change (c.endFlag || c.markFlag) = false at he
        by_cases hf : a.finish = i <;> simp [c.flagEnd ho,c.flagMark ho,hf] at he
    simp [c.idle hi hn]
  left_allowed hi hl := by
    obtain ⟨a,ha⟩ : ∃ a, a ∈ c.left := by
      apply not_forall_not.mp
      intro hn
      simp [List.eq_nil_iff_forall_not_mem.mpr hn] at hl
    have hm := ((mem_activeList hM).mp (c.left_old ha)).1
    simpa [level,hi] using ((hM.1 _ hm).1 ⟨i,hi⟩).2 ((c.positive hi).2.1 a ha)
  right_allowed hi hr := by
    obtain ⟨a,ha⟩ : ∃ a, a ∈ c.right := by
      apply not_forall_not.mp
      intro hn
      simp [List.eq_nil_iff_forall_not_mem.mpr hn] at hr
    have hm := ((mem_activeList hM).mp (c.right_old ha)).1
    simpa [level,hi] using ((hM.1 _ hm).1 ⟨i,hi⟩).1 ((c.positive hi).2.2 a ha)

theorem cut_ends : c.cut.ends = c.ends.map SArc.key := by
  classical
  change (if c.endFlag then (pointEvent hM i).toList.map SArc.key else []) = _
  cases he : pointEvent hM i with
  | none => simp [ends,he,(c.flagIdle he).1]
  | some a => by_cases hf : a.finish = i <;> simp [ends,he,c.flagEnd he,hf]

theorem cut_marks : c.cut.marks = c.marks.map SArc.key := by
  classical
  change (if c.markFlag then (pointEvent hM i).toList.map SArc.key else []) = _
  cases he : pointEvent hM i with
  | none => simp [marks,he,(c.flagIdle he).2]
  | some a => by_cases hf : a.finish = i <;> simp [marks,he,c.flagMark he,hf]

noncomputable def move : Move d i ((activeList hM i.castSucc).map SArc.key) :=
  ⟨c.event,c.cut,(keys_startList hM i).choose⟩

theorem move_next : c.move.next = (activeList hM i.succ).map SArc.key := by
  change c.cut.left ++ c.cut.marks ++ startsAt i (keys_startList hM i).choose ++ c.cut.right = _
  rw [c.cut_marks,(keys_startList hM i).choose_spec]
  simpa only [cut,List.map_append] using congrArg (List.map SArc.key) c.next_arcs

theorem cut_right_iff {a : SArc s} (ha : (a,a.finish) ∈ M) :
    a.key ∈ c.cut.passesRight ↔ i ∈ a.right := by
  by_cases hi : s i = 0
  · simp only [Cut.passesRight,hi,ite_true,List.not_mem_nil,false_iff]
    exact fun h => (mem_positiveInterior.mp (a.right_subset h)).2.2 hi
  simp only [Cut.passesRight,hi,ite_false]
  change a.key ∈ c.right.map SArc.key ↔ _
  constructor
  · intro hk
    obtain ⟨b,hb,he⟩ := List.mem_map.mp hk
    have hb' := ((mem_activeList hM).mp (c.right_old hb)).1
    have e := live_key_injective hM hb' ha he
    exact e ▸ (c.positive hi).2.2 b hb
  · intro h
    obtain ⟨hs,hf,_⟩ := mem_positiveInterior.mp (a.right_subset h)
    have hb := (mem_activeList hM (q := i.castSucc)).mpr ⟨ha,hs,hf.le⟩
    rw [c.split] at hb
    obtain (hl | hp) | hr := List.mem_append.mp hb |>.imp_left List.mem_append.mp
    · exact ((mem_left.mp ((c.positive hi).2.1 a hl)).2 h).elim
    · exact (hf.ne (pointEvent_pos hM hi (Option.mem_toList.mp hp)).symm).elim
    · exact List.mem_map.mpr ⟨a,hr,rfl⟩

end ArcSplit

open History

noncomputable def occupiedLevels (M : Finset (EndEvent s)) : Finset (Fin n) := by
  classical
  exact M.image Prod.snd

theorem mem_occupiedLevels {i : Fin n} : i ∈ occupiedLevels M ↔ ∃ a, (a,i) ∈ M := by
  classical
  simp [occupiedLevels]

theorem occupiedLevels_card (hM : IsMarked d M) : (occupiedLevels M).card = M.card := by
  classical
  apply Finset.card_image_iff.mpr
  intro a ha b hb he
  by_contra hn
  exact (hM.2 ha hb hn).1 he

noncomputable def encodeHistory (hM : IsMarked d M) : Complete d M.card where
  active q := (activeList hM q).map SArc.key
  grade q := ((occupiedLevels M) ∩ levelsFrom q).card
  move i := (arcSplit hM i).move
  first := by
    have e : activeList hM 0 = [] := List.eq_nil_iff_forall_not_mem.mpr (fun a ha =>
      Nat.not_lt_zero _ ((mem_activeList hM).mp ha).2.1)
    simp [e]
  last := by
    have e : activeList hM (Fin.last n) = [] := List.eq_nil_iff_forall_not_mem.mpr (fun a ha =>
      (not_le_of_gt a.finish.isLt) ((mem_activeList hM).mp ha).2.2)
    simp [e]
  first_grade := by
    have e : levelsFrom (0 : Fin (n+1)) = Finset.univ := by ext i; simp
    rw [e,Finset.inter_univ,occupiedLevels_card hM]
  last_grade := by
    have e : levelsFrom (Fin.last n) = (∅ : Finset (Fin n)) := by
      ext i
      simp [Nat.not_le_of_gt i.isLt]
    simp [e]
  next i := (arcSplit hM i).move_next
  next_grade i := by
    classical
    change (_ ∩ levelsFrom i.castSucc).card =
      (arcSplit hM i).event.weight + (_ ∩ levelsFrom i.succ).card
    rw [levelsFrom_step,(arcSplit hM i).event_weight]
    cases he : pointEvent hM i with
    | none =>
      have hn : i ∉ occupiedLevels M := fun hi => by
        obtain ⟨a,ha⟩ := mem_occupiedLevels.mp hi
        have h := (pointEvent_spec hM).mpr ha
        rw [he] at h
        contradiction
      have e : occupiedLevels M ∩ insert i (levelsFrom i.succ) =
          occupiedLevels M ∩ levelsFrom i.succ := by
        ext j
        simp only [Finset.mem_inter,Finset.mem_insert]
        aesop
      simp [e]
    | some a =>
      have hp : i ∈ occupiedLevels M := mem_occupiedLevels.mpr ⟨a,(pointEvent_spec hM).mp he⟩
      have e : occupiedLevels M ∩ insert i (levelsFrom i.succ) =
          insert i (occupiedLevels M ∩ levelsFrom i.succ) := by
        ext j
        simp only [Finset.mem_inter,Finset.mem_insert]
        aesop
      have hn : i ∉ occupiedLevels M ∩ levelsFrom i.succ := by simp
      rw [e,Finset.card_insert_of_notMem hn]
      simp [Nat.add_comm]

#print axioms ArcSplit.next_arcs
#print axioms encodeHistory

end Permutree.SweepStep
```

### `SweepInverse.lean`

```lean
import SweepEncode

namespace Permutree.SweepStep

open SArc
open History
open scoped List

variable {n m : ℕ} {s : Fin n → ℕ} {d : Decoration s} {M : Finset (EndEvent s)}

theorem arc_eq {a b : SArc s} (hk : a.key = b.key)
    (hf : a.finish = b.finish) (hr : a.right = b.right) : a = b := by
  cases a
  cases b
  obtain ⟨hi,hl⟩ := Sigma.mk.inj_iff.mp hk
  cases hi
  cases hf
  cases hr
  cases hl
  rfl

theorem decode_encodeHistory (hM : IsMarked d M) : (encodeHistory hM).decoded = M := by
  let H := encodeHistory hM
  have end_iff {i : Fin n} {k : Key s} :
      k ∈ (H.move i).cut.ends ↔ ∃ a, (a,i) ∈ M ∧ a.finish = i ∧ a.key = k := by
    change k ∈ (arcSplit hM i).cut.ends ↔ _
    rw [(arcSplit hM i).cut_ends]
    simp only [List.mem_map,(arcSplit hM i).mem_ends,and_assoc]
  have pivot_iff {i : Fin n} {k : Key s} :
      k ∈ (H.move i).cut.pivot ↔ ∃ a, (a,i) ∈ M ∧ a.key = k := by
    change k ∈ (pointEvent hM i).toList.map key ↔ _
    simp only [List.mem_map,Option.mem_toList,pointEvent_spec hM]
  have recover {a : SArc s} (ha : (a,a.finish) ∈ M)
      (he : a.key ∈ (H.move a.finish).cut.ends) :
      H.arcOf a.key a.finish he = a := by
    refine arc_eq (H.arcOf_key _ _ _) rfl ?_
    ext i
    rw [H.arcOf_right he]
    exact (arcSplit hM i).cut_right_iff ha
  ext e
  obtain ⟨a,i⟩ := e
  change (a,i) ∈ H.decoded ↔ (a,i) ∈ M
  rw [H.mem_decoded]
  constructor
  · rintro ⟨k,hk,j,hj,rfl⟩
    obtain ⟨b,hb,hbj,hbk⟩ := end_iff.mp hj
    obtain ⟨c,hc,hck⟩ := pivot_iff.mp hk
    subst j k
    have hr := (hM.1 _ hc).2.2.2.2
    have e : c = b := live_key_injective hM hr hb hck
    subst c
    rwa [recover hb hj]
  · intro h
    have hb := (hM.1 _ h).2.2.2.2
    have he := end_iff.mpr ⟨a,hb,rfl,rfl⟩
    exact ⟨a.key,pivot_iff.mpr ⟨a,h,rfl⟩,a.finish,he,recover hb he⟩

namespace History

variable (H : Complete d m)

theorem decoded_end {i : Fin n} {k : Key s} :
    k ∈ (H.move i).cut.ends ↔ ∃ a, (a,i) ∈ H.decoded ∧ a.finish = i ∧ a.key = k := by
  constructor
  · intro h
    have hp : k ∈ (H.move i).cut.pivot := by rw [(H.move i).pivot_partition]; simp [h]
    exact ⟨H.arcOf k i h, H.mem_decoded.mpr ⟨k,hp,i,h,rfl⟩,rfl,H.arcOf_key _ _ _⟩
  · rintro ⟨a,ha,hf,hk⟩
    obtain ⟨l,_,j,he,rfl⟩ := H.mem_decoded.mp ha
    change j = i at hf
    have e := (H.arcOf_key l j he).symm.trans hk
    subst j l
    exact he

theorem decoded_mark {i : Fin n} {k : Key s} :
    k ∈ (H.move i).cut.marks ↔ ∃ a, (a,i) ∈ H.decoded ∧ a.finish ≠ i ∧ a.key = k := by
  constructor
  · intro h
    have hp : k ∈ (H.move i).cut.pivot := by rw [(H.move i).pivot_partition]; simp [h]
    obtain ⟨j,_,he⟩ := H.exists_end i.castSucc ((H.move i).mem_marks_old h)
    have hf : j ≠ i := by
      rintro rfl
      rcases (H.move j).marks_ends_disjoint with e | e
      · simp [e] at h
      · simp [e] at he
    exact ⟨H.arcOf k j he,H.mem_decoded.mpr ⟨k,hp,j,he,rfl⟩,hf,H.arcOf_key _ _ _⟩
  · rintro ⟨a,ha,hf,hk⟩
    obtain ⟨l,hl,j,he,rfl⟩ := H.mem_decoded.mp ha
    change j ≠ i at hf
    have e := (H.arcOf_key l j he).symm.trans hk
    subst l
    rw [(H.move i).pivot_partition,List.mem_append] at hl
    exact hl.resolve_left (fun h => hf (H.end_unique he h))

theorem decoded_right {i : Fin n} {k : Key s} :
    k ∈ (H.move i).cut.passesRight ↔
      ∃ a, (a,a.finish) ∈ H.decoded ∧ a.key = k ∧ i ∈ a.right := by
  constructor
  · intro h
    obtain ⟨j,_,he⟩ := H.exists_end i.castSucc ((H.move i).mem_passesRight_old h)
    have hp : k ∈ (H.move j).cut.pivot := by rw [(H.move j).pivot_partition]; simp [he]
    exact ⟨H.arcOf k j he,H.mem_decoded.mpr ⟨k,hp,j,he,rfl⟩,H.arcOf_key _ _ _,(H.arcOf_right he).mpr h⟩
  · rintro ⟨a,ha,hk,hr⟩
    obtain ⟨l,_,j,he,rfl⟩ := H.mem_decoded.mp ha
    have e := (H.arcOf_key l j he).symm.trans hk
    subst l
    exact (H.arcOf_right he).mp hr

theorem decoded_start {i : Fin n} {r : Fin (s i)} :
    r ∈ (H.move i).starts ↔
      ∃ a, (a,a.finish) ∈ H.decoded ∧ a.key = (⟨i,r⟩ : Key s) := by
  constructor
  · intro h
    have hm := (H.mem_active_succ i).mpr (Or.inr (mem_startsAt.mpr ⟨r,h,rfl⟩))
    obtain ⟨j,_,he⟩ := H.exists_end i.succ hm
    have hp : (⟨i,r⟩ : Key s) ∈ (H.move j).cut.pivot := by
      rw [(H.move j).pivot_partition]
      simp [he]
    exact ⟨H.arcOf _ j he,H.mem_decoded.mpr ⟨_,hp,j,he,rfl⟩,H.arcOf_key _ _ _⟩
  · rintro ⟨a,ha,hk⟩
    have he := H.decoded_end.mpr ⟨a,ha,rfl,hk⟩
    obtain ⟨t,ht,heq⟩ := mem_startsAt.mp ((H.starts_iff he i).mpr rfl)
    cases eq_of_heq (Sigma.mk.inj_iff.mp heq).2
    exact ht

end History

namespace Move

variable {i : Fin n} {old : List (Key s)} (u v : Move d i old)

private theorem list_eq_of_short {A : Type*} {xs ys : List A}
    (hx : xs.length ≤ 1) (hy : ys.length ≤ 1) (h : ∀ a, a ∈ xs ↔ a ∈ ys) : xs = ys := by
  cases xs with
  | nil => exact (List.eq_nil_iff_forall_not_mem.mpr fun a ha => by simpa using (h a).mpr ha).symm
  | cons a as =>
    cases ys with
    | nil => have := (h a).mp (by simp); simp at this
    | cons b bs =>
      have ea : as = [] := (by simpa using hx)
      have eb : bs = [] := (by simpa using hy)
      simpa [ea,eb] using h

private theorem ends_short : u.cut.ends.length ≤ 1 := by
  cases h : u.event.val.1 <;> simp [Cut.ends,h,u.length_pivot_le_one]

private theorem marks_short : u.cut.marks.length ≤ 1 := by
  cases h : u.event.val.2 <;> simp [Cut.marks,h,u.length_pivot_le_one]

private theorem length_ends : u.cut.ends.length = u.event.val.1.toNat := by
  have hp := u.cut.pivot_length
  cases h : u.event.val.1 <;> simp [Cut.ends,Event.hasPivot,h] at hp ⊢
  exact hp

private theorem length_marks : u.cut.marks.length = u.event.val.2.toNat := by
  have hp := u.cut.pivot_length
  have hc : u.event.val.2 = true → u.event.val.1 = false := fun h => (u.event.property.2 h).2.2
  cases h : u.event.val.2 <;> simp [Cut.marks,Event.hasPivot,h] at hp hc ⊢
  exact hp

private theorem cut_eq_of_records {e : Permutree.Event (level d i) old.length}
    (hn : old.Nodup) (c c' : Cut d i old e) (hp : c.pivot = c'.pivot)
    (hr : ∀ k, k ∈ c.passesRight ↔ k ∈ c'.passesRight) : c = c' := by
  apply Cut.eq_of_rank
  by_cases hi : s i = 0
  · by_cases h : Event.hasPivot e = false
    · rw [c.zero_idle hi h,c'.zero_idle hi h]
    · have hlen : 0 < c.pivot.length := by
        rw [c.pivot_length]
        have ht : Event.hasPivot e = true := Bool.eq_true_of_not_eq_false h
        simp [ht]
      have atPivot (v : Cut d i old e) (hv : 0 < v.pivot.length) :
          old[v.left.length]? = v.pivot[0]? := by
        calc
          _ = (v.left ++ (v.pivot ++ v.right))[v.left.length]? :=
            congrArg (fun l : List (Key s) => l[v.left.length]?) (by simpa [List.append_assoc] using v.split)
          _ = _ := by
            rw [List.getElem?_append_right le_rfl,Nat.sub_self,List.getElem?_append_left hv]
      have hl : c.left.length < old.length := by
        have h := c.total_length
        rw [← c.pivot_length] at h
        omega
      exact (hn.getElem?_inj hl).mp ((atPivot c hlen).trans ((congrArg (fun l : List (Key s) =>
        l[0]?) hp).trans (atPivot c' (hp ▸ hlen)).symm))
  · classical
    simp only [Cut.passesRight,hi,ite_false] at hr
    have right_nodup (u : Cut d i old e) : u.right.Nodup := by
      have hsub : u.right <+ old := by
        calc
          _ <+ u.left ++ u.pivot ++ u.right := List.sublist_append_right _ _
          _ = old := u.split.symm
      exact hn.sublist hsub
    have hn₁ := right_nodup c
    have hn₂ := right_nodup c' 
    have hs : c.right.toFinset = c'.right.toFinset := by ext k; simpa using hr k
    have hl := congrArg Finset.card hs
    rw [List.toFinset_card_of_nodup hn₁,List.toFinset_card_of_nodup hn₂] at hl
    have h₁ := c.total_length
    have h₂ := c'.total_length
    omega

theorem eq_of_data (hn : old.Nodup)
    (he : ∀ k, k ∈ u.cut.ends ↔ k ∈ v.cut.ends)
    (hm : ∀ k, k ∈ u.cut.marks ↔ k ∈ v.cut.marks)
    (hr : ∀ k, k ∈ u.cut.passesRight ↔ k ∈ v.cut.passesRight)
    (hs : u.starts = v.starts) : u = v := by
  have he' := list_eq_of_short u.ends_short v.ends_short he
  have hm' := list_eq_of_short u.marks_short v.marks_short hm
  have ef : u.event = v.event := by
    apply Subtype.ext
    apply Prod.ext
    · have h := u.length_ends.symm.trans ((congrArg List.length he').trans v.length_ends)
      cases h₁ : u.event.val.1 <;> cases h₂ : v.event.val.1 <;> simp_all
    · have h := u.length_marks.symm.trans ((congrArg List.length hm').trans v.length_marks)
      cases h₁ : u.event.val.2 <;> cases h₂ : v.event.val.2 <;> simp_all
  obtain ⟨e,c,S⟩ := u
  obtain ⟨e',c',S'⟩ := v
  change e = e' at ef
  subst e'
  have h₁ := (Move.pivot_partition ⟨e,c,S⟩)
  have h₂ := (Move.pivot_partition ⟨e,c',S'⟩)
  have hp : c.pivot = c'.pivot := by
    change c.ends = c'.ends at he'
    change c.marks = c'.marks at hm'
    exact h₁.trans ((congrArg₂ List.append he' hm').trans h₂.symm)
  have hc := cut_eq_of_records hn c c' hp hr
  change S = S' at hs
  subst c' S'
  rfl

end Move

namespace Move

variable {i : Fin n} {old old' : List (Key s)} {u : Move d i old} {v : Move d i old'}

theorem heq_of_data (h : old = old') (hn : old.Nodup)
    (he : ∀ k, k ∈ u.cut.ends ↔ k ∈ v.cut.ends)
    (hm : ∀ k, k ∈ u.cut.marks ↔ k ∈ v.cut.marks)
    (hr : ∀ k, k ∈ u.cut.passesRight ↔ k ∈ v.cut.passesRight)
    (hs : u.starts = v.starts) : HEq u v := by
  subst old'
  exact heq_of_eq (u.eq_of_data v hn he hm hr hs)

theorem heq_next (ho : old = old') (h : HEq u v) : u.next = v.next := by
  subst old'
  cases h
  rfl

theorem heq_weight (ho : old = old') (h : HEq u v) : u.weight = v.weight := by
  subst old'
  cases h
  rfl

end Move

theorem decode_injective : Function.Injective (History.decode (d := d) (m := m)) := by
  intro H J e
  have eM : H.decoded = J.decoded := congrArg Subtype.val e
  have moves (i : Fin n) (h : H.active i.castSucc = J.active i.castSucc) :
      HEq (H.move i) (J.move i) := by
    apply Move.heq_of_data h (H.active_invariant i.castSucc).1
    · intro k
      simp only [H.decoded_end,J.decoded_end,eM]
    · intro k
      simp only [H.decoded_mark,J.decoded_mark,eM]
    · intro k
      simp only [H.decoded_right,J.decoded_right,eM]
    · ext r
      simp only [H.decoded_start,J.decoded_start,eM]
  have ea (q : Fin (n+1)) : H.active q = J.active q := by
    induction q using Fin.induction with
    | zero => exact H.first.trans J.first.symm
    | succ i ih =>
      exact (H.next i).symm.trans ((Move.heq_next ih (moves i ih)).trans (J.next i))
  have eg (q : Fin (n+1)) : H.grade q = J.grade q := by
    induction q using Fin.reverseInduction with
    | last => exact H.last_grade.trans J.last_grade.symm
    | cast i ih =>
      rw [H.next_grade i,J.next_grade i,Move.heq_weight (ea i.castSucc) (moves i (ea i.castSucc)),ih]
  refine History.ext (funext ea) (funext eg) (Function.hfunext rfl ?_)
  intro i j he
  have e : i = j := eq_of_heq he
  subst j
  exact moves i (ea i.castSucc)

theorem decode_surjective : Function.Surjective (History.decode (d := d) (m := m)) := by
  rintro ⟨M,hM,hm⟩
  subst m
  exact ⟨encodeHistory hM, Subtype.ext (decode_encodeHistory hM)⟩

/-- Both directions are inverse on the marked diagrams and on the entire
length-indexed sweep code. -/
noncomputable def encode_marked_sweep_inverse (d : Decoration s) (m : ℕ) :
    MarkedOfSize d m ≃ Sweep (levels d) 0 m :=
  (Equiv.ofBijective History.decode ⟨decode_injective,decode_surjective⟩).symm.trans
    (historyEquiv d id [] m)

#print axioms decode_encodeHistory
#print axioms Move.eq_of_data
#print axioms encode_marked_sweep_inverse

end Permutree.SweepStep
```

### `SPosition.lean`

```lean
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold

namespace Permutree

variable {n : ℕ} {s : Fin n → ℕ}

/-- Position arrays satisfying Proposition 30, with unused coordinates set to zero. -/
structure SPosition (s : Fin n → ℕ) where
  pos : Fin n → Fin n → ℕ
  bound : ∀ i j, pos i j ≤ s i
  zero_of_not_lt : ∀ i j, ¬ i < j → pos i j = 0
  transitive : ∀ {i j k}, i < j → j < k → 0 < pos j k → pos i j ≤ pos i k
  planar : ∀ {i j k}, i < j → j < k → pos j k < s j → pos i k ≤ pos i j

namespace SPosition

@[ext] theorem ext {x y : SPosition s} (h : x.pos = y.pos) : x = y := by
  cases x
  cases y
  cases h
  rfl

instance : PartialOrder (SPosition s) := PartialOrder.lift pos (fun _ _ => ext)

theorem le_iff {x y : SPosition s} : x ≤ y ↔ ∀ i j, x.pos i j ≤ y.pos i j := Iff.rfl

instance : Finite (SPosition s) :=
  Finite.of_injective (fun x (i j : Fin n) => (⟨x.pos i j, Nat.lt_succ_of_le (x.bound i j)⟩ :
    Fin (s i + 1))) (fun _ _ h => ext (funext fun i => funext fun j =>
      congrArg Fin.val (congrFun (congrFun h i) j)))

protected def zero : SPosition s where
  pos _ _ := 0
  bound _ _ := Nat.zero_le _
  zero_of_not_lt _ _ _ := rfl
  transitive _ _ _ := le_rfl
  planar _ _ _ := le_rfl

instance : OrderBot (SPosition s) where
  bot := SPosition.zero
  bot_le _ := fun _ _ => Nat.zero_le _

/-- The first step carries the threshold; later steps must be positive. -/
inductive Walk (p : Fin n → Fin n → ℕ) : Fin n → ℕ → Fin n → Prop
  | single {i j r} : i < j → r ≤ p i j → Walk p i r j
  | cons {i j k r} : i < j → r ≤ p i j → Walk p j 1 k → Walk p i r k

namespace Walk

variable {p : Fin n → Fin n → ℕ} {i j k : Fin n} {r : ℕ}

theorem increasing (w : Walk p i r k) : i < k := by
  induction w with
  | single h _ => exact h
  | cons h _ _ ih => exact h.trans ih

theorem lower (w : Walk p i r k) {t : ℕ} (h : t ≤ r) : Walk p i t k := by
  cases w with
  | single hij hr => exact .single hij (h.trans hr)
  | cons hij hr tail => exact .cons hij (h.trans hr) tail

theorem append (w : Walk p i r j) (v : Walk p j 1 k) : Walk p i r k := by
  induction w with
  | single hij hr => exact .cons hij hr v
  | cons hij hr _ ih => exact .cons hij hr (ih v)

theorem bounded (w : Walk p i r k) (hp : ∀ a b, p a b ≤ s a) : r ≤ s i := by
  cases w with
  | single _ h | cons _ h _ => exact h.trans (hp _ _)

theorem le_of_le_pos (w : Walk p i r k) {z : SPosition s}
    (hz : ∀ a b, p a b ≤ z.pos a b) : r ≤ z.pos i k := by
  induction w with
  | single _ h => exact h.trans (hz _ _)
  | cons hij hr tail ih =>
    exact (hr.trans (hz _ _)).trans (z.transitive hij tail.increasing ih)

/-- If a path passes a level, either the same threshold can reach that
level or the full threshold at that level can reach the target (or it is unary). -/
theorem split_planar
    (hp : ∀ {i j k : Fin n} {r}, i < j → j < k → r ≤ p i k →
      r ≤ p i j ∨ s j ≤ p j k)
    (w : Walk p i r k) (hij : i < j) (hjk : j < k) :
    Walk p i r j ∨ s j = 0 ∨ Walk p j (s j) k := by
  induction w with
  | @single i k r _ hr =>
    rcases hp hij hjk hr with h | h
    · exact Or.inl (.single hij h)
    · exact Or.inr (Or.inr (.single hjk h))
  | @cons i a k r hia hr tail ih =>
    rcases lt_trichotomy j a with hja | hja | haj
    · rcases hp hij hja hr with h | h
      · exact Or.inl (.single hij h)
      · exact Or.inr (Or.inr (.cons hja h tail))
    · subst j
      exact Or.inl (.single hia hr)
    · rcases ih haj hjk with h | hz | h
      · exact Or.inl (.cons hia hr h)
      · exact Or.inr (Or.inl hz)
      · exact Or.inr (Or.inr h)

end Walk

noncomputable def closure (s : Fin n → ℕ) (p : Fin n → Fin n → ℕ) (i j : Fin n) : ℕ := by
  classical
  exact ((Finset.range (s i + 1)).filter (fun r => Walk p i r j)).sup id

theorem walk_le_closure {p : Fin n → Fin n → ℕ} {i j : Fin n} {r : ℕ}
    (hr : r ≤ s i) (w : Walk p i r j) : r ≤ closure s p i j := by
  classical
  exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_range_succ_iff.mpr hr, w⟩)

theorem walk_of_le_closure {p : Fin n → Fin n → ℕ} {i j : Fin n} {r : ℕ}
    (hr : 0 < r) (h : r ≤ closure s p i j) : Walk p i r j := by
  classical
  obtain ⟨t, ht, hrt⟩ := (Finset.le_sup_iff (show (⊥ : ℕ) < r from hr)).mp h
  exact (Finset.mem_filter.mp ht).2.lower hrt

theorem closure_bound (p : Fin n → Fin n → ℕ) (i j : Fin n) : closure s p i j ≤ s i := by
  classical
  exact Finset.sup_le fun _ h => Finset.mem_range_succ_iff.mp (Finset.mem_filter.mp h).1

noncomputable def join (x y : SPosition s) : SPosition s where
  pos := closure s (fun i j => max (x.pos i j) (y.pos i j))
  bound := closure_bound _
  zero_of_not_lt := by
    intro i j h
    by_contra he
    have hc := Nat.pos_of_ne_zero he
    exact h (walk_of_le_closure hc le_rfl).increasing
  transitive := by
    intro i j k _ _ h
    change 0 < closure s _ j k at h
    by_cases hr : closure s (fun i j => max (x.pos i j) (y.pos i j)) i j = 0
    · rw [hr]
      exact Nat.zero_le _
    · exact walk_le_closure (closure_bound _ _ _)
        ((walk_of_le_closure (Nat.pos_of_ne_zero hr) le_rfl).append (walk_of_le_closure (by decide) h))
  planar := by
    intro i j k hij hjk h
    change closure s _ j k < s j at h
    by_cases hr : closure s (fun i j => max (x.pos i j) (y.pos i j)) i k = 0
    · rw [hr]
      exact Nat.zero_le _
    have hp {a b c : Fin n} {r : ℕ} (hab : a < b) (hbc : b < c)
        (hle : r ≤ max (x.pos a c) (y.pos a c)) :
        r ≤ max (x.pos a b) (y.pos a b) ∨ s b ≤ max (x.pos b c) (y.pos b c) := by
      rcases le_max_iff.mp hle with hle | hle
      · by_cases hlt : x.pos b c < s b
        · exact Or.inl (hle.trans ((x.planar hab hbc hlt).trans (le_max_left _ _)))
        · exact Or.inr ((le_of_not_gt hlt).trans (le_max_left _ _))
      · by_cases hlt : y.pos b c < s b
        · exact Or.inl (hle.trans ((y.planar hab hbc hlt).trans (le_max_right _ _)))
        · exact Or.inr ((le_of_not_gt hlt).trans (le_max_right _ _))
    rcases (walk_of_le_closure (Nat.pos_of_ne_zero hr) le_rfl).split_planar hp hij hjk with hw | hz | hw
    · exact walk_le_closure (closure_bound _ _ _) hw
    · omega
    · exact (not_le_of_gt h (walk_le_closure le_rfl hw)).elim

theorem le_join_left (x y : SPosition s) : x ≤ join x y := by
  intro i j
  by_cases h : i < j
  · exact walk_le_closure (x.bound i j) (.single h (le_max_left _ _))
  · rw [x.zero_of_not_lt _ _ h]
    exact Nat.zero_le _

theorem le_join_right (x y : SPosition s) : y ≤ join x y := by
  intro i j
  by_cases h : i < j
  · exact walk_le_closure (y.bound i j) (.single h (le_max_right _ _))
  · rw [y.zero_of_not_lt _ _ h]
    exact Nat.zero_le _

theorem join_le {x y z : SPosition s} (hx : x ≤ z) (hy : y ≤ z) : join x y ≤ z := by
  classical
  intro i j
  change closure s _ i j ≤ z.pos i j
  exact Finset.sup_le fun _ hr => (Finset.mem_filter.mp hr).2.le_of_le_pos
    (fun a b => max_le (hx a b) (hy a b))

def mirror (x : SPosition s) : SPosition s where
  pos i j := if i < j then s i - x.pos i j else 0
  bound i j := by split <;> omega
  zero_of_not_lt i j h := ite_eq_right h
  transitive := by
    intro i j k hij hjk h
    simp only [ite_eq_left hij, ite_eq_left hjk, ite_eq_left (hij.trans hjk)] at *
    exact Nat.sub_le_sub_left (x.planar hij hjk (by omega)) _
  planar := by
    intro i j k hij hjk h
    simp only [ite_eq_left hij, ite_eq_left hjk, ite_eq_left (hij.trans hjk)] at *
    exact Nat.sub_le_sub_left (x.transitive hij hjk (by omega)) _

theorem mirror_antitone : Antitone (mirror (s := s)) := by
  intro x y h i j
  change (if i < j then s i - y.pos i j else 0) ≤ (if i < j then s i - x.pos i j else 0)
  split
  · exact Nat.sub_le_sub_left (h i j) _
  · exact Nat.zero_le _

@[simp] theorem mirror_mirror (x : SPosition s) : x.mirror.mirror = x := by
  ext : 1
  funext i j
  by_cases h : i < j
  · have := x.bound i j
    simp only [mirror, ite_eq_left h]
    omega
  · simp [mirror, h, x.zero_of_not_lt _ _ h]

noncomputable instance : Lattice (SPosition s) where
  sup := join
  le_sup_left := le_join_left
  le_sup_right := le_join_right
  sup_le _ _ _ := join_le
  inf x y := (join x.mirror y.mirror).mirror
  inf_le_left x y := by simpa using mirror_antitone (le_join_left x.mirror y.mirror)
  inf_le_right x y := by simpa using mirror_antitone (le_join_right x.mirror y.mirror)
  le_inf x y z hxy hxz := by
    simpa using mirror_antitone (join_le (mirror_antitone hxy) (mirror_antitone hxz))

#print axioms join
#print axioms instLattice

end SPosition

end Permutree
```

### `STree.lean`

```lean
import SPosition

namespace Permutree

variable {n : ℕ} {s : Fin n → ℕ}

/-- Number of leaves after the first m insertions. -/
def leafCount (s : Fin n → ℕ) : ℕ → ℕ
  | 0 => 1
  | m+1 => leafCount s m + (if h : m < n then s ⟨m,h⟩ else 0)

theorem leafCount_succ (s : Fin n → ℕ) {m : ℕ} (h : m < n) :
    leafCount s (m+1) = leafCount s m + s ⟨m,h⟩ := by simp [leafCount,h]

/-- Increasing plane trees encoded by the successive leaves at which their
nodes are inserted, as in Remark 2(6). Leaves are indexed from the left. -/
inductive TreePrefix (s : Fin n → ℕ) : ℕ → Type
  | empty : TreePrefix s 0
  | insert {m : ℕ} : TreePrefix s m → (hm : m < n) →
      Fin (leafCount s m) → TreePrefix s (m+1)

abbrev STree (s : Fin n → ℕ) := TreePrefix s n

namespace TreePrefix

variable {m : ℕ}

/-- The old leaf from which an updated leaf descends. -/
def oldLeaf (hm : m < n) (q : Fin (leafCount s m))
    (v : Fin (leafCount s (m+1))) : Fin (leafCount s m) :=
  if h : v.val < q.val then ⟨v.val,h.trans q.isLt⟩
  else if h' : q.val + s ⟨m,hm⟩ < v.val then
    ⟨v.val - s ⟨m,hm⟩, by have hv := v.isLt; have hc := leafCount_succ s hm; omega⟩
  else q

/-- Number of separators belonging to a node to the right of a leaf.
An insertion replaces its leaf by s_j+1 consecutive child leaves. -/
def profile : {m : ℕ} → TreePrefix s m → Fin (leafCount s m) → Fin n → ℕ
  | _, .empty, _, _ => 0
  | _, @TreePrefix.insert _ _ m T hm q, v, i =>
    if i.val = m then
      if v.val < q.val then s i else q.val + s i - v.val
    else profile T (oldLeaf hm q v) i

/-- Definition 28. At insertion of j, the leaf's profile at i counts the
outgoing edges strictly to the right of the path, truncated at s_i. -/
def pos : {m : ℕ} → TreePrefix s m → Fin n → Fin n → ℕ
  | _, .empty, _, _ => 0
  | _, @TreePrefix.insert _ _ m T _ q, i, j =>
    if j.val = m then profile T q i else pos T i j

theorem oldLeaf_val (hm : m < n) (q : Fin (leafCount s m))
    (v : Fin (leafCount s (m+1))) :
    (oldLeaf hm q v).val =
      if v.val < q.val then v.val else if q.val + s ⟨m,hm⟩ < v.val
      then v.val - s ⟨m,hm⟩ else q.val := by
  by_cases h : v.val < q.val
  · simp [oldLeaf,h]
  · by_cases h' : q.val + s ⟨m,hm⟩ < v.val <;> simp [oldLeaf,h,h']

theorem oldLeaf_mono (hm : m < n) (q : Fin (leafCount s m)) :
    Monotone (oldLeaf hm q) := by
  intro u v h
  have he : u.val ≤ v.val := h
  change (oldLeaf hm q u).val ≤ (oldLeaf hm q v).val
  rw [oldLeaf_val, oldLeaf_val]
  repeat' split
  all_goals omega

private theorem recover_leaf (T : TreePrefix s m) (hm : m < n)
    (q : Fin (leafCount s m)) (v : Fin (leafCount s (m+1))) :
    v.val = if (oldLeaf hm q v).val < q.val then (oldLeaf hm q v).val
      else if q.val < (oldLeaf hm q v).val then (oldLeaf hm q v).val + s ⟨m,hm⟩
      else q.val + s ⟨m,hm⟩ - (T.insert hm q).profile v ⟨m,hm⟩ := by
  rw [oldLeaf_val]
  have hp : (T.insert hm q).profile v ⟨m,hm⟩ =
      (if v.val < q.val then s ⟨m,hm⟩ else q.val + s ⟨m,hm⟩ - v.val) := by
    simp [profile]
  rw [hp]
  repeat' split
  all_goals omega

theorem profile_antitone (T : TreePrefix s m) (i : Fin n) :
    Antitone (fun v => T.profile v i) := by
  induction T with
  | empty => exact fun _ _ _ => le_rfl
  | @insert m T hm q ih =>
    intro u v h
    have he : u.val ≤ v.val := h
    simp only [profile]
    split
    · split <;> split <;> omega
    · exact ih (oldLeaf_mono hm q h)

theorem profile_bound (T : TreePrefix s m) (v : Fin (leafCount s m)) (i : Fin n) :
    T.profile v i ≤ s i := by
  induction T with
  | empty => exact Nat.zero_le _
  | insert T hm q ih =>
    simp only [profile]
    split
    · split <;> omega
    · exact ih _

theorem profile_zero (T : TreePrefix s m) (v : Fin (leafCount s m)) (i : Fin n)
    (hi : m ≤ i.val) : T.profile v i = 0 := by
  induction T with
  | empty => rfl
  | insert T _ _ ih =>
    simp only [profile]
    split
    · omega
    · exact ih _ (by omega)

theorem profile_injective (T : TreePrefix s m) : Function.Injective T.profile := by
  induction T with
  | empty =>
    intro u v _
    have hu : u.val < 1 := u.isLt
    have hv : v.val < 1 := v.isLt
    exact Fin.ext (by omega)
  | @insert m T hm q ih =>
    intro u v e
    have ep := congrFun e ⟨m,hm⟩
    have eo : T.profile (oldLeaf hm q u) = T.profile (oldLeaf hm q v) := by
      funext i
      by_cases hi : i.val = m
      · rw [profile_zero T _ _ (by omega), profile_zero T _ _ (by omega)]
      · simpa only [profile, ite_eq_right hi] using congrFun e i
    have ho := congrArg Fin.val (ih eo)
    exact Fin.ext (by rw [recover_leaf T hm q u, recover_leaf T hm q v, ho, ep])

theorem pos_bound (T : TreePrefix s m) (i j : Fin n) : T.pos i j ≤ s i := by
  induction T with
  | empty => exact Nat.zero_le _
  | insert T _ q ih =>
    unfold pos
    split
    · exact profile_bound T q i
    · exact ih

theorem pos_zero_future (T : TreePrefix s m) (i j : Fin n) (hj : m ≤ j.val) :
    T.pos i j = 0 := by
  induction T with
  | empty => rfl
  | @insert m T hm q ih =>
    simp only [pos, ite_eq_right (show j.val ≠ m by omega)]
    exact ih (by omega)

theorem pos_zero_of_not_lt (T : TreePrefix s m) (i j : Fin n) (h : ¬ i < j) :
    T.pos i j = 0 := by
  induction T with
  | empty => rfl
  | insert T hm q ih =>
    simp only [pos]
    split
    · exact profile_zero T q i (by omega)
    · exact ih

/-- A leaf profile satisfies the two position implications with all preceding nodes. -/
theorem profile_planar (T : TreePrefix s m) (v : Fin (leafCount s m))
    {i j : Fin n} (hij : i < j) (hj : j.val < m) :
    (0 < T.profile v j → T.pos i j ≤ T.profile v i) ∧
    (T.profile v j < s j → T.profile v i ≤ T.pos i j) := by
  induction T with
  | empty => omega
  | @insert m T hm q ih =>
    by_cases hjm : j.val = m
    · have hin : i.val ≠ m := by omega
      have hjs : j = ⟨m,hm⟩ := Fin.ext hjm
      simp only [pos, profile, ite_eq_left hjm, ite_eq_right hin]
      have hq₁ : v.val < q.val → oldLeaf hm q v ≤ q := by
        intro h
        simp [oldLeaf,h,Fin.le_def,h.le]
      have hq₂ : q.val + s ⟨m,hm⟩ < v.val → q ≤ oldLeaf hm q v := by
        intro h
        have hn : ¬ v.val < q.val := by omega
        simp only [oldLeaf,dite_eq_right hn,dite_eq_left h,Fin.le_def]
        omega
      have hmid (h₁ : ¬ v.val < q.val) (h₂ : ¬ q.val + s ⟨m,hm⟩ < v.val) :
          oldLeaf hm q v = q := by simp [oldLeaf,h₁,h₂]
      by_cases h₁ : v.val < q.val
      · refine ⟨fun _ => profile_antitone T i (hq₁ h₁), ?_⟩
        simp [h₁]
      · by_cases h₂ : q.val + s ⟨m,hm⟩ < v.val
        · refine ⟨?_, fun _ => profile_antitone T i (hq₂ h₂)⟩
          rw [hjs] at *
          simp [h₁, Nat.sub_eq_zero_of_le h₂.le]
        · simp [hmid h₁ h₂]
    · have hin : i.val ≠ m := by omega
      simpa only [pos,profile,ite_eq_right hjm,ite_eq_right hin] using
        ih (oldLeaf hm q v) (by omega)

theorem pos_planar (T : TreePrefix s m) {i j k : Fin n}
    (hij : i < j) (hjk : j < k) (hk : k.val < m) :
    (0 < T.pos j k → T.pos i j ≤ T.pos i k) ∧
    (T.pos j k < s j → T.pos i k ≤ T.pos i j) := by
  induction T with
  | empty => omega
  | @insert m T hm q ih =>
    by_cases hkm : k.val = m
    · have hjn : j.val ≠ m := by omega
      simpa only [pos,ite_eq_left hkm,ite_eq_right hjn] using
        profile_planar T q hij (by omega)
    · have hjn : j.val ≠ m := by omega
      simpa only [pos,ite_eq_right hkm,ite_eq_right hjn] using ih (by omega)

end TreePrefix

namespace STree

def toPosition (T : STree s) : SPosition s where
  pos := T.pos
  bound := T.pos_bound
  zero_of_not_lt := T.pos_zero_of_not_lt
  transitive _ hjk := (T.pos_planar ‹_› hjk (Fin.isLt _)).1
  planar _ hjk := (T.pos_planar ‹_› hjk (Fin.isLt _)).2

/-- Definition 31. -/
def WeakLE (T U : STree s) : Prop := ∀ i j, T.pos i j ≤ U.pos i j

#print axioms toPosition

end STree

end Permutree
```

### `STreeLattice.lean`

```lean
import STree

namespace Permutree

variable {n : ℕ} {s : Fin n → ℕ}

namespace TreePrefix

variable {m : ℕ}

theorem pos_injective : Function.Injective (pos (s := s) (m := m)) := by
  intro T
  induction T with
  | empty =>
    intro U _
    cases U
    rfl
  | @insert m T hm q ih =>
    intro U h
    cases U with
    | insert U hm' q' =>
      have hTU : T.pos = U.pos := by
        funext i j
        by_cases hj : j.val = m
        · rw [pos_zero_future T i j hj.ge, pos_zero_future U i j hj.ge]
        · simpa only [pos,ite_eq_right hj] using congrFun (congrFun h i) j
      have he := ih hTU
      subst U
      have eq : T.profile q = T.profile q' := by
        funext i
        have hi := congrFun (congrFun h i) (⟨m,hm⟩ : Fin n)
        simpa [pos] using hi
      cases profile_injective T eq
      rfl

private theorem new_slot (T : TreePrefix s m) (hm : m < n)
    (q w : Fin (leafCount s m)) (r : ℕ) (hr : r ≤ s ⟨m,hm⟩)
    (hleft : w < q → r = s ⟨m,hm⟩) (hright : q < w → r = 0) :
    ∃ v : Fin (leafCount s (m+1)), oldLeaf hm q v = w ∧
      (T.insert hm q).profile v ⟨m,hm⟩ = r := by
  have H := leafCount_succ s hm
  have hw := w.isLt
  have hq := q.isLt
  rcases lt_trichotomy w q with h | rfl | h
  · have hwq : w.val < q.val := h
    let v : Fin (leafCount s (m+1)) := ⟨w.val, by omega⟩
    exact ⟨v, Fin.ext (by simp [oldLeaf_val,v,hwq]), by simp [profile,v,hwq,hleft h]⟩
  · let v : Fin (leafCount s (m+1)) := ⟨w.val + s ⟨m,hm⟩ - r, by omega⟩
    have h₁ : ¬ v.val < w.val := by dsimp [v]; omega
    have h₂ : ¬ w.val + s ⟨m,hm⟩ < v.val := by dsimp [v]; omega
    refine ⟨v, Fin.ext (by simp [oldLeaf_val,h₁,h₂]), ?_⟩
    simp only [profile, ite_true, ite_eq_right h₁]
    dsimp [v]
    omega
  · have hqw : q.val < w.val := h
    let v : Fin (leafCount s (m+1)) := ⟨w.val + s ⟨m,hm⟩, by omega⟩
    have h₁ : ¬ v.val < q.val := by dsimp [v]; omega
    have h₂ : q.val + s ⟨m,hm⟩ < v.val := by dsimp [v]; omega
    refine ⟨v, Fin.ext (by simp [oldLeaf_val,h₁,h₂,v]), ?_⟩
    simp [profile,h₁,Nat.sub_eq_zero_of_le h₂.le,hright h]

/-- The leaf profiles are exactly the bounded vectors satisfying the
inequalities with all preceding positions. -/
theorem exists_leaf_profile (T : TreePrefix s m) (u : Fin n → ℕ)
    (hb : ∀ i, u i ≤ s i) (hz : ∀ i, m ≤ i.val → u i = 0)
    (hc : ∀ i j : Fin n, i < j → j.val < m →
      (0 < u j → T.pos i j ≤ u i) ∧ (u j < s j → u i ≤ T.pos i j)) :
    ∃ q, T.profile q = u := by
  induction T generalizing u with
  | empty =>
    exact ⟨⟨0, Nat.zero_lt_succ 0⟩,funext fun i => (hz i (Nat.zero_le _)).symm⟩
  | @insert m T hm q ih =>
    let u' : Fin n → ℕ := fun i => if i.val < m then u i else 0
    have hbu' (i : Fin n) : u' i ≤ s i := by
      dsimp [u']
      split
      · exact hb i
      · exact Nat.zero_le _
    have hzu' (i : Fin n) (hi : m ≤ i.val) : u' i = 0 := by simp [u',not_lt_of_ge hi]
    have hcu' (i j : Fin n) (hij : i < j) (hj : j.val < m) :
        (0 < u' j → T.pos i j ≤ u' i) ∧ (u' j < s j → u' i ≤ T.pos i j) := by
      have hi : i.val < m := by omega
      have hjn : j.val ≠ m := by omega
      simpa only [u',ite_eq_left hi,ite_eq_left hj,pos,ite_eq_right hjn] using
        hc i j hij (by omega)
    obtain ⟨w,hw⟩ := ih u' hbu' hzu' hcu'
    let j : Fin n := ⟨m,hm⟩
    have hq (i : Fin n) (hi : i.val < m) :
        (0 < u j → T.profile q i ≤ T.profile w i) ∧
        (u j < s j → T.profile w i ≤ T.profile q i) := by
      have e : T.profile w i = u i := by simp [hw,u',hi]
      rw [e]
      have hij : i < j := hi
      simpa [pos,j] using hc i j hij (by change m < m+1; omega)
    have hleft (hwq : w < q) : u j = s j := by
      apply (hb j).antisymm
      by_contra h
      have ep : T.profile w = T.profile q := by
        funext i
        by_cases hlt : i.val < m
        · exact ((hq i hlt).2 (lt_of_not_ge h)).antisymm (profile_antitone T i hwq.le)
        · rw [profile_zero T _ _ (Nat.le_of_not_gt hlt), profile_zero T _ _ (Nat.le_of_not_gt hlt)]
      exact hwq.ne (profile_injective T ep)
    have hright (hqw : q < w) : u j = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro h
      have ep : T.profile w = T.profile q := by
        funext i
        by_cases hlt : i.val < m
        · exact (profile_antitone T i hqw.le).antisymm ((hq i hlt).1 h)
        · rw [profile_zero T _ _ (Nat.le_of_not_gt hlt), profile_zero T _ _ (Nat.le_of_not_gt hlt)]
      exact hqw.ne (profile_injective T ep).symm
    obtain ⟨v,hold,hnew⟩ := new_slot T hm q w (u j) (hb j) hleft hright
    refine ⟨v,funext fun i => ?_⟩
    rcases lt_trichotomy i.val m with h | h | h
    · simp [profile, show i.val ≠ m from h.ne,hold,hw,u',h]
    · have e : i = j := Fin.ext h
      subst i
      exact hnew
    · rw [profile_zero _ _ _ h, hz _ h]

/-- Realize each prefix of a position vector by successive leaf insertion. -/
theorem exists_prefix (P : SPosition s) (m : ℕ) (hm : m ≤ n) :
    ∃ T : TreePrefix s m, ∀ i j : Fin n, j.val < m → T.pos i j = P.pos i j := by
  induction m with
  | zero => exact ⟨.empty,by omega⟩
  | succ m ih =>
    obtain ⟨T,hT⟩ := ih (by omega)
    let j : Fin n := ⟨m,by omega⟩
    have hc (a b : Fin n) (hab : a < b) (hb : b.val < m) :
        (0 < P.pos b j → T.pos a b ≤ P.pos a j) ∧
        (P.pos b j < s b → P.pos a j ≤ T.pos a b) := by
      rw [hT a b hb]
      have hbj : b < j := hb
      exact ⟨P.transitive hab hbj, P.planar hab hbj⟩
    obtain ⟨q,hq⟩ := exists_leaf_profile T (fun i => P.pos i j) (fun i => P.bound i j)
      (fun i hi => P.zero_of_not_lt i j (fun h => Nat.not_lt_of_ge hi h)) hc
    refine ⟨T.insert j.isLt q, fun i b hb => ?_⟩
    by_cases h : b.val = m
    · have e : b = j := Fin.ext h
      subst b
      simpa [pos,j] using congrFun hq i
    · simpa only [pos,ite_eq_right h] using hT i b (by omega)

end TreePrefix

namespace STree

theorem toPosition_injective : Function.Injective (toPosition (s := s)) :=
  fun _ _ h => TreePrefix.pos_injective (congrArg SPosition.pos h)

theorem toPosition_surjective : Function.Surjective (toPosition (s := s)) := by
  intro P
  obtain ⟨T,hT⟩ := TreePrefix.exists_prefix P n le_rfl
  exact ⟨T, SPosition.ext (funext fun i => funext fun j => hT i j j.isLt)⟩

noncomputable def positionEquiv : STree s ≃ SPosition s :=
  Equiv.ofBijective toPosition ⟨toPosition_injective, toPosition_surjective⟩

instance : Finite (STree s) := Finite.of_injective toPosition toPosition_injective

noncomputable instance : Fintype (STree s) := Fintype.ofFinite _

instance : PartialOrder (STree s) := PartialOrder.lift toPosition toPosition_injective

noncomputable def positionOrderIso : STree s ≃o SPosition s where
  toEquiv := positionEquiv
  map_rel_iff' := Iff.rfl

noncomputable instance treeLattice : Lattice (STree s) where
  sup x y := positionEquiv.symm (toPosition x ⊔ toPosition y)
  inf x y := positionEquiv.symm (toPosition x ⊓ toPosition y)
  le_sup_left x y := positionOrderIso.le_iff_le.mp (by
    change positionEquiv x ≤ positionEquiv (positionEquiv.symm _)
    rw [Equiv.apply_symm_apply]
    exact le_sup_left)
  le_sup_right x y := positionOrderIso.le_iff_le.mp (by
    change positionEquiv y ≤ positionEquiv (positionEquiv.symm _)
    rw [Equiv.apply_symm_apply]
    exact le_sup_right)
  sup_le x y z h₁ h₂ := positionOrderIso.le_iff_le.mp (by
    change positionEquiv (positionEquiv.symm _) ≤ _
    rw [Equiv.apply_symm_apply]
    exact sup_le h₁ h₂)
  inf_le_left x y := positionOrderIso.le_iff_le.mp (by
    change positionEquiv (positionEquiv.symm _) ≤ positionEquiv x
    rw [Equiv.apply_symm_apply]
    exact inf_le_left)
  inf_le_right x y := positionOrderIso.le_iff_le.mp (by
    change positionEquiv (positionEquiv.symm _) ≤ positionEquiv y
    rw [Equiv.apply_symm_apply]
    exact inf_le_right)
  le_inf x y z h₁ h₂ := positionOrderIso.le_iff_le.mp (by
    change _ ≤ positionEquiv (positionEquiv.symm _)
    rw [Equiv.apply_symm_apply]
    exact le_inf h₁ h₂)

noncomputable instance treeOrderBot : OrderBot (STree s) where
  bot := positionEquiv.symm ⊥
  bot_le x := positionOrderIso.le_iff_le.mp (by
    change positionEquiv (positionEquiv.symm _) ≤ _
    rw [Equiv.apply_symm_apply]
    exact bot_le)

#print axioms toPosition_surjective
#print axioms positionOrderIso
#print axioms treeLattice

end STree

end Permutree
```

### `LatticeQuotient.lean`

```lean
import Mathlib.Order.Lattice.Congruence
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.EquivFin

namespace Permutree

variable {L : Type*} [Lattice L]

/-- The intersection of all lattice congruences containing a given relation. -/
def generatedCongruence (R : L → L → Prop) : LatticeCon L where
  r x y := ∀ c : LatticeCon L, (∀ a b, R a b → c.r a b) → c.r x y
  iseqv.refl x c _ := c.refl x
  iseqv.symm h c hc := c.symm (h c hc)
  iseqv.trans h h' c hc := c.trans (h c hc) (h' c hc)
  inf h h' c hc := c.inf (h c hc) (h' c hc)
  sup h h' c hc := c.sup (h c hc) (h' c hc)

theorem generated_contains (R : L → L → Prop) {x y : L} (h : R x y) :
    (generatedCongruence R).r x y := fun _ hc => hc x y h

theorem generated_le (R : L → L → Prop) (c : LatticeCon L) (h : ∀ a b, R a b → c.r a b)
    {x y : L} (hxy : (generatedCongruence R).r x y) : c.r x y := hxy c h

def ConQuot (c : LatticeCon L) := Quotient c.toSetoid

namespace ConQuot

variable (c : LatticeCon L)

def mk (x : L) : ConQuot c := Quotient.mk _ x

theorem mk_surjective : Function.Surjective (mk c) := fun q => Quotient.inductionOn q (fun x => ⟨x,rfl⟩)

theorem mk_eq_mk {x y : L} : mk c x = mk c y ↔ c.r x y :=
  ⟨Quotient.exact, Quotient.sound⟩

instance [Finite L] : Finite (ConQuot c) := Finite.of_surjective (mk c) (mk_surjective c)

noncomputable instance [Finite L] : Fintype (ConQuot c) := Fintype.ofFinite _

instance : Max (ConQuot c) :=
  ⟨fun a b => Quotient.liftOn₂ a b (fun x y => mk c (x ⊔ y))
    (fun _ _ _ _ hx hy => Quotient.sound (c.sup hx hy))⟩

instance : Min (ConQuot c) :=
  ⟨fun a b => Quotient.liftOn₂ a b (fun x y => mk c (x ⊓ y))
    (fun _ _ _ _ hx hy => Quotient.sound (c.inf hx hy))⟩

@[simp] theorem mk_sup (x y : L) : mk c (x ⊔ y) = mk c x ⊔ mk c y := rfl
@[simp] theorem mk_inf (x y : L) : mk c (x ⊓ y) = mk c x ⊓ mk c y := rfl

private theorem qsup_assoc (a b d : ConQuot c) : a ⊔ b ⊔ d = a ⊔ (b ⊔ d) := by
  obtain ⟨x,rfl⟩ := mk_surjective c a
  obtain ⟨y,rfl⟩ := mk_surjective c b
  obtain ⟨z,rfl⟩ := mk_surjective c d
  simpa using congrArg (mk c) (sup_assoc x y z)

private theorem qsup_comm (a b : ConQuot c) : a ⊔ b = b ⊔ a := by
  obtain ⟨x,rfl⟩ := mk_surjective c a
  obtain ⟨y,rfl⟩ := mk_surjective c b
  simpa using congrArg (mk c) (sup_comm x y)

private theorem qsup_idem (a : ConQuot c) : a ⊔ a = a := by
  obtain ⟨x,rfl⟩ := mk_surjective c a
  exact congrArg (mk c) (sup_idem (a := x))

instance : LE (ConQuot c) := ⟨fun a b => a ⊔ b = b⟩

theorem le_iff_sup {a b : ConQuot c} : a ≤ b ↔ a ⊔ b = b := Iff.rfl

theorem le_iff_inf {a b : ConQuot c} : a ≤ b ↔ a ⊓ b = a := by
  obtain ⟨x,rfl⟩ := mk_surjective c a
  obtain ⟨y,rfl⟩ := mk_surjective c b
  change mk c (x ⊔ y) = mk c y ↔ mk c (x ⊓ y) = mk c x
  rw [mk_eq_mk, mk_eq_mk]
  constructor
  · intro h
    simpa [inf_comm] using c.symm (c.inf h (c.refl x))
  · intro h
    simpa [sup_comm] using c.symm (c.sup h (c.refl y))

instance : PartialOrder (ConQuot c) where
  le_refl := qsup_idem c
  le_trans _ _ _ hab hbd := by
    rw [le_iff_sup] at *
    rw [← hbd, ← qsup_assoc, hab]
  le_antisymm a b hab hba := by
    rw [le_iff_sup] at *
    rw [← hba, qsup_comm, hab]

theorem mk_mono : Monotone (mk c) := fun _ _ h => by
  rw [le_iff_sup, ← mk_sup, sup_eq_right.mpr h]

instance : Lattice (ConQuot c) where
  sup := max
  inf := min
  le_sup_left a b := by rw [le_iff_sup, ← qsup_assoc, qsup_idem]
  le_sup_right a b := by
    rw [qsup_comm c a b, le_iff_sup, ← qsup_assoc, qsup_idem]
  sup_le a b d ha hb := by
    rw [le_iff_sup] at *
    rw [qsup_assoc, hb, ha]
  inf_le_left a b := by
    obtain ⟨x,rfl⟩ := mk_surjective c a
    obtain ⟨y,rfl⟩ := mk_surjective c b
    exact mk_mono c inf_le_left
  inf_le_right a b := by
    obtain ⟨x,rfl⟩ := mk_surjective c a
    obtain ⟨y,rfl⟩ := mk_surjective c b
    exact mk_mono c inf_le_right
  le_inf a b d hab had := by
    obtain ⟨x,rfl⟩ := mk_surjective c a
    obtain ⟨y,rfl⟩ := mk_surjective c b
    obtain ⟨z,rfl⟩ := mk_surjective c d
    rw [le_iff_inf] at *
    change mk c (x ⊓ y) = mk c x at hab
    change mk c (x ⊓ z) = mk c x at had
    change mk c (x ⊓ (y ⊓ z)) = mk c x
    rw [← inf_assoc, mk_inf, hab, ← mk_inf, had]

instance [OrderBot L] : OrderBot (ConQuot c) where
  bot := mk c ⊥
  bot_le q := by
    obtain ⟨x,rfl⟩ := mk_surjective c q
    exact mk_mono c bot_le

@[simp] theorem mk_bot [OrderBot L] : mk c ⊥ = ⊥ := rfl

section Minimum

variable [Finite L]

private noncomputable def fiber (q : ConQuot c) : Finset L := by
  classical
  letI := Fintype.ofFinite L
  exact Finset.univ.filter fun x => mk c x = q

private theorem mem_fiber {q : ConQuot c} {x : L} : x ∈ fiber c q ↔ mk c x = q := by
  classical
  simp [fiber]

private theorem fiber_nonempty (q : ConQuot c) : (fiber c q).Nonempty := by
  obtain ⟨x,hx⟩ := mk_surjective c q
  exact ⟨x, (mem_fiber c).mpr hx⟩

/-- The meet of the members of a congruence class is its minimum. -/
noncomputable def minRep (q : ConQuot c) : L :=
  (fiber c q).inf' (fiber_nonempty c q) id

theorem minRep_le_of_eq {q : ConQuot c} {x : L} (h : mk c x = q) : minRep c q ≤ x :=
  Finset.inf'_le id ((mem_fiber c).mpr h)

@[simp] theorem mk_minRep (q : ConQuot c) : mk c (minRep c q) = q := by
  rw [minRep, Finset.apply_inf'_eq_inf'_comp (f := id) _ (mk c) (mk_inf c)]
  apply le_antisymm
  · obtain ⟨x,hx⟩ := fiber_nonempty c q
    exact (Finset.inf'_le (mk c ∘ id) hx).trans (le_of_eq ((mem_fiber c).mp hx))
  · exact Finset.le_inf' (fiber_nonempty c q) (mk c ∘ id) fun x hx => le_of_eq ((mem_fiber c).mp hx).symm

theorem gc : GaloisConnection (minRep c) (mk c) := by
  intro q x
  constructor
  · intro h
    simpa using mk_mono c h
  · intro h
    rw [le_iff_inf] at h
    exact (minRep_le_of_eq c (by simpa using h : mk c (minRep c q ⊓ x) = q)).trans inf_le_right

theorem minRep_injective : Function.Injective (minRep c) :=
  Function.LeftInverse.injective (mk_minRep c)

theorem minRep_mono : Monotone (minRep c) := (gc c).monotone_l

@[simp] theorem minRep_sup (a b : ConQuot c) :
    minRep c (a ⊔ b) = minRep c a ⊔ minRep c b := (gc c).l_sup

@[simp] theorem minRep_bot [OrderBot L] : minRep c ⊥ = ⊥ := (gc c).l_bot

end Minimum

#print axioms instLattice
#print axioms gc

end ConQuot

end Permutree
```

### `CanonicalQuotient.lean`

```lean
import LatticeQuotient
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Atoms

namespace Permutree

variable {L : Type*} [Lattice L] [OrderBot L]

/-- An irredundant join decomposition refining all join decompositions. -/
def IsCanonicalJoinRep [DecidableEq L] (X : Finset L) (x : L) : Prop :=
  X.sup id = x ∧
  (∀ a ∈ X, ¬a ≤ (X.erase a).sup id) ∧
  ∀ Y : Finset L, Y.sup id = x → ∀ a ∈ X, ∃ b ∈ Y, a ≤ b

def CanonicalFaceOfSize (L : Type*) [Lattice L] [OrderBot L] [DecidableEq L] (m : ℕ) :=
  {X : Finset L // IsCanonicalJoinRep X (X.sup id) ∧ X.card = m}

noncomputable instance [Finite L] [DecidableEq L] (m : ℕ) :
    Fintype (CanonicalFaceOfSize L m) := by
  classical
  unfold CanonicalFaceOfSize
  letI := Fintype.ofFinite L
  infer_instance

theorem IsCanonicalJoinRep.eq_of_le [DecidableEq L] {X : Finset L} {x a b : L}
    (h : IsCanonicalJoinRep X x) (ha : a ∈ X) (hb : b ∈ X) (hab : a ≤ b) : a = b := by
  by_contra hne
  exact h.2.1 a ha (hab.trans (Finset.le_sup (f := id) (Finset.mem_erase.mpr ⟨(fun e => hne e.symm),hb⟩)))

theorem IsCanonicalJoinRep.unique [DecidableEq L] {X Y : Finset L} {x : L}
    (hx : IsCanonicalJoinRep X x) (hy : IsCanonicalJoinRep Y x) : X = Y := by
  have sub {A B : Finset L} (hA : IsCanonicalJoinRep A x) (hB : IsCanonicalJoinRep B x) :
      A ⊆ B := by
    intro a ha
    obtain ⟨b,hb,hab⟩ := hA.2.2 B hB.1 a ha
    obtain ⟨a',ha',hba'⟩ := hB.2.2 A hA.1 b hb
    have e := hA.eq_of_le ha ha' (hab.trans hba')
    rwa [le_antisymm hab (e ▸ hba')]
  exact Finset.Subset.antisymm (sub hx hy) (sub hy hx)

def JoinSemidistributive (L : Type*) [Lattice L] : Prop :=
  ∀ x y z : L, x ⊔ y = x ⊔ z → x ⊔ (y ⊓ z) = x ⊔ y

namespace ConQuot

variable [Finite L] (c : LatticeCon L)

noncomputable def minEmbedding : ConQuot c ↪ L := ⟨minRep c, minRep_injective c⟩

omit [OrderBot L] in
@[simp] theorem minEmbedding_apply (q : ConQuot c) : minEmbedding c q = minRep c q := rfl

omit [OrderBot L] in
theorem minRep_le_iff {p q : ConQuot c} : minRep c p ≤ minRep c q ↔ p ≤ q := by
  rw [gc c p (minRep c q), mk_minRep]

theorem sup_map_minRep (X : Finset (ConQuot c)) :
    (X.map (minEmbedding c)).sup id = minRep c (X.sup id) := by
  rw [Finset.sup_map, Finset.apply_sup_eq_sup_comp (f := id) (minRep c) (minRep_sup c)
    (minRep_bot c)]
  rfl

omit [Finite L] in
theorem sup_image_mk [DecidableEq (ConQuot c)] (Y : Finset L) :
    (Y.image (mk c)).sup id = mk c (Y.sup id) := by
  rw [Finset.sup_image, Finset.apply_sup_eq_sup_comp (f := id) (mk c) (mk_sup c) (mk_bot c)]
  rfl

omit [OrderBot L] in
theorem joinSemidistributive_quotient (h : JoinSemidistributive L) :
    JoinSemidistributive (ConQuot c) := by
  intro x y z e
  have e' : minRep c x ⊔ minRep c y = minRep c x ⊔ minRep c z := by
    simpa only [minRep_sup] using congrArg (minRep c) e
  simpa using congrArg (mk c) (h _ _ _ e')

/-- The minimal-representative section identifies canonical join
representations in the quotient with those in the source on its image. -/
theorem isCanonical_map_minRep [DecidableEq L] [DecidableEq (ConQuot c)]
    (X : Finset (ConQuot c)) (x : ConQuot c) :
    IsCanonicalJoinRep (X.map (minEmbedding c)) (minRep c x) ↔ IsCanonicalJoinRep X x := by
  have irred (a : ConQuot c) :
      minRep c a ≤ ((X.map (minEmbedding c)).erase (minRep c a)).sup id ↔
        a ≤ (X.erase a).sup id := by
    rw [← minEmbedding_apply c a, ← Finset.map_erase, sup_map_minRep, minEmbedding_apply,
      minRep_le_iff]
  constructor
  · intro h
    refine ⟨minRep_injective c ((sup_map_minRep c X).symm.trans h.1), ?_, ?_⟩
    · intro a ha hle
      exact h.2.1 _ (Finset.mem_map.mpr ⟨a,ha,rfl⟩) ((irred a).mpr hle)
    · intro Y hy a ha
      obtain ⟨b,hb,hle⟩ := h.2.2 (Y.map (minEmbedding c))
        ((sup_map_minRep c Y).trans (congrArg (minRep c) hy)) _ (Finset.mem_map.mpr ⟨a,ha,rfl⟩)
      obtain ⟨b',hb',rfl⟩ := Finset.mem_map.mp hb
      exact ⟨b',hb',(minRep_le_iff c).mp hle⟩
  · intro h
    refine ⟨(sup_map_minRep c X).trans (congrArg (minRep c) h.1), ?_, ?_⟩
    · intro a ha hle
      obtain ⟨a',ha',rfl⟩ := Finset.mem_map.mp ha
      exact h.2.1 _ ha' ((irred a').mp hle)
    · intro Y hy a ha
      obtain ⟨a',ha',rfl⟩ := Finset.mem_map.mp ha
      have hy' := (sup_image_mk c Y).trans (congrArg (mk c) hy)
      rw [mk_minRep] at hy'
      obtain ⟨b,hb,hle⟩ := h.2.2 (Y.image (mk c)) hy' _ ha'
      obtain ⟨b',hb',rfl⟩ := Finset.mem_image.mp hb
      exact ⟨b',hb',(gc c _ _).mpr hle⟩

def IsUncontracted (j : L) : Prop := ∀ y, y ⋖ j → mk c y ≠ mk c j

omit [OrderBot L] in
theorem isUncontracted_iff_minRep (j : L) :
    IsUncontracted c j ↔ minRep c (mk c j) = j := by
  have hle : minRep c (mk c j) ≤ j := (gc c _ _).mpr le_rfl
  constructor
  · intro h
    by_contra hne
    obtain ⟨y,hy,hyj⟩ := exists_le_covBy_of_lt (lt_of_le_of_ne hle hne)
    have hp₁ := mk_mono c hy
    have hp₂ := mk_mono c hyj.le
    rw [mk_minRep] at hp₁
    exact h y hyj (le_antisymm hp₂ hp₁)
  · intro h y hy he
    have := minRep_le_of_eq c he
    rw [h] at this
    exact (not_le_of_gt hy.lt) this

theorem canonical_rep_of_minimum [DecidableEq L] [DecidableEq (ConQuot c)]
    {X : Finset L} {x : L} (h : IsCanonicalJoinRep X x) (hx : minRep c (mk c x) = x) :
    ∀ a ∈ X, minRep c (mk c a) = a := by
  intro a ha
  let Y := (X.image (mk c)).map (minEmbedding c)
  have hy : Y.sup id = x := by
    rw [show Y = (X.image (mk c)).map (minEmbedding c) from rfl,
      sup_map_minRep, sup_image_mk, h.1, hx]
  obtain ⟨b,hb,hab⟩ := h.2.2 Y hy a ha
  obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hb
  obtain ⟨a',ha',rfl⟩ := Finset.mem_image.mp hq
  have hle : minRep c (mk c a') ≤ a' := (gc c _ _).mpr le_rfl
  have he := h.eq_of_le ha ha' (hab.trans hle)
  rw [← he] at hab hle
  exact le_antisymm hle hab

/-- Section 4.1.2, graded by the number of joinands. The carrier on the right
is the canonical join complex restricted to uncontracted vertices. -/
noncomputable def canonicalQuotientEquiv [DecidableEq L] [DecidableEq (ConQuot c)] (m : ℕ) :
    CanonicalFaceOfSize (ConQuot c) m ≃
      {X : CanonicalFaceOfSize L m // ∀ a ∈ X.val, IsUncontracted c a} := by
  have map_image (X : Finset L) (h : ∀ a ∈ X, IsUncontracted c a) :
      (X.image (mk c)).map (minEmbedding c) = X := by
    ext a
    simp only [Finset.mem_map, Finset.mem_image, exists_exists_and_eq_and, minEmbedding_apply]
    constructor
    · rintro ⟨b,hb,rfl⟩
      rw [(isUncontracted_iff_minRep c b).mp (h b hb)]
      exact hb
    · intro ha
      exact ⟨a,ha,(isUncontracted_iff_minRep c a).mp (h a ha)⟩
  refine
    { toFun := fun X => ⟨⟨X.val.map (minEmbedding c), ?_, by simpa using X.property.2⟩, ?_⟩
      invFun := fun Y => ⟨Y.val.val.image (mk c), ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [sup_map_minRep]
    exact (isCanonical_map_minRep c _ _).mpr X.property.1
  · intro a ha
    obtain ⟨b,_,rfl⟩ := Finset.mem_map.mp ha
    exact (isUncontracted_iff_minRep c _).mpr (by simp)
  · apply (isCanonical_map_minRep c _ _).mp
    rw [← sup_map_minRep, map_image _ Y.property]
    exact Y.val.property.1
  · rw [← Finset.card_map (f := minEmbedding c), map_image _ Y.property, Y.val.property.2]
  · intro X
    apply Subtype.ext
    change (X.val.map (minEmbedding c)).image (mk c) = X.val
    ext a
    simp
  · intro Y
    exact Subtype.ext (Subtype.ext (map_image _ Y.property))

#print axioms canonicalQuotientEquiv
#print axioms joinSemidistributive_quotient

end ConQuot

end Permutree
```

### `CanonicalFinite.lean`

```lean
import CanonicalQuotient
import Mathlib.Data.Fintype.BigOperators

namespace Permutree

variable {L : Type*} [Lattice L] [OrderBot L]

omit [OrderBot L] in
private theorem exists_least_join_witness [Finite L] (h : JoinSemidistributive L)
    {x y : L} (hy : y ≤ x) : ∃ j : L, y ⊔ j = x ∧ ∀ a, y ⊔ a = x → j ≤ a := by
  classical
  let _ : Fintype L := Fintype.ofFinite L
  let B := Finset.univ.filter (fun a : L => y ⊔ a = x)
  have hm {a : L} : a ∈ B ↔ y ⊔ a = x := by simp [B]
  have he : B.Nonempty := ⟨x, hm.mpr (sup_eq_right.mpr hy)⟩
  have hc : ∀ a ∈ ({a : L | y ⊔ a = x} : Set L), ∀ b ∈ {a : L | y ⊔ a = x},
      a ⊓ b ∈ {a : L | y ⊔ a = x} := by
    intro a ha b hb
    exact (h y a b (ha.trans hb.symm)).trans ha
  refine ⟨B.inf' he id, ?_, fun a ha => Finset.inf'_le id (hm.mpr ha)⟩
  exact Finset.inf'_mem {a : L | y ⊔ a = x} hc B he id (fun a ha => hm.mp ha)

omit [OrderBot L] in
private theorem join_eq_of_cover {x y a : L} (hy : y ⋖ x) (ha : a ≤ x) (hay : ¬a ≤ y) :
    y ⊔ a = x :=
  (hy.eq_or_eq le_sup_left (sup_le hy.le ha)).resolve_left (fun e => hay (sup_le_iff.mp e.le).2)

theorem exists_canonical [Finite L] [DecidableEq L] (h : JoinSemidistributive L) (x : L) :
    ∃ X : Finset L, IsCanonicalJoinRep X x := by
  classical
  let _ : Fintype L := Fintype.ofFinite L
  let J (y : {y : L // y ⋖ x}) : L := (exists_least_join_witness h y.property.le).choose
  have hJ (y : {y : L // y ⋖ x}) :
      y.val ⊔ J y = x ∧ ∀ a, y.val ⊔ a = x → J y ≤ a :=
    (exists_least_join_witness h y.property.le).choose_spec
  let Z : Finset L := Finset.univ.image J
  have memZ {a : L} : a ∈ Z ↔ ∃ y, J y = a := by simp [Z]
  have hZ : Z.sup id = x := by
    have hle : Z.sup id ≤ x := Finset.sup_le fun a ha => by
      obtain ⟨y,rfl⟩ := memZ.mp ha
      exact le_sup_right.trans (hJ y).1.le
    apply hle.antisymm
    by_contra hn
    obtain ⟨y,hy,hyx⟩ := exists_le_covBy_of_lt (lt_of_le_not_ge hle hn)
    let y' : {y : L // y ⋖ x} := ⟨y,hyx⟩
    have : J y' ≤ y := (Finset.le_sup (f := id) (memZ.mpr ⟨y',rfl⟩)).trans hy
    exact hyx.ne ((sup_eq_left.mpr this).symm.trans (hJ y').1)
  let Candidates := Z.powerset.filter fun X => X.sup id = x
  have hCandidates : Candidates.Nonempty := ⟨Z, by simp [Candidates,hZ]⟩
  obtain ⟨X,hX,hXmin⟩ := Finset.exists_mem_eq_inf' hCandidates Finset.card
  have hmin : ∀ Y ∈ Candidates, X.card ≤ Finset.card Y := by
    intro Y hY
    rw [← hXmin]
    exact Finset.inf'_le Finset.card hY
  have hXdata : X ⊆ Z ∧ X.sup id = x := by simpa [Candidates] using hX
  refine ⟨X, hXdata.2, ?_, ?_⟩
  · intro a ha hle
    have he : (X.erase a).sup id = x := by
      calc
        (X.erase a).sup id = (insert a (X.erase a)).sup id := by
          rw [Finset.sup_insert]
          exact (sup_eq_right.mpr hle).symm
        _ = x := by rw [Finset.insert_erase ha, hXdata.2]
    have hm : X.erase a ∈ Candidates := by
      simpa [Candidates,he] using (Finset.erase_subset a X).trans hXdata.1
    exact (not_le_of_gt (Finset.card_erase_lt_of_mem ha)) (hmin _ hm)
  · intro Y hY a ha
    obtain ⟨y,rfl⟩ := memZ.mp (hXdata.1 ha)
    have hnot : ¬ ∀ b ∈ Y, b ≤ y.val := by
      intro hall
      have hle := Finset.sup_le (f := id) hall
      rw [hY] at hle
      exact (not_le_of_gt y.property.lt) hle
    push Not at hnot
    obtain ⟨b,hb,hby⟩ := hnot
    have hb' : b ≤ x := hY ▸ Finset.le_sup (f := id) hb
    exact ⟨b,hb,(hJ y).2 _ (join_eq_of_cover y.property hb' hby)⟩

/-- All canonical faces, without a size restriction. -/
abbrev CanonicalFaces (L : Type*) [Lattice L] [OrderBot L] [DecidableEq L] :=
  {X : Finset L // IsCanonicalJoinRep X (X.sup id)}

/-- Taking joins identifies faces with elements when every element has a canonical join. -/
noncomputable def canonicalJoinEquiv [DecidableEq L]
    (h : ∀ x : L, ∃ X : Finset L, IsCanonicalJoinRep X x) : CanonicalFaces L ≃ L :=
  Equiv.ofBijective (fun X => X.val.sup id) ⟨by
    intro X Y he
    change X.val.sup id = Y.val.sup id at he
    exact Subtype.ext (X.property.unique (he.symm ▸ Y.property)), by
    intro x
    obtain ⟨X,hX⟩ := h x
    exact ⟨⟨X,hX.1 ▸ hX⟩,hX.1⟩⟩

private theorem canonical_card_sum (N : ℕ) (M : Type*) [Lattice M] [OrderBot M] [DecidableEq M] [Fintype M]
      (hM : ∀ x : M, ∃ X : Finset M, IsCanonicalJoinRep X x) (hN : Fintype.card M < N) :
      Fintype.card M = ∑ m : Fin N, Fintype.card (CanonicalFaceOfSize M m.val) := by
  let e : CanonicalFaces M ≃ (Σ m : Fin N, CanonicalFaceOfSize M m.val) :=
    { toFun := fun X => ⟨⟨X.val.card, (Finset.card_le_univ _).trans_lt hN⟩, ⟨X.val,X.property,rfl⟩⟩
      invFun := fun Z => ⟨Z.2.val,Z.2.property.1⟩
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨m,hm⟩,X⟩
        have hx := X.property.2
        dsimp at hx
        apply Sigma.ext
        · exact Fin.ext hx
        · cases X with
          | mk X hX =>
            change X.card = m at hx
            subst m
            rfl }
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr ((canonicalJoinEquiv hM).symm.trans e)

theorem card_eq_of_canonical_counts {K : Type*} [Lattice K] [OrderBot K] [DecidableEq K]
    [DecidableEq L] [Fintype L] [Fintype K]
    (hL : ∀ x : L, ∃ X : Finset L, IsCanonicalJoinRep X x)
    (hK : ∀ x : K, ∃ X : Finset K, IsCanonicalJoinRep X x)
    (h : ∀ m, Fintype.card (CanonicalFaceOfSize L m) = Fintype.card (CanonicalFaceOfSize K m)) :
    Fintype.card L = Fintype.card K := by
  classical
  let N := max (Fintype.card L) (Fintype.card K) + 1
  rw [canonical_card_sum N L hL (Nat.lt_succ_of_le (le_max_left _ _)),
    canonical_card_sum N K hK (Nat.lt_succ_of_le (le_max_right _ _))]
  exact Finset.sum_congr rfl fun m _ => h m.val

#print axioms exists_canonical
#print axioms card_eq_of_canonical_counts

end Permutree
```

### `SPermutree.lean`

```lean
import SArc
import STreeLattice
import LatticeQuotient
import Mathlib.Order.Cover

namespace Permutree

variable {n : ℕ} {s : Fin n → ℕ}

namespace SArc

/-- Nodes of the grafted right comb in Definition 48. -/
def graftNodes (a : SArc s) : Finset (Fin n) := insert a.finish a.right

theorem start_lt_mem_graftNodes {a : SArc s} {j : Fin n} (h : j ∈ a.graftNodes) : a.start < j := by
  rcases Finset.mem_insert.mp h with rfl | h
  · exact a.start_lt_finish
  · exact (mem_positiveInterior.mp (a.right_subset h)).1

theorem r_pos (a : SArc s) : 0 < a.r := Nat.zero_lt_succ _
theorem r_le (a : SArc s) : a.r ≤ s a.start := a.label.isLt

theorem leafCount_pos (s : Fin n → ℕ) (m : ℕ) : 0 < leafCount s m := by
  induction m with
  | zero => exact Nat.zero_lt_succ _
  | succ m ih =>
    simp only [leafCount]
    omega

/-- Track the rightmost leaf of the grafted branch. When i is inserted at
the last leaf, the graft starts at the (r+1)-st leaf from its right.
Subsequent right-comb insertions either extend this branch or attach
at the global last leaf, leaving the graft's slot intact. -/
def combPrefix (a : SArc s) :
    (m : ℕ) → m ≤ n → TreePrefix s m × Option (Fin (leafCount s m))
  | 0, _ => (.empty, none)
  | m+1, hm =>
    let j : Fin n := ⟨m, Nat.lt_of_succ_le hm⟩
    let (T, branch) := combPrefix a m (Nat.le_of_lt j.isLt)
    have hcount : leafCount s (m+1) = leafCount s m + s j := leafCount_succ s j.isLt
    have hp := leafCount_pos s m
    let lastLeaf : Fin (leafCount s m) := ⟨leafCount s m - 1, by omega⟩
    let q := if j ∈ a.graftNodes then branch.getD lastLeaf else lastLeaf
    let branch' : Option (Fin (leafCount s (m+1))) :=
      if j = a.start then
        some ⟨leafCount s (m+1) - 1 - a.r, by omega⟩
      else
        branch.map fun p => ⟨p.val + (if j ∈ a.graftNodes then s j else 0), by
          have h := p.isLt
          split <;> omega⟩
    (T.insert j.isLt q, branch')

/-- Definition 48's join comb with the auxiliary right comb grafted at i. -/
def Tvee (a : SArc s) : STree s := (combPrefix a n (Nat.le_refl n)).1

end SArc

/-- Generate the decoration congruence by contracting the lower covers of
the join combs belonging to forbidden arcs. -/
noncomputable def permutreeCon (s : Fin n → ℕ) (d : Decoration s) : LatticeCon (STree s) :=
  generatedCongruence fun x y => ∃ a : SArc s, ¬Allowed d a ∧ x = a.Tvee ∧ y ⋖ x

abbrev PermutreeLattice (s : Fin n → ℕ) (d : Decoration s) :=
  ConQuot (permutreeCon s d)

theorem forbidden_contracts {d : Decoration s} {a : SArc s} (h : ¬Allowed d a)
    {y : STree s} (hy : y ⋖ a.Tvee) :
    ConQuot.mk (permutreeCon s d) y = ConQuot.mk (permutreeCon s d) a.Tvee :=
  (ConQuot.mk_eq_mk _).mpr ((permutreeCon s d).symm (generated_contains _ ⟨a,h,rfl,hy⟩))

#print axioms SArc.Tvee
#print axioms permutreeCon
#print axioms forbidden_contracts

end Permutree
```

### `CombCoordinates.lean`

```lean
import SPermutree
import ArcShortening
import Mathlib.Order.Atoms

namespace Permutree

variable {n : ℕ} {s : Fin n → ℕ}

namespace TreePrefix

def lastLeaf (s : Fin n → ℕ) (m : ℕ) : Fin (leafCount s m) :=
  ⟨leafCount s m - 1, by have := SArc.leafCount_pos s m; omega⟩

theorem oldLeaf_child {m : ℕ} (hm : m < n) (q : Fin (leafCount s m))
    (v : Fin (leafCount s (m+1))) (h₁ : q.val ≤ v.val)
    (h₂ : v.val ≤ q.val + s ⟨m,hm⟩) :
    oldLeaf hm q v = q := by
  apply Fin.ext
  rw [oldLeaf_val]
  simp [not_lt_of_ge h₁,not_lt_of_ge h₂]

theorem oldLeaf_before {m : ℕ} (hm : m < n) (q : Fin (leafCount s m))
    (v : Fin (leafCount s (m+1))) (h : v.val < q.val) :
    (oldLeaf hm q v).val = v.val := by rw [oldLeaf_val,ite_eq_left h]

theorem profile_lastLeaf {m : ℕ} (T : TreePrefix s m) (i : Fin n) :
    T.profile (lastLeaf s m) i = 0 := by
  induction T with
  | empty => rfl
  | @insert m T hm q ih =>
    have hl : (lastLeaf s (m+1)).val = (lastLeaf s m).val + s ⟨m,hm⟩ := by
      have hc := leafCount_succ s hm
      have hp := SArc.leafCount_pos s m
      simp only [lastLeaf]
      omega
    have hq : q.val ≤ (lastLeaf s m).val := by
      have h := q.isLt
      change q.val ≤ leafCount s m - 1
      omega
    by_cases hi : i.val = m
    · have hi' : i = ⟨m,hm⟩ := Fin.ext hi
      subst i
      simp only [profile,ite_true]
      change (if (lastLeaf s (m+1)).val < q.val then s ⟨m,hm⟩
        else q.val + s ⟨m,hm⟩ - (lastLeaf s (m+1)).val) = 0
      rw [hl,ite_eq_right (by omega)]
      omega
    · rw [profile,ite_eq_right hi]
      have he : oldLeaf hm q (lastLeaf s (m+1)) = lastLeaf s m := by
        apply Fin.ext
        rw [oldLeaf_val,hl,ite_eq_right (by omega : ¬ (lastLeaf s m).val + s ⟨m,hm⟩ < q.val)]
        split
        · omega
        · omega
      rw [he,ih]

end TreePrefix

namespace SArc

open TreePrefix

private def branchProfile (a : SArc s) (m : ℕ) (i : Fin n) : ℕ :=
  if i.val < m then
    if i = a.start then a.r else if a.start < i ∧ i ∉ a.graftNodes then s i else 0
  else 0

private theorem combPrefix_branch (a : SArc s) (m : ℕ) (hm : m ≤ n) :
    ((a.combPrefix m hm).2 = none ↔ m ≤ a.start.val) ∧
    ∀ p : Fin (leafCount s m), (a.combPrefix m hm).2 = some p →
      p.val < (lastLeaf s m).val ∧
      ∀ i, (a.combPrefix m hm).1.profile p i = branchProfile a m i := by
  induction m with
  | zero => simp [combPrefix]
  | succ m ih =>
    let j : Fin n := ⟨m,by omega⟩
    let C := a.combPrefix m (Nat.le_of_lt j.isLt)
    have hc := leafCount_succ s (m := m) j.isLt
    have hp := leafCount_pos s m
    have hl : (lastLeaf s (m+1)).val = (lastLeaf s m).val + s j := by
      simp only [lastLeaf]
      change leafCount s (m+1) - 1 = leafCount s m - 1 + s ⟨m,j.isLt⟩
      omega
    let q := if j ∈ a.graftNodes then C.2.getD (lastLeaf s m) else lastLeaf s m
    let g (p : Fin (leafCount s m)) : Fin (leafCount s (m+1)) :=
      ⟨p.val + (if j ∈ a.graftNodes then s j else 0),by
        have h := p.isLt
        change leafCount s (m+1) = leafCount s m + s j at hc
        split <;> omega⟩
    have hT : (a.combPrefix (m+1) hm).1 = C.1.insert j.isLt q := rfl
    have ihC := ih (Nat.le_of_lt j.isLt)
    change (C.2 = none ↔ m ≤ a.start.val) ∧ _ at ihC
    rcases lt_trichotomy j a.start with hj | hj | hj
    · have hJ : m < a.start.val := hj
      have hC : C.2 = none := ihC.1.mpr hJ.le
      have hh : (a.combPrefix (m+1) hm).2 = none := by
        change (if j = a.start then _ else C.2.map g) = none
        simp [hj.ne,hC]
      simp [hh, Nat.succ_le_of_lt hJ]
    · have hJ : m = a.start.val := congrArg Fin.val hj
      have hjr : a.r ≤ s j := hj ▸ a.r_le
      have hr := a.r_pos
      have hjg : j ∉ a.graftNodes := fun h => (start_lt_mem_graftNodes h).ne hj.symm
      have hq : q = lastLeaf s m := by simp [q,hjg]
      let p : Fin (leafCount s (m+1)) :=
        ⟨(lastLeaf s (m+1)).val - a.r,by have hp := (lastLeaf s (m+1)).isLt; omega⟩
      have hB : (a.combPrefix (m+1) hm).2 = some p := by
        change (if j = a.start then _ else C.2.map g) = some p
        rw [ite_eq_left hj]
        rfl
      have hnot : ¬m + 1 ≤ a.start.val := by omega
      rw [hB]
      refine ⟨by simp [hnot],fun v hv => ?_⟩
      have he : p = v := Option.some.inj hv
      subst v
      have hpval : p.val = (lastLeaf s (m+1)).val - a.r := rfl
      have hpl : p.val < (lastLeaf s (m+1)).val := by omega
      refine ⟨hpl,fun i => ?_⟩
      have hpq : (lastLeaf s m).val ≤ p.val := by omega
      have hps : p.val ≤ (lastLeaf s m).val + s ⟨m,j.isLt⟩ := by
        change p.val ≤ (lastLeaf s m).val + s j
        omega
      have ho := oldLeaf_child j.isLt (lastLeaf s m) p hpq hps
      rw [hT,hq]
      by_cases hi : i = j
      · subst i
        have hbefore : ¬p.val < (lastLeaf s m).val := by omega
        rw [profile,ite_eq_left (show j.val = m from rfl),ite_eq_right hbefore]
        simp only [branchProfile,ite_eq_left (show j.val < m+1 from Nat.lt_succ_self m),ite_eq_left hj]
        change (lastLeaf s m).val + s j - p.val = a.r
        omega
      · have hin : i.val ≠ m := fun h => hi (Fin.ext h)
        rw [profile,ite_eq_right hin,ho,profile_lastLeaf]
        by_cases hlt : i.val < m+1
        · have hil : ¬a.start < i := by omega
          simp [branchProfile,hlt,show i ≠ a.start from fun h => hi (h.trans hj.symm),hil]
        · simp [branchProfile,hlt]
    · have hJ : a.start.val < m := hj
      have hne : C.2 ≠ none := fun e => (Nat.not_le_of_gt hJ) (ihC.1.mp e)
      cases he : C.2 with
      | none => exact (hne he).elim
      | some p =>
        obtain ⟨hp',hprof⟩ := ihC.2 p he
        have hB : (a.combPrefix (m+1) hm).2 = some (g p) := by
          change (if j = a.start then _ else C.2.map g) = some (g p)
          simp [hj.ne.symm,he]
        have hnot : ¬m + 1 ≤ a.start.val := by omega
        rw [hB]
        refine ⟨by simp [hnot], fun v hv => ?_⟩
        have eq : g p = v := Option.some.inj hv
        subst v
        have preserve : oldLeaf j.isLt q (g p) = p := by
          by_cases hg : j ∈ a.graftNodes
          · have hq : q = p := by simp [q,hg,he]
            rw [hq]
            have hgv : (g p).val = p.val + s j := by simp [g,hg]
            apply oldLeaf_child
            · omega
            · exact hgv.le
          · have hq : q = lastLeaf s m := by simp [q,hg]
            have hgv : (g p).val = p.val := by simp [g,hg]
            exact Fin.ext ((oldLeaf_before j.isLt q (g p) (by rw [hgv,hq]; exact hp')).trans hgv)
        refine ⟨?_,fun i => ?_⟩
        · rw [hl]
          change p.val + (if j ∈ a.graftNodes then s j else 0) < (lastLeaf s m).val + s j
          split <;> omega
        · rw [hT,profile]
          by_cases hi : i.val = m
          · have hij : i = j := Fin.ext hi
            subst i
            have hs : j.val < m+1 := Nat.lt_succ_self m
            simp only [branchProfile,ite_eq_left hs,ite_eq_right hj.ne.symm,hj,true_and]
            rw [ite_eq_left hi]
            by_cases hg : j ∈ a.graftNodes
            · simp [q,g,hg,he,show ¬p.val + s j < p.val by omega]
            · simp [q,g,hg,hp']
          · rw [ite_eq_right hi,preserve,hprof]
            have hi' : i.val < m ↔ i.val < m+1 := by omega
            simp only [branchProfile,hi']

/-- Lemma 49 for the join comb, with coordinates valid for i < j. -/
theorem pos_Tvee (a : SArc s) (i j : Fin n) (hij : i < j) :
    a.Tvee.pos i j =
      if j ∈ a.graftNodes then if i = a.start then a.r else if i ∈ a.left then s i else 0 else 0 := by
  have hPrefix (m : ℕ) (hm : m ≤ n) (hj : j.val < m) :
      (a.combPrefix m hm).1.pos i j =
        if j ∈ a.graftNodes then if i = a.start then a.r else if i ∈ a.left then s i else 0 else 0 := by
    induction m with
    | zero => omega
    | succ m ih =>
      let k : Fin n := ⟨m,by omega⟩
      let C := a.combPrefix m (Nat.le_of_lt k.isLt)
      let q := if k ∈ a.graftNodes then C.2.getD (lastLeaf s m) else lastLeaf s m
      change (C.1.insert k.isLt q).pos i j = _
      rw [pos]
      by_cases h : j.val = m
      · have hkj : k = j := Fin.ext h.symm
        rw [ite_eq_left h]
        by_cases hg : j ∈ a.graftNodes
        · rw [ite_eq_left hg]
          have hg' : k ∈ a.graftNodes := hkj ▸ hg
          have ha : a.start < j := start_lt_mem_graftNodes hg
          have hh := combPrefix_branch a m (Nat.le_of_lt k.isLt)
          change (C.2 = none ↔ m ≤ a.start.val) ∧ _ at hh
          have hn : C.2 ≠ none := by
            intro he
            have := hh.1.mp he
            omega
          cases hB : C.2 with
          | none => exact (hn hB).elim
          | some p =>
            have hq : q = p := by simp [q,hg',hB]
            rw [hq,(hh.2 p hB).2]
            have hi : i.val < m := by omega
            rw [branchProfile,ite_eq_left hi]
            by_cases hia : i = a.start
            · simp [hia]
            · rw [ite_eq_right hia,ite_eq_right hia]
              by_cases hz : s i = 0
              · simp [hz]
              · have e : (a.start < i ∧ i ∉ a.graftNodes) ↔ i ∈ a.left := by
                  rw [mem_left,mem_positiveInterior,graftNodes,Finset.mem_insert]
                  have hjf : j ≤ a.finish := by
                    rcases Finset.mem_insert.mp hg with hf | hr
                    · exact hf.le
                    · exact (mem_positiveInterior.mp (a.right_subset hr)).2.1.le
                  have hif := hij.trans_le hjf
                  constructor
                  · rintro ⟨hs,hn⟩
                    exact ⟨⟨hs,hif,hz⟩,fun hr => hn (Or.inr hr)⟩
                  · rintro ⟨⟨hs,_,_⟩,hn⟩
                    exact ⟨hs,fun he => he.elim hif.ne hn⟩
                by_cases hl : i ∈ a.left
                · rw [ite_eq_left (e.mpr hl),ite_eq_left hl]
                · rw [ite_eq_right (fun hh => hl (e.mp hh)),ite_eq_right hl]
        · have hq : q = lastLeaf s m := by simp [q,hkj,hg]
          rw [hq,profile_lastLeaf,ite_eq_right hg]
      · rw [ite_eq_right h]
        exact ih (Nat.le_of_lt k.isLt) (by omega)
  exact hPrefix n le_rfl j.isLt

theorem Tvee_pos_start_finish (a : SArc s) : a.Tvee.pos a.start a.finish = a.r := by
  simp [pos_Tvee a _ _ a.start_lt_finish, graftNodes]

theorem Tvee_has_lower_cover (a : SArc s) : ∃ x : STree s, x ⋖ a.Tvee := by
  have hlt : (⊥ : STree s) < a.Tvee := by
    refine lt_of_le_of_ne bot_le ?_
    intro he
    have hp := congrArg (fun T : STree s => T.pos a.start a.finish) he
    have hb : (⊥ : STree s).pos a.start a.finish = 0 := by
      change (STree.positionEquiv (STree.positionEquiv.symm ⊥)).pos a.start a.finish = 0
      rw [Equiv.apply_symm_apply]
      rfl
    rw [hb,Tvee_pos_start_finish] at hp
    exact a.r_pos.ne' hp.symm
  obtain ⟨x,_,hx⟩ := exists_le_covBy_of_lt hlt
  exact ⟨x,hx⟩

theorem mem_graftNodes_iff_pos (a : SArc s) (j : Fin n) :
    j ∈ a.graftNodes ↔ 0 < a.Tvee.pos a.start j := by
  constructor
  · intro hj
    simpa [pos_Tvee a _ _ (start_lt_mem_graftNodes hj),hj] using a.r_pos
  · intro hj
    by_contra hn
    by_cases h : a.start < j
    · simp [pos_Tvee a _ _ h,hn] at hj
    · simp [TreePrefix.pos_zero_of_not_lt _ _ _ h] at hj

private theorem start_le_of_pos {a : SArc s} {i j : Fin n} (h : 0 < a.Tvee.pos i j) :
    a.start ≤ i := by
  by_contra hne
  have hi : i < a.start := lt_of_not_ge hne
  have hil : i ∉ a.left := fun h => (mem_positiveInterior.mp (mem_left.mp h).1).1.not_ge hi.le
  by_cases hij : i < j
  · simp [pos_Tvee a _ _ hij,hi.ne,hil] at h
  · simp [TreePrefix.pos_zero_of_not_lt _ _ _ hij] at h

theorem Tvee_injective : Function.Injective (Tvee (s := s)) := by
  intro a b e
  have hab : a.start ≤ b.start := start_le_of_pos
    (by rw [e,Tvee_pos_start_finish]; exact b.r_pos : 0 < a.Tvee.pos b.start b.finish)
  have hba : b.start ≤ a.start := start_le_of_pos
    (by rw [← e,Tvee_pos_start_finish]; exact a.r_pos : 0 < b.Tvee.pos a.start a.finish)
  have hi := hab.antisymm hba
  have hG : a.graftNodes = b.graftNodes := by
    ext j
    rw [mem_graftNodes_iff_pos,mem_graftNodes_iff_pos,e,hi]
  have finish_ge (a : SArc s) (j : Fin n) (h : j ∈ a.graftNodes) : j ≤ a.finish := by
    rcases Finset.mem_insert.mp h with rfl | h
    · exact le_rfl
    · exact (mem_positiveInterior.mp (a.right_subset h)).2.1.le
  have hfa : a.finish ∈ a.graftNodes := Finset.mem_insert_self _ _
  have hfb : b.finish ∈ b.graftNodes := Finset.mem_insert_self _ _
  have hf := (finish_ge b _ (hG ▸ hfa)).antisymm (finish_ge a _ (hG.symm ▸ hfb))
  have hr : a.r = b.r := by
    rw [← Tvee_pos_start_finish a,← Tvee_pos_start_finish b,e,hi,hf]
  have hRight : a.right = b.right := by
    ext i
    by_cases h : i = a.finish
    · subst i
      exact iff_of_false (fun h => lt_irrefl _ (mem_positiveInterior.mp (a.right_subset h)).2.1)
        (fun h => (mem_positiveInterior.mp (b.right_subset h)).2.1.not_ge hf.ge)
    · have h' : i ≠ b.finish := fun e => h (e.trans hf.symm)
      have he := Finset.ext_iff.mp hG i
      simpa [graftNodes,h,h'] using he
  exact eq_of_key_finish_right ⟨hi,hr⟩ hf hRight

#print axioms Tvee_injective

#print axioms pos_Tvee
#print axioms Tvee_has_lower_cover

end SArc

end Permutree
```

### `CombIrreducibles.lean`

```lean
import CombCoordinates
import Mathlib.Data.Finset.Lattice.Fold

namespace Permutree

open TreePrefix

variable {n : ℕ} {s : Fin n → ℕ}

namespace SArc

theorem Tvee_le_of_thresholds (a : SArc s) (T : STree s)
    (hA : ∀ j ∈ a.graftNodes, a.r ≤ T.pos a.start j)
    (hB : ∀ i ∈ a.left, T.pos a.start i < a.r) : a.Tvee ≤ T := by
  intro i j
  change a.Tvee.pos i j ≤ T.pos i j
  by_cases hij : i < j
  · rw [pos_Tvee a i j hij]
    by_cases hj : j ∈ a.graftNodes
    · rw [ite_eq_left hj]
      by_cases hi : i = a.start
      · subst i
        simpa using hA j hj
      · rw [ite_eq_right hi]
        by_cases hb : i ∈ a.left
        · rw [ite_eq_left hb]
          have hai := (mem_positiveInterior.mp (mem_left.mp hb).1).1
          by_contra hne
          have hlt : T.pos i j < s i := lt_of_not_ge hne
          have := (T.toPosition.planar hai hij hlt)
          exact (not_le_of_gt (hB i hb)) ((hA j hj).trans this)
        · simp [hb]
    · simp [hj]
  · simp [pos_zero_of_not_lt a.Tvee i j hij]

theorem Tvee_eq_of_le_of_coord (a : SArc s) (T : STree s) (hT : T ≤ a.Tvee)
    (h : T.pos a.start a.finish = a.r) : T = a.Tvee := by
  refine hT.antisymm (Tvee_le_of_thresholds a T ?_ ?_)
  · intro j hj
    rcases Finset.mem_insert.mp hj with hfin | hr
    · simp [hfin,h]
    have hd := mem_positiveInterior.mp (a.right_subset hr)
    have hzero : a.Tvee.pos j a.finish = 0 := by
      have hn : j ∉ a.left := fun hn => (mem_left.mp hn).2 hr
      simp [pos_Tvee a j a.finish hd.2.1,graftNodes,hd.1.ne.symm,hn]
    have hb : T.pos j a.finish ≤ a.Tvee.pos j a.finish := hT j a.finish
    rw [hzero] at hb
    rw [← h]
    exact T.toPosition.planar hd.1 hd.2.1 (lt_of_le_of_lt hb (Nat.pos_of_ne_zero hd.2.2))
  · intro i hi
    have hd := mem_positiveInterior.mp (mem_left.mp hi).1
    have hG : i ∉ a.graftNodes := by
      simpa [graftNodes,hd.2.1.ne] using (mem_left.mp hi).2
    have hle : T.pos a.start i ≤ a.Tvee.pos a.start i := hT a.start i
    rw [pos_Tvee a a.start i hd.1,ite_eq_right hG] at hle
    exact hle.trans_lt a.r_pos

private theorem leaf_row_zero (a : SArc s) (j : Fin n) (hj : j ∈ a.graftNodes) (k : Fin n) :
    a.Tvee.pos j k = 0 := by
  by_cases h : j < k
  · have hne := (start_lt_mem_graftNodes hj).ne.symm
    have hleft : j ∉ a.left := by
      intro hleft
      rcases Finset.mem_insert.mp hj with hfin | hr
      · exact (mem_positiveInterior.mp (mem_left.mp hleft).1).2.1.ne hfin
      · exact (mem_left.mp hleft).2 hr
    simp [pos_Tvee a _ _ h,hne,hleft]
  · exact pos_zero_of_not_lt _ _ _ h

theorem sup_coord_eq_max_below (a : SArc s) {U V : STree s} (hU : U ≤ a.Tvee) (hV : V ≤ a.Tvee) :
    (U ⊔ V).pos a.start a.finish =
      max (U.pos a.start a.finish) (V.pos a.start a.finish) := by
  let p (i j : Fin n) := max (U.pos i j) (V.pos i j)
  have pLe (i j : Fin n) : p i j ≤ a.Tvee.pos i j := max_le (hU _ _) (hV _ _)
  have hjoin : STree.toPosition (U ⊔ V) = SPosition.join U.toPosition V.toPosition := by
    exact STree.positionEquiv.apply_symm_apply _
  change (STree.toPosition (U ⊔ V)).pos a.start a.finish = p a.start a.finish
  rw [hjoin]
  change SPosition.closure s p a.start a.finish = _
  refine le_antisymm ?_ (SPosition.walk_le_closure ((pLe _ _).trans (a.Tvee.pos_bound _ _))
    (.single a.start_lt_finish le_rfl))
  by_contra hn
  have hlt := lt_of_not_ge hn
  have hw := SPosition.walk_of_le_closure (Nat.zero_lt_succ _) (Nat.succ_le_of_lt hlt)
  have noTail {j k : Fin n} (hPos : 0 < a.Tvee.pos a.start j)
      (tail : SPosition.Walk p j 1 k) : False := by
    have hG := (mem_graftNodes_iff_pos a j).mpr hPos
    cases tail with
    | single _ htail =>
      have hp := htail.trans (pLe _ _)
      rw [leaf_row_zero a j hG] at hp
      omega
    | cons _ htail _ =>
      have hp := htail.trans (pLe _ _)
      rw [leaf_row_zero a j hG] at hp
      omega
  cases hw with
  | single _ hle => exact Nat.not_succ_le_self _ hle
  | cons _ hr tail =>
    exact noTail ((Nat.zero_lt_succ _).trans_le (hr.trans (pLe _ _))) tail

theorem sup_lt_Tvee (a : SArc s) {U V : STree s} (hU : U < a.Tvee) (hV : V < a.Tvee) :
    U ⊔ V < a.Tvee := by
  refine lt_of_le_of_ne (sup_le hU.le hV.le) ?_
  intro he
  have coord_lt (W : STree s) (hW : W < a.Tvee) : W.pos a.start a.finish < a.r := by
    have h : W.pos a.start a.finish ≤ a.Tvee.pos a.start a.finish := hW.le a.start a.finish
    rw [Tvee_pos_start_finish] at h
    exact lt_of_le_of_ne h (fun h => hW.ne (Tvee_eq_of_le_of_coord a W hW.le h))
  have hc := max_lt (coord_lt U hU) (coord_lt V hV)
  rw [← sup_coord_eq_max_below a hU.le hV.le,he,Tvee_pos_start_finish] at hc
  exact (lt_irrefl _ hc)

theorem Tvee_unique_lower_cover (a : SArc s) : ∃! x : STree s, x ⋖ a.Tvee := by
  obtain ⟨x,hx⟩ := Tvee_has_lower_cover a
  refine ⟨x,hx,fun y hy => ?_⟩
  have hxy := sup_lt_Tvee a hx.lt hy.lt
  have eqx : x ⊔ y = x := (hx.eq_or_eq le_sup_left hxy.le).resolve_right hxy.ne
  have eqy : x ⊔ y = y := (hy.eq_or_eq le_sup_right hxy.le).resolve_right hxy.ne
  exact eqy.symm.trans eqx

/-- Below any tree, every positive coordinate threshold is witnessed
by a join comb with the same start, finish and threshold. -/
def witness (T : STree s) (i j : Fin n) (hij : i < j)
    (r : ℕ) (hr : 0 < r) (hb : r ≤ T.pos i j) : SArc s where
  start := i
  finish := j
  right := (positiveInterior s i j).filter fun h => r ≤ T.pos i h
  label := ⟨r - 1, by have := hb.trans (T.pos_bound i j); omega⟩
  start_lt_finish := hij
  right_subset := fun _ h => (Finset.mem_filter.mp h).1

theorem witness_r (T : STree s) {i j : Fin n} {hij : i < j}
    {r : ℕ} {hr : 0 < r} {hb : r ≤ T.pos i j} :
    (witness T i j hij r hr hb).r = r := by
  change r - 1 + 1 = r
  omega

theorem witness_le (T : STree s) (i j : Fin n) (hij : i < j)
    (r : ℕ) (hr : 0 < r) (hb : r ≤ T.pos i j) : (witness T i j hij r hr hb).Tvee ≤ T := by
  let a := witness T i j hij r hr hb
  change a.Tvee ≤ T
  have h : a.r = r := witness_r T
  apply Tvee_le_of_thresholds
  · intro k hk
    change a.r ≤ T.pos i k
    rw [h]
    rcases Finset.mem_insert.mp hk with hf | hA
    · exact (show k = j from hf).symm ▸ hb
    · exact (Finset.mem_filter.mp hA).2
  · intro k hk
    change T.pos i k < a.r
    rw [h]
    exact lt_of_not_ge fun hl => (mem_left.mp hk).2 (Finset.mem_filter.mpr ⟨(mem_left.mp hk).1,hl⟩)

end SArc

namespace STree

open SArc

noncomputable def combsBelow (T : STree s) : Finset (SArc s) := by
  classical
  exact Finset.univ.filter (fun a : SArc s => a.Tvee ≤ T)

@[simp] theorem mem_combsBelow {T : STree s} {a : SArc s} : a ∈ combsBelow T ↔ a.Tvee ≤ T := by
  classical
  simp [combsBelow]

/-- The combs below T join to T. This holds even when there are unary nodes. -/
theorem sup_combs_below (T : STree s) : (combsBelow T).sup SArc.Tvee = T := by
  refine (Finset.sup_le fun a ha => mem_combsBelow.mp ha).antisymm ?_
  intro i j
  change T.pos i j ≤ ((combsBelow T).sup SArc.Tvee).pos i j
  by_cases hr : 0 < T.pos i j
  · have hij : i < j := by
      by_contra h
      rw [pos_zero_of_not_lt T _ _ h] at hr
      omega
    let a := witness T i j hij (T.pos i j) hr le_rfl
    have hA : a ∈ combsBelow T := mem_combsBelow.mpr (witness_le _ _ _ _ _ _ _)
    have hle := Finset.le_sup (f := SArc.Tvee) hA
    have hc : a.Tvee.pos i j = T.pos i j := (Tvee_pos_start_finish a).trans (witness_r T)
    rw [← hc]
    exact hle i j
  · have hz := Nat.eq_zero_of_not_pos hr
    rw [hz]
    exact Nat.zero_le _

theorem eq_Tvee_of_unique_lower_cover {T : STree s} (h : ∃! x : STree s, x ⋖ T) :
    ∃ a : SArc s, a.Tvee = T := by
  classical
  obtain ⟨x,hx,hu⟩ := h
  by_contra hn
  push Not at hn
  have hle : (combsBelow T).sup SArc.Tvee ≤ x := Finset.sup_le fun a ha => by
    obtain ⟨y,hy,hyt⟩ := exists_le_covBy_of_lt (lt_of_le_of_ne (mem_combsBelow.mp ha) (hn a))
    exact (hu _ hyt) ▸ hy
  rw [sup_combs_below T] at hle
  exact (not_le_of_gt hx.lt) hle

/-- Proposition 51, join version, for the grafted comb map. -/
theorem Tvee_bijective_irreducibles :
    Function.Bijective (fun a : SArc s => (⟨a.Tvee, a.Tvee_unique_lower_cover⟩ :
      {T : STree s // ∃! x : STree s, x ⋖ T})) := by
  refine ⟨fun a b e => SArc.Tvee_injective (congrArg Subtype.val e),?_⟩
  intro T
  obtain ⟨a,ha⟩ := eq_Tvee_of_unique_lower_cover T.property
  exact ⟨a,Subtype.ext ha⟩

#print axioms Tvee_bijective_irreducibles
#print axioms sup_combs_below

end STree

end Permutree
```

### `STreeSemidistributive.lean`

```lean
import CombIrreducibles
import CanonicalFinite
import Mathlib.Data.Nat.Find

namespace Permutree

open SArc TreePrefix

variable {n : ℕ} {s : Fin n → ℕ}

namespace STree

/-- If an interval has the shortest span on which Y differs from T,
the join of Y with any U below T cannot add that coordinate via a longer walk. -/
theorem sup_coord_eq_max_shortest {Y U T : STree s} (hY : Y ≤ T) (hU : U ≤ T)
    {i j : Fin n} (hij : i < j)
    (hshort : ∀ a b : Fin n, a < b → b.val - a.val < j.val - i.val →
      Y.pos a b = T.pos a b) :
    (Y ⊔ U).pos i j = max (Y.pos i j) (U.pos i j) := by
  let p (a b : Fin n) := max (Y.pos a b) (U.pos a b)
  have pLe (a b : Fin n) : p a b ≤ T.pos a b := max_le (hY a b) (hU a b)
  have hjoin : STree.toPosition (Y ⊔ U) = SPosition.join Y.toPosition U.toPosition :=
    STree.positionEquiv.apply_symm_apply _
  change (STree.toPosition (Y ⊔ U)).pos i j = p i j
  rw [hjoin]
  change SPosition.closure s p i j = p i j
  apply le_antisymm _ (SPosition.walk_le_closure ((pLe _ _).trans (T.pos_bound _ _))
    (.single hij le_rfl))
  by_contra hn
  have hlt := lt_of_not_ge hn
  have w := SPosition.walk_of_le_closure (Nat.zero_lt_succ _) (Nat.succ_le_of_lt hlt)
  have no_tail {k : Fin n} (hik : i < k) (hr : p i j + 1 ≤ p i k)
      (tail : SPosition.Walk p k 1 j) : False := by
    have hkj := tail.increasing
    have hshort₁ := hshort i k hik (by omega)
    have hshort₂ := hshort k j hkj (by omega)
    have hr' := hr.trans (pLe i k)
    have htail := tail.le_of_le_pos (z := T.toPosition) pLe
    change 1 ≤ T.pos k j at htail
    rw [← hshort₁] at hr'
    rw [← hshort₂] at htail
    have hl := Y.toPosition.transitive hik hkj htail
    exact Nat.not_succ_le_self _ ((hr'.trans hl).trans (le_max_left _ _))
  cases w with
  | single _ h => exact Nat.not_succ_le_self _ h
  | cons hik hr tail => exact no_tail hik hr tail

private theorem exists_shortest_difference {Y T : STree s} (hYT : Y < T) :
    ∃ i j : Fin n, i < j ∧ Y.pos i j < T.pos i j ∧
      ∀ a b : Fin n, a < b → b.val - a.val < j.val - i.val → Y.pos a b = T.pos a b := by
  classical
  let P (m : ℕ) := ∃ i j : Fin n, i < j ∧ m = j.val - i.val ∧ Y.pos i j < T.pos i j
  have hE : ∃ m, P m := by
    by_contra hn
    apply hYT.ne
    apply STree.toPosition_injective
    apply SPosition.ext
    funext a b
    change Y.pos a b = T.pos a b
    by_cases hab : a < b
    · exact (hYT.le a b).antisymm (le_of_not_gt (fun h => hn ⟨_,a,b,hab,rfl,h⟩))
    · rw [pos_zero_of_not_lt _ _ _ hab,pos_zero_of_not_lt _ _ _ hab]
  obtain ⟨i,j,hij,hspan,hd⟩ := Nat.find_spec hE
  refine ⟨i,j,hij,hd,fun a b hab hlt => ?_⟩
  apply (hYT.le a b).antisymm
  apply le_of_not_gt
  intro he
  apply Nat.find_min hE (show b.val - a.val < Nat.find hE from hspan.symm ▸ hlt)
  exact ⟨a,b,hab,rfl,he⟩

/-- The least witness for a cover is a comb at a shortest differing interval. -/
theorem cover_least_comb {Y T : STree s} (hcover : Y ⋖ T) :
    ∃ a : SArc s, Y ⊔ a.Tvee = T ∧
      ∀ U : STree s, Y ⊔ U = T → a.Tvee ≤ U := by
  obtain ⟨i,j,hij,hlt,hshort⟩ := exists_shortest_difference hcover.lt
  let r := T.pos i j
  have hr : 0 < r := (Nat.zero_le _).trans_lt hlt
  let a := witness T i j hij r hr le_rfl
  have ha : a.Tvee ≤ T := witness_le T i j hij r hr le_rfl
  have har : a.r = r := witness_r T
  have hcoord : a.Tvee.pos i j = r := (Tvee_pos_start_finish a).trans har
  have hf : ¬ a.Tvee ≤ Y := by
    intro he
    have hd : a.Tvee.pos i j ≤ Y.pos i j := he i j
    rw [hcoord] at hd
    exact (not_le_of_gt hlt) hd
  refine ⟨a, (hcover.eq_or_eq le_sup_left (sup_le hcover.le ha)).resolve_left
    (fun he => hf (le_sup_right.trans he.le)), ?_⟩
  intro U hU
  have hu : U ≤ T := le_sup_right.trans hU.le
  have hf := sup_coord_eq_max_shortest hcover.le hu hij hshort
  rw [hU] at hf
  have hEq : U.pos i j = r := by
    change r = _ at hf
    omega
  apply Tvee_le_of_thresholds
  · intro k hk
    rw [har]
    rcases Finset.mem_insert.mp hk with hk | hk
    · change k = j at hk
      change r ≤ U.pos i k
      rw [hk,hEq]
    · have hd := mem_positiveInterior.mp (a.right_subset hk)
      change i < k ∧ k < j ∧ s k ≠ 0 at hd
      have hTk : r ≤ T.pos i k := (Finset.mem_filter.mp hk).2
      have hz : T.pos k j = 0 := by
        by_contra hne
        have hk' := hshort k j hd.2.1 (by omega)
        have hi' := hshort i k hd.1 (by omega)
        have hpos : 0 < Y.pos k j := hk'.symm ▸ Nat.pos_of_ne_zero hne
        have hy := Y.toPosition.transitive hd.1 hd.2.1 hpos
        change Y.pos i k ≤ Y.pos i j at hy
        rw [hi'] at hy
        exact (not_le_of_gt hlt) (hTk.trans hy)
      have hUk : U.pos k j ≤ T.pos k j := hu k j
      rw [hz] at hUk
      have hf := U.toPosition.planar hd.1 hd.2.1 (hUk.trans_lt (Nat.pos_of_ne_zero hd.2.2))
      exact hEq.ge.trans hf
  · intro k hk
    have hd := mem_left.mp hk
    have hTk : T.pos i k < r := lt_of_not_ge fun he => hd.2 (Finset.mem_filter.mpr ⟨hd.1,he⟩)
    rw [har]
    exact (show U.pos i k ≤ T.pos i k from hu i k).trans_lt hTk

theorem joinSemidistributive : JoinSemidistributive (STree s) := by
  intro x y z h
  let T := x ⊔ y
  have hle : x ⊔ (y ⊓ z) ≤ T := sup_le_sup_left inf_le_left x
  apply hle.antisymm
  by_contra hn
  obtain ⟨Y,hY,hYT⟩ := exists_le_covBy_of_lt (lt_of_le_not_ge hle hn)
  obtain ⟨a,ha,hleast⟩ := cover_least_comb hYT
  have hx : x ≤ Y := le_sup_left.trans hY
  have hy : Y ⊔ y = T := le_antisymm (sup_le hYT.le le_sup_right)
    (sup_le_sup_right hx y)
  have hz : Y ⊔ z = T := le_antisymm (sup_le hYT.le (le_sup_right.trans h.symm.le))
    (h.le.trans (sup_le_sup_right hx z))
  have ham := le_inf (hleast y hy) (hleast z hz)
  have hb : a.Tvee ≤ Y := ham.trans (le_sup_right.trans hY)
  exact hYT.ne ((sup_eq_left.mpr hb).symm.trans ha)

attribute [local instance] Classical.decEq

/-- Each lower cover contributes one distinct canonical joinand. -/
theorem canonical_cover_combs (T : STree s) :
    ∃ chart : {Y : STree s // Y ⋖ T} ↪ SArc s,
      (∀ Y, Y.val ⊔ (chart Y).Tvee = T ∧
        ∀ U : STree s, Y.val ⊔ U = T → (chart Y).Tvee ≤ U) ∧
      IsCanonicalJoinRep ((@Finset.univ _ (Fintype.ofFinite _)).image (fun Y => (chart Y).Tvee)) T := by
  classical
  let J (Y : {Y : STree s // Y ⋖ T}) := (cover_least_comb Y.property).choose
  let _ : Fintype {Y : STree s // Y ⋖ T} := Fintype.ofFinite _
  have hJ (Y : {Y : STree s // Y ⋖ T}) :
      Y.val ⊔ (J Y).Tvee = T ∧ ∀ U : STree s, Y.val ⊔ U = T → (J Y).Tvee ≤ U :=
    (cover_least_comb Y.property).choose_spec
  have hnot (Y : {Y : STree s // Y ⋖ T}) : ¬ (J Y).Tvee ≤ Y.val := by
    intro h
    exact Y.property.ne ((sup_eq_left.mpr h).symm.trans (hJ Y).1)
  have hcross (Y Z : {Y : STree s // Y ⋖ T}) (hne : Y ≠ Z) : (J Y).Tvee ≤ Z.val := by
    apply (hJ Y).2
    apply (Y.property.eq_or_eq le_sup_left (sup_le Y.property.le Z.property.le)).resolve_left
    intro h
    have hle : Z.val ≤ Y.val := le_sup_right.trans h.le
    have hlt : Z.val < Y.val := lt_of_le_of_ne hle (fun e => hne (Subtype.ext e.symm))
    exact Z.property.2 hlt Y.property.lt
  have hInj : Function.Injective (fun Y => (J Y).Tvee) := by
    intro Y Z he
    by_contra hne
    change (J Y).Tvee = (J Z).Tvee at he
    exact hnot Z (he ▸ hcross Y Z hne)
  have hJinj : Function.Injective J := fun _ _ e => hInj (congrArg SArc.Tvee e)
  refine ⟨⟨J,hJinj⟩,hJ,?_⟩
  let X := Finset.univ.image (fun Y => (J Y).Tvee)
  have hX {j : STree s} : j ∈ X ↔ ∃ Y, (J Y).Tvee = j := by simp [X]
  have hle : X.sup id ≤ T := Finset.sup_le fun j hj => by
    obtain ⟨Y,rfl⟩ := hX.mp hj
    exact le_sup_right.trans (hJ Y).1.le
  change IsCanonicalJoinRep X T
  refine ⟨hle.antisymm ?_, ?_, ?_⟩
  · by_contra h
    obtain ⟨Y,hY,hYT⟩ := exists_le_covBy_of_lt (lt_of_le_not_ge hle h)
    exact hnot ⟨Y,hYT⟩ ((Finset.le_sup (f := id) (hX.mpr ⟨⟨Y,hYT⟩,rfl⟩)).trans hY)
  · intro j hj hj'
    obtain ⟨Y,rfl⟩ := hX.mp hj
    apply hnot Y (hj'.trans (Finset.sup_le fun k hk => ?_))
    obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hk
    obtain ⟨Z,rfl⟩ := hX.mp hm
    exact hcross Z Y (fun e => hne (congrArg (fun Y => (J Y).Tvee) e))
  · intro R hR j hj
    obtain ⟨Y,rfl⟩ := hX.mp hj
    have hex : ∃ U ∈ R, ¬ U ≤ Y.val := by
      by_contra hn
      push Not at hn
      have hr : R.sup id ≤ Y.val := Finset.sup_le hn
      rw [hR] at hr
      exact (not_le_of_gt Y.property.lt) hr
    obtain ⟨U,hU,hn⟩ := hex
    have hu : U ≤ T := hR ▸ Finset.le_sup (f := id) hU
    have he : Y.val ⊔ U = T :=
      (Y.property.eq_or_eq le_sup_left (sup_le Y.property.le hu)).resolve_left
        (fun he => hn (le_sup_right.trans he.le))
    exact ⟨U,hU,(hJ Y).2 U he⟩

/-- Left/right reflection on the position vectors reverses the tree order. -/
noncomputable def reflect (T : STree s) : STree s :=
  positionEquiv.symm T.toPosition.mirror

@[simp] theorem toPosition_reflect (T : STree s) :
    (reflect T).toPosition = T.toPosition.mirror :=
  positionEquiv.apply_symm_apply _

@[simp] theorem reflect_reflect (T : STree s) : reflect (reflect T) = T := by
  apply toPosition_injective
  rw [toPosition_reflect,toPosition_reflect,SPosition.mirror_mirror]

theorem reflect_antitone : Antitone (reflect (s := s)) := by
  intro T U h
  change (reflect U).toPosition ≤ (reflect T).toPosition
  rw [toPosition_reflect,toPosition_reflect]
  exact SPosition.mirror_antitone h

@[simp] theorem reflect_sup (T U : STree s) : reflect (T ⊔ U) = reflect T ⊓ reflect U := by
  apply le_antisymm
  · exact le_inf (reflect_antitone le_sup_left) (reflect_antitone le_sup_right)
  · have h₁ : T ≤ reflect (reflect T ⊓ reflect U) := by
      simpa using (reflect_antitone (inf_le_left (a := reflect T) (b := reflect U)))
    have h₂ : U ≤ reflect (reflect T ⊓ reflect U) := by
      simpa using (reflect_antitone (inf_le_right (a := reflect T) (b := reflect U)))
    simpa using reflect_antitone (sup_le h₁ h₂)

@[simp] theorem reflect_inf (T U : STree s) : reflect (T ⊓ U) = reflect T ⊔ reflect U := by
  have h := congrArg reflect (reflect_sup (reflect T) (reflect U))
  simpa only [reflect_reflect] using h.symm

theorem meetSemidistributive {x y z : STree s} (h : x ⊓ y = x ⊓ z) :
    x ⊓ (y ⊔ z) = x ⊓ y := by
  have he : reflect x ⊔ reflect y = reflect x ⊔ reflect z := by
    simpa only [reflect_inf] using congrArg reflect h
  have hf := joinSemidistributive (reflect x) (reflect y) (reflect z) he
  simpa only [reflect_sup,reflect_inf,reflect_reflect] using congrArg reflect hf

#print axioms canonical_cover_combs
#print axioms cover_least_comb
#print axioms joinSemidistributive
#print axioms meetSemidistributive

end STree

end Permutree
```

### `CanonicalPairwise.lean`

```lean
import CanonicalFinite

namespace Permutree

variable {L : Type*} [Lattice L] [OrderBot L]

/-- A lower witness and its corresponding upper bound for a join irreducible. -/
structure JoinBound (j : L) where
  lower : L
  upper : L
  lower_lt : lower < j
  greatest_below : ∀ y, y < j → y ≤ lower
  lower_le_upper : lower ≤ upper
  not_le_upper : ¬ j ≤ upper
  greatest_avoiding : ∀ y, lower ≤ y → ¬ j ≤ y → y ≤ upper

omit [OrderBot L] in
theorem JoinBound.upper_spec {j : L} (b : JoinBound j) {y : L} (h : b.lower ≤ y) :
    y ≤ b.upper ↔ ¬ j ≤ y :=
  ⟨fun hy h' => b.not_le_upper (h'.trans hy), b.greatest_avoiding y h⟩

/-- Pairwise comparisons with the upper bounds characterize the canonical
faces carried by join irreducibles. -/
theorem canonical_iff_pairwise_join_bounds [DecidableEq L]
    (existsCanonical : ∀ x : L, ∃ C : Finset L, IsCanonicalJoinRep C x)
    (X : Finset L) (bounds : ∀ j ∈ X, JoinBound j) :
    IsCanonicalJoinRep X (X.sup id) ↔
      ∀ i ∈ X, ∀ j (hj : j ∈ X), i ≠ j → i ≤ (bounds j hj).upper := by
  constructor
  · intro h i hi j hj hne
    let b := bounds j hj
    let Y := insert b.lower (X.erase j)
    have hlo : b.lower ≤ Y.sup id := Finset.le_sup (f := id) (Finset.mem_insert_self _ _)
    have hAvoid : ¬ j ≤ Y.sup id := by
      intro hjY
      have eq : Y.sup id = X.sup id := by
        apply le_antisymm
        · apply Finset.sup_le
          intro a ha
          rcases Finset.mem_insert.mp ha with rfl | ha
          · exact b.lower_lt.le.trans (Finset.le_sup (f := id) hj)
          · exact Finset.le_sup (f := id) (Finset.mem_of_mem_erase ha)
        · apply Finset.sup_le
          intro a ha
          by_cases e : a = j
          · exact e.symm ▸ hjY
          · exact Finset.le_sup (f := id) (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨e,ha⟩))
      obtain ⟨a,ha,hja⟩ := h.2.2 Y eq j hj
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact (not_le_of_gt b.lower_lt) hja
      · exact (Finset.mem_erase.mp ha).1 (h.eq_of_le hj (Finset.mem_of_mem_erase ha) hja).symm
    exact (Finset.le_sup (f := id) (Finset.mem_insert_of_mem
      (Finset.mem_erase.mpr ⟨hne,hi⟩))).trans ((b.upper_spec hlo).mpr hAvoid)
  · intro h
    obtain ⟨C,hC⟩ := existsCanonical (X.sup id)
    have hxc : X ⊆ C := by
      intro j hj
      let b := bounds j hj
      have hex : ∃ a ∈ C, ¬ a ≤ b.upper := by
        by_contra hn
        push Not at hn
        have hle : C.sup id ≤ b.upper := Finset.sup_le hn
        exact b.not_le_upper ((Finset.le_sup (f := id) hj).trans (hC.1 ▸ hle))
      obtain ⟨a,ha,hn⟩ := hex
      obtain ⟨i,hi,hai⟩ := hC.2.2 X rfl a ha
      have e : i = j := by
        by_contra he
        exact hn (hai.trans (h i hi j hj he))
      subst i
      have he : a = j := by
        by_contra hne
        exact hn ((b.greatest_below a (lt_of_le_of_ne hai hne)).trans b.lower_le_upper)
      exact he ▸ ha
    have hcx : C ⊆ X := by
      intro a ha
      obtain ⟨i,hi,hai⟩ := hC.2.2 X rfl a ha
      exact (hC.eq_of_le ha (hxc hi) hai).symm ▸ hi
    have e := Finset.Subset.antisymm hxc hcx
    rw [← e] at hC
    exact hC

#print axioms canonical_iff_pairwise_join_bounds

end Permutree
```

### `CombBounds.lean`

```lean
import STreeSemidistributive
import CanonicalPairwise

namespace Permutree.SArc

open TreePrefix

variable {n : ℕ} {s : Fin n → ℕ}

private theorem not_mem_graft_of_left {a : SArc s} {i : Fin n} (h : i ∈ a.left) :
    i ∉ a.graftNodes := by
  have hl := mem_left.mp h
  simpa [graftNodes,(mem_positiveInterior.mp hl.1).2.1.ne] using hl.2

private theorem mem_graft_le_finish {a : SArc s} {i : Fin n} (h : i ∈ a.graftNodes) :
    i ≤ a.finish := by
  rcases Finset.mem_insert.mp h with e | h
  · exact e.le
  · exact (mem_positiveInterior.mp (a.right_subset h)).2.1.le

private def lowerCoords (a : SArc s) (i j : Fin n) : ℕ :=
  if i = a.start ∧ j = a.finish then a.r - 1 else a.Tvee.pos i j

private theorem lowerCoords_le (a : SArc s) (i j : Fin n) :
    a.lowerCoords i j ≤ a.Tvee.pos i j := by
  by_cases h : i = a.start ∧ j = a.finish
  · obtain ⟨rfl,rfl⟩ := h
    simp [lowerCoords,Tvee_pos_start_finish]
  · simp [lowerCoords,h]

private def lowerPosition (a : SArc s) : SPosition s where
  pos := a.lowerCoords
  bound i j := (a.lowerCoords_le i j).trans (a.Tvee.pos_bound i j)
  zero_of_not_lt i j h := by
    have e : ¬(i = a.start ∧ j = a.finish) := fun ⟨hi,hj⟩ => h (hi.symm ▸ hj.symm ▸ a.start_lt_finish)
    simp [lowerCoords,e,pos_zero_of_not_lt _ _ _ h]
  transitive := by
    intro i j k hij hjk hp
    by_cases h : i = a.start ∧ k = a.finish
    · obtain ⟨rfl,rfl⟩ := h
      have hs : j ≠ a.start := hij.ne.symm
      have hp' := hp.trans_le (a.lowerCoords_le j a.finish)
      have hl : j ∈ a.left := by
        by_contra hnl
        simp [pos_Tvee a j a.finish hjk,graftNodes,hs,hnl] at hp'
      have hz : a.Tvee.pos a.start j = 0 := by
        simp [pos_Tvee a a.start j hij,not_mem_graft_of_left hl]
      have hd := a.lowerCoords_le a.start j
      rw [hz] at hd
      exact hd.trans (Nat.zero_le _)
    · exact (a.lowerCoords_le i j).trans (by
        rw [lowerCoords,ite_eq_right h]
        exact a.Tvee.toPosition.transitive hij hjk (hp.trans_le (a.lowerCoords_le j k)))
  planar := by
    intro i j k hij hjk hs
    by_cases h : i = a.start ∧ j = a.finish
    · obtain ⟨rfl,rfl⟩ := h
      have hG : k ∉ a.graftNodes := fun hG => hjk.not_ge (mem_graft_le_finish hG)
      have hx : a.Tvee.pos a.start k = 0 := by
        simp [pos_Tvee a a.start k (hij.trans hjk),hG]
      exact (a.lowerCoords_le _ _).trans (hx ▸ Nat.zero_le _)
    · have hR : a.lowerCoords i j = a.Tvee.pos i j := ite_eq_right h
      rw [hR]
      by_cases he : j = a.start ∧ k = a.finish
      · obtain ⟨rfl,rfl⟩ := he
        have hl : i ∉ a.left := fun h => (mem_positiveInterior.mp (mem_left.mp h).1).1.not_ge hij.le
        have hx : a.Tvee.pos i a.finish = 0 := by
          simp [pos_Tvee a i a.finish (hij.trans hjk),graftNodes,hij.ne,hl]
        exact (a.lowerCoords_le _ _).trans (hx ▸ Nat.zero_le _)
      · rw [lowerCoords,ite_eq_right he] at hs
        exact (a.lowerCoords_le _ _).trans (a.Tvee.toPosition.planar hij hjk hs)

/-- The lower cover of a join comb is obtained by decreasing its endpoint coordinate. -/
noncomputable def lowerTree (a : SArc s) : STree s :=
  STree.positionEquiv.symm a.lowerPosition

theorem pos_lowerTree (a : SArc s) (i j : Fin n) :
    a.lowerTree.pos i j = if i = a.start ∧ j = a.finish then a.r - 1 else a.Tvee.pos i j := by
  change (STree.positionEquiv (STree.positionEquiv.symm _)).pos i j = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem lowerTree_lt (a : SArc s) : a.lowerTree < a.Tvee := by
  refine lt_of_le_of_ne (fun i j => ?_) ?_
  · change a.lowerTree.pos i j ≤ a.Tvee.pos i j
    exact (pos_lowerTree a i j).symm ▸ a.lowerCoords_le i j
  · intro h
    have hp := congrArg (fun T : STree s => T.pos a.start a.finish) h
    change a.lowerTree.pos a.start a.finish = a.Tvee.pos a.start a.finish at hp
    simp [pos_lowerTree,Tvee_pos_start_finish] at hp
    have := a.r_pos
    omega

theorem le_lowerTree_of_lt (a : SArc s) {U : STree s} (hu : U < a.Tvee) : U ≤ a.lowerTree := by
  intro i j
  change U.pos i j ≤ a.lowerTree.pos i j
  rw [pos_lowerTree]
  by_cases h : i = a.start ∧ j = a.finish
  · obtain ⟨rfl,rfl⟩ := h
    simp only [true_and,ite_true]
    have hb : U.pos a.start a.finish ≤ a.r := a.Tvee_pos_start_finish ▸ hu.le _ _
    have he : U.pos a.start a.finish ≠ a.r :=
      fun e => hu.ne (Tvee_eq_of_le_of_coord a U hu.le e)
    omega
  · exact ite_eq_right h ▸ hu.le _ _

theorem lowerTree_covBy (a : SArc s) : a.lowerTree ⋖ a.Tvee :=
  ⟨a.lowerTree_lt,fun _ hlt hu => (not_le_of_gt hlt) (a.le_lowerTree_of_lt hu)⟩

private def opposite (a : SArc s) : SArc s where
  start := a.start
  finish := a.finish
  right := a.left
  label := ⟨s a.start - a.r, by have := a.r_pos; have := a.r_le; omega⟩
  start_lt_finish := a.start_lt_finish
  right_subset := fun _ h => (mem_left.mp h).1

private theorem opposite_left (a : SArc s) : a.opposite.left = a.right := by
  ext i
  rw [mem_left]
  change (i ∈ positiveInterior s a.start a.finish ∧ i ∉ a.left) ↔ i ∈ a.right
  simp only [mem_left]
  constructor
  · rintro ⟨h,hn⟩
    by_contra h'
    exact hn ⟨h,h'⟩
  · exact fun h => ⟨a.right_subset h,fun hn => hn.2 h⟩

def meetNodes (a : SArc s) : Finset (Fin n) := insert a.finish a.left

/-- The left-comb counterpart of the join comb, obtained by reflection. -/
noncomputable def kappa (a : SArc s) : STree s := STree.reflect a.opposite.Tvee

theorem pos_kappa (a : SArc s) (i j : Fin n) (h : i < j) :
    a.kappa.pos i j = if j ∈ a.meetNodes then
      if i = a.start then a.r - 1 else if i ∈ a.right then 0 else s i else s i := by
  change (STree.reflect a.opposite.Tvee).toPosition.pos i j = _
  rw [STree.toPosition_reflect]
  change (if i < j then s i - a.opposite.Tvee.pos i j else 0) = _
  rw [ite_eq_left h,pos_Tvee _ _ _ h]
  have hG : a.opposite.graftNodes = a.meetNodes := rfl
  have hI : a.opposite.start = a.start := rfl
  rw [hG,hI,opposite_left]
  by_cases hg : j ∈ a.meetNodes
  · rw [ite_eq_left hg,ite_eq_left hg]
    by_cases hi : i = a.start
    · subst i
      simp only [ite_true]
      change s a.start - (s a.start - a.r + 1) = a.r - 1
      have := a.r_le
      have := a.r_pos
      omega
    · rw [ite_eq_right hi,ite_eq_right hi]
      split <;> simp
  · simp [hg]

private theorem not_le_kappa (a : SArc s) : ¬a.Tvee ≤ a.kappa := by
  intro h
  have hp : a.Tvee.pos a.start a.finish ≤ a.kappa.pos a.start a.finish := h _ _
  rw [Tvee_pos_start_finish,pos_kappa _ _ _ a.start_lt_finish] at hp
  simp [meetNodes] at hp
  have := a.r_pos
  omega

private theorem lower_le_kappa (a : SArc s) : a.lowerTree ≤ a.kappa := by
  intro i j
  change a.lowerTree.pos i j ≤ a.kappa.pos i j
  by_cases hij : i < j
  · rw [pos_kappa _ _ _ hij]
    by_cases hg : j ∈ a.meetNodes
    · rw [ite_eq_left hg]
      by_cases hi : i = a.start
      · subst i
        rw [ite_eq_left rfl,pos_lowerTree]
        rcases Finset.mem_insert.mp hg with e | hl
        · simp [e]
        · have hn := (mem_positiveInterior.mp (mem_left.mp hl).1).2.1.ne
          have hd := not_mem_graft_of_left hl
          simp [hn,pos_Tvee _ _ _ hij,hd]
      · rw [ite_eq_right hi]
        by_cases hr : i ∈ a.right
        · have hn : i ∉ a.left := fun h => (mem_left.mp h).2 hr
          rw [ite_eq_left hr,pos_lowerTree]
          simp [hi,pos_Tvee _ _ _ hij,hn]
        · rw [ite_eq_right hr]
          exact a.lowerTree.pos_bound i j
    · rw [ite_eq_right hg]
      exact a.lowerTree.pos_bound i j
  · simp [pos_zero_of_not_lt _ _ _ hij]

private theorem le_kappa_of_avoids (a : SArc s) (U : STree s) (hl : a.lowerTree ≤ U)
    (hn : ¬ a.Tvee ≤ U) : U ≤ a.kappa := by
  have hfin : U.pos a.start a.finish < a.r := by
    by_contra hne
    apply hn
    intro i j
    change a.Tvee.pos i j ≤ U.pos i j
    by_cases h : i = a.start ∧ j = a.finish
    · obtain ⟨rfl,rfl⟩ := h
      rw [Tvee_pos_start_finish]
      exact le_of_not_gt hne
    · have h' : a.lowerTree.pos i j ≤ U.pos i j := hl i j
      rwa [pos_lowerTree,ite_eq_right h] at h'
  have hsmall (j : Fin n) (hj : j ∈ a.meetNodes) : U.pos a.start j < a.r := by
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hfin
    · obtain ⟨h₁,h₂,hz⟩ := mem_positiveInterior.mp (mem_left.mp hj).1
      have h' : a.lowerTree.pos j a.finish ≤ U.pos j a.finish := hl j a.finish
      have hn := h₁.ne.symm
      rw [pos_lowerTree,ite_eq_right (fun h => hn h.1),
        pos_Tvee _ _ _ h₂,ite_eq_left (show a.finish ∈ a.graftNodes from Finset.mem_insert_self _ _),ite_eq_right hn,ite_eq_left hj] at h'
      exact (U.toPosition.transitive h₁ h₂ ((Nat.pos_of_ne_zero hz).trans_le h')).trans_lt hfin
  intro i j
  change U.pos i j ≤ a.kappa.pos i j
  by_cases hij : i < j
  · rw [pos_kappa _ _ _ hij]
    by_cases hg : j ∈ a.meetNodes
    · rw [ite_eq_left hg]
      by_cases hi : i = a.start
      · subst i
        rw [ite_eq_left rfl]
        have := hsmall j hg
        omega
      · rw [ite_eq_right hi]
        by_cases hr : i ∈ a.right
        · rw [ite_eq_left hr]
          obtain ⟨h₁,h₂,_⟩ := mem_positiveInterior.mp (a.right_subset hr)
          have hp : a.lowerTree.pos a.start i ≤ U.pos a.start i := hl a.start i
          rw [pos_lowerTree,ite_eq_right (fun h => h₂.ne h.2),pos_Tvee _ _ _ h₁,
            ite_eq_left (show i ∈ a.graftNodes from Finset.mem_insert_of_mem hr),ite_eq_left rfl] at hp
          apply Nat.le_of_not_gt
          intro hc
          exact (not_le_of_gt (hsmall j hg)) (hp.trans (U.toPosition.transitive h₁ hij hc))
        · rw [ite_eq_right hr]
          exact U.pos_bound i j
    · rw [ite_eq_right hg]
      exact U.pos_bound i j
  · rw [pos_zero_of_not_lt _ _ _ hij,pos_zero_of_not_lt _ _ _ hij]

/-- For each arc the reflected comb is its greatest avoiding bound. -/
noncomputable def joinBound (a : SArc s) : JoinBound a.Tvee where
  lower := a.lowerTree
  upper := a.kappa
  lower_lt := a.lowerTree_lt
  greatest_below := fun _ h => a.le_lowerTree_of_lt h
  lower_le_upper := lower_le_kappa a
  not_le_upper := not_le_kappa a
  greatest_avoiding := le_kappa_of_avoids a

#print axioms lowerTree_covBy
#print axioms joinBound

end Permutree.SArc
```

### `CombCompatibility.lean`

```lean
import CombBounds

namespace Permutree.SArc

open TreePrefix

variable {n : ℕ} {s : Fin n → ℕ}

private def From (a b : SArc s) (h : Fin n) : Prop :=
  (h = a.start ∨ h ∈ a.left) ∧ (h = b.start ∨ h ∈ b.right) ∧
    ¬(h = a.start ∧ h = b.start ∧ a.r < b.r)

private def To (a b : SArc s) (h : Fin n) : Prop :=
  h ∈ a.graftNodes ∧ h ∈ b.meetNodes

private def Block (a b : SArc s) : Prop :=
  ∃ i j, i < j ∧ From a b i ∧ To a b j

private theorem left_bounds {a : SArc s} {h : Fin n} (hm : h ∈ a.left) :
    a.start < h ∧ h < a.finish ∧ s h ≠ 0 :=
  mem_positiveInterior.mp (mem_left.mp hm).1

private theorem right_bounds {a : SArc s} {h : Fin n} (hm : h ∈ a.right) :
    a.start < h ∧ h < a.finish ∧ s h ≠ 0 :=
  mem_positiveInterior.mp (a.right_subset hm)

private theorem to_bounds {a b : SArc s} {h : Fin n} (hm : To a b h) :
    (a.start < h ∧ h ≤ a.finish) ∧ (b.start < h ∧ h ≤ b.finish) := by
  refine ⟨⟨start_lt_mem_graftNodes hm.1,?_⟩,?_⟩
  · rcases Finset.mem_insert.mp hm.1 with e | h
    · exact e.le
    · exact (right_bounds h).2.1.le
  · rcases Finset.mem_insert.mp hm.2 with e | h
    · exact ⟨e.symm ▸ b.start_lt_finish,e.le⟩
    · exact ⟨(left_bounds h).1,(left_bounds h).2.1.le⟩

private theorem not_block_iff_le (a b : SArc s) : ¬Block a b ↔ a.Tvee ≤ b.kappa := by
  have coord (i j : Fin n) (hij : i < j) :
      ¬(From a b i ∧ To a b j) ↔ a.Tvee.pos i j ≤ b.kappa.pos i j := by
    rw [pos_Tvee _ _ _ hij,pos_kappa _ _ _ hij]
    by_cases h₁ : j ∈ a.graftNodes
    · rw [ite_eq_left h₁]
      by_cases h₂ : j ∈ b.meetNodes
      · rw [ite_eq_left h₂]
        have ht : To a b j := ⟨h₁,h₂⟩
        simp only [ht,and_true]
        by_cases ha : i = a.start
        · rw [ite_eq_left ha]
          by_cases hb : i = b.start
          · rw [ite_eq_left hb]
            have h : a.r ≤ b.r - 1 ↔ a.r < b.r := by
              have := b.r_pos
              omega
            rw [h]
            unfold From
            tauto
          · rw [ite_eq_right hb]
            by_cases hbr : i ∈ b.right
            · rw [ite_eq_left hbr]
              have h : ¬a.r ≤ 0 := Nat.not_le_of_lt a.r_pos
              unfold From
              tauto
            · rw [ite_eq_right hbr]
              have h : a.r ≤ s i := ha.symm ▸ a.r_le
              unfold From
              tauto
        · rw [ite_eq_right ha]
          by_cases hal : i ∈ a.left
          · rw [ite_eq_left hal]
            by_cases hb : i = b.start
            · rw [ite_eq_left hb]
              have h : ¬ s i ≤ b.r - 1 := by
                have hb' : b.r ≤ s i := hb.symm ▸ b.r_le
                have := b.r_pos
                omega
              unfold From
              tauto
            · rw [ite_eq_right hb]
              by_cases hbr : i ∈ b.right
              · rw [ite_eq_left hbr]
                have h : ¬ s i ≤ 0 := Nat.not_le_of_lt (Nat.pos_of_ne_zero (left_bounds hal).2.2)
                unfold From
                tauto
              · rw [ite_eq_right hbr]
                have h : s i ≤ s i := le_rfl
                unfold From
                tauto
          · rw [ite_eq_right hal]
            have hnt : ¬From a b i := fun hh => hh.1.elim ha hal
            exact iff_of_true hnt (Nat.zero_le _)
      · rw [ite_eq_right h₂]
        have hbound := a.Tvee.pos_bound i j
        rw [pos_Tvee _ _ _ hij,ite_eq_left h₁] at hbound
        exact iff_of_true (fun h => h₂ h.2.2) hbound
    · rw [ite_eq_right h₁]
      exact iff_of_true (fun h => h₁ h.2.1) (Nat.zero_le _)
  constructor
  · intro hn i j
    change a.Tvee.pos i j ≤ b.kappa.pos i j
    by_cases hij : i < j
    · exact (coord i j hij).mp (fun h => hn ⟨i,j,hij,h.1,h.2⟩)
    · rw [pos_zero_of_not_lt _ _ _ hij,pos_zero_of_not_lt _ _ _ hij]
  · intro h ⟨i,j,hij,hfrom,hto⟩
    exact (coord i j hij).mpr (h i j) ⟨hfrom,hto⟩

private theorem from_start_of_leftOf {a b : SArc s} (h : a.LeftOf b) :
    ∃ i, From a b i ∧ (i = a.start ∨ i = b.start) := by
  rcases h with h | h | h
  · exact ⟨b.start,⟨Or.inr h.2,Or.inl rfl,fun he => h.1.ne he.1.symm⟩,Or.inr rfl⟩
  · refine ⟨a.start,⟨Or.inl rfl,Or.inl h.1,?_⟩,Or.inl rfl⟩
    exact fun he => lt_asymm h.2 he.2.2
  · exact ⟨a.start,⟨Or.inl rfl,Or.inr h.2,fun he => h.1.ne he.2.1.symm⟩,Or.inl rfl⟩

private theorem from_start_of_sameKey {a b : SArc s} (h : a.SameKey b) :
    ∃ i, From a b i ∧ (i = a.start ∨ i = b.start) :=
  ⟨a.start,⟨Or.inl rfl,Or.inl h.1,fun he => lt_irrefl _ (h.2 ▸ he.2.2)⟩,Or.inl rfl⟩

private theorem from_start_or_to {a b : SArc s} {i : Fin n} (h : From a b i) :
    (a.LeftOf b ∨ a.SameKey b) ∨ To b a i := by
  obtain ⟨ha,hb,hn⟩ := h
  rcases ha with rfl | ha <;> rcases hb with hb | hb
  · apply Or.inl
    rcases lt_trichotomy b.r a.r with hr | hr | hr
    · exact Or.inl (Or.inr (Or.inl ⟨hb,hr⟩))
    · exact Or.inr ⟨hb,hr.symm⟩
    · exact (hn ⟨rfl,hb,hr⟩).elim
  · exact Or.inl (Or.inl (Or.inr (Or.inr ⟨(right_bounds hb).1,hb⟩)))
  · subst i
    exact Or.inl (Or.inl (Or.inl ⟨(left_bounds ha).1,ha⟩))
  · exact Or.inr ⟨Finset.mem_insert_of_mem hb,Finset.mem_insert_of_mem ha⟩

private theorem no_to_of_no_block {a b : SArc s} (hn : ¬Block a b)
    (h : a.LeftOf b ∨ a.SameKey b) : ∀ j, ¬To a b j := by
  obtain ⟨i,hi,hstart⟩ := h.elim from_start_of_leftOf from_start_of_sameKey
  intro j hj
  have bound := to_bounds hj
  exact hn ⟨i,j,hstart.elim (fun e => e.symm ▸ bound.1.1) (fun e => e.symm ▸ bound.2.1),hi,hj⟩

private theorem no_blocks_of_leftOf {a b : SArc s} (h : a.LeftOf b)
    (hn : ∀ i, ¬To a b i) : ¬Block a b ∧ ¬Block b a := by
  refine ⟨fun ⟨_,j,_,_,hj⟩ => hn j hj, ?_⟩
  rintro ⟨i,_,_,hi,_⟩
  rcases from_start_or_to hi with (hl | hk) | ht
  · exact leftOf_exclusive h hl
  · exact not_sameKey_of_leftOf h ⟨hk.1.symm,hk.2.symm⟩
  · exact hn i ht

private theorem leftSide_of_interior_not_right {a : SArc s} {i : Fin n}
    (hi : i ∈ positiveInterior s a.start a.finish) (hn : i ∉ a.right) :
    i ∈ a.left := mem_left.mpr ⟨hi,hn⟩

private theorem no_to_iff_ordered_side {a b : SArc s} (he : a.finish < b.finish) :
    (∀ h, ¬To a b h) ↔ a.SideIncl b ∧ a.finish ∉ b.left := by
  constructor
  · intro hn
    refine ⟨?_,fun hf => hn a.finish ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hf⟩⟩
    intro h hboth hra
    by_contra hnr
    have hb := mem_between.mp hboth.2
    have hp := (right_bounds hra).2.2
    have hl := leftSide_of_interior_not_right (mem_positiveInterior.mpr ⟨hb.1,hb.2,hp⟩) hnr
    exact hn h ⟨Finset.mem_insert_of_mem hra,Finset.mem_insert_of_mem hl⟩
  · rintro ⟨hs,hn⟩ h ⟨ha,hb⟩
    have hne : h ≠ b.finish := ((to_bounds (show To a b h from ⟨ha,hb⟩)).1.2.trans_lt he).ne
    have hbl : h ∈ b.left := (Finset.mem_insert.mp hb).resolve_left hne
    rcases Finset.mem_insert.mp ha with rfl | har
    · exact hn hbl
    · have ha := right_bounds har
      have hb := left_bounds hbl
      exact (mem_left.mp hbl).2 (hs h ⟨mem_between.mpr ⟨ha.1,ha.2.1⟩,
        mem_between.mpr ⟨hb.1,hb.2.1⟩⟩ har)

private theorem no_to_iff_ordered_side_rev {a b : SArc s} (he : a.finish < b.finish) :
    (∀ h, ¬To b a h) ↔ b.SideIncl a ∧ a.finish ∉ b.right := by
  constructor
  · intro hn
    refine ⟨?_,fun hf => hn a.finish ⟨Finset.mem_insert_of_mem hf,Finset.mem_insert_self _ _⟩⟩
    intro h hboth hrb
    by_contra hnr
    have ha := mem_between.mp hboth.2
    have hp := (right_bounds hrb).2.2
    have hl := leftSide_of_interior_not_right (mem_positiveInterior.mpr ⟨ha.1,ha.2,hp⟩) hnr
    exact hn h ⟨Finset.mem_insert_of_mem hrb,Finset.mem_insert_of_mem hl⟩
  · rintro ⟨hs,hn⟩ h ⟨hb,ha⟩
    have hne : h ≠ b.finish := ((to_bounds (show To b a h from ⟨hb,ha⟩)).2.2.trans_lt he).ne
    have hbr : h ∈ b.right := (Finset.mem_insert.mp hb).resolve_left hne
    rcases Finset.mem_insert.mp ha with rfl | hal
    · exact hn hbr
    · have ha := left_bounds hal
      have hb := right_bounds hbr
      exact (mem_left.mp hal).2 (hs h ⟨mem_between.mpr ⟨hb.1,hb.2.1⟩,
        mem_between.mpr ⟨ha.1,ha.2.1⟩⟩ hbr)

private theorem no_blocks_of_disjoint {a b : SArc s} (h : a.finish ≤ b.start) :
    ¬Block a b ∧ ¬Block b a := by
  exact ⟨fun ⟨_,_,_,_,ht⟩ => (to_bounds ht).2.1.not_ge ((to_bounds ht).1.2.trans h),
    fun ⟨_,_,_,_,ht⟩ => (to_bounds ht).1.1.not_ge ((to_bounds ht).2.2.trans h)⟩

private theorem no_blocks_iff_ordered {a b : SArc s} (he : a.finish < b.finish) :
    (¬Block a b ∧ ¬Block b a) ↔ a.orderedNoncrossing b := by
  rw [orderedNoncrossing_iff]
  by_cases hgap : a.finish ≤ b.start
  · exact ⟨fun _ => ⟨he,Or.inl hgap⟩,fun _ => no_blocks_of_disjoint hgap⟩
  have hba := lt_of_not_ge hgap
  have hab := a.start_lt_finish.trans he
  constructor
  · rintro ⟨ha,hb⟩
    refine ⟨he,Or.inr ?_⟩
    rcases leftOf_trichotomy hab hba with hl | hk | hl
    · have hs := (no_to_iff_ordered_side he).mp (no_to_of_no_block ha (Or.inl hl))
      exact Or.inr (Or.inl ⟨hl,hs⟩)
    · have hs := (no_to_iff_ordered_side he).mp (no_to_of_no_block ha (Or.inr hk))
      have hs' := (no_to_iff_ordered_side_rev he).mp
        (no_to_of_no_block hb (Or.inr ⟨hk.1.symm,hk.2.symm⟩))
      have hz : s a.finish = 0 := by
        by_contra hne
        have hi := mem_positiveInterior.mpr ⟨hba,he,hne⟩
        exact hs.2 (mem_left.mpr ⟨hi,hs'.2⟩)
      exact Or.inr (Or.inr ⟨hk,hz,hs'.1,hs.1⟩)
    · have hs := (no_to_iff_ordered_side_rev he).mp (no_to_of_no_block hb (Or.inl hl))
      exact Or.inl ⟨hl,hs⟩
  · rintro ⟨_,h | ⟨hl,hs⟩ | ⟨hl,hs⟩ | ⟨_,hz,hs,hs'⟩⟩
    · exact (hgap h).elim
    · exact (no_blocks_of_leftOf hl ((no_to_iff_ordered_side_rev he).mpr hs)).symm
    · exact no_blocks_of_leftOf hl ((no_to_iff_ordered_side he).mpr hs)
    · have hn₁ : a.finish ∉ b.left := fun hm => (left_bounds hm).2.2 hz
      have hn₂ : a.finish ∉ b.right := fun hm => (right_bounds hm).2.2 hz
      have ht₁ := (no_to_iff_ordered_side he).mpr ⟨hs',hn₁⟩
      have ht₂ := (no_to_iff_ordered_side_rev he).mpr ⟨hs,hn₂⟩
      exact ⟨fun ⟨_,j,_,_,hj⟩ => ht₁ j hj,fun ⟨_,j,_,_,hj⟩ => ht₂ j hj⟩

/-- The two directional comb bounds give exactly the eight noncrossing cases. -/
theorem noncrossing_iff_join_bounds (a b : SArc s) :
    a.Noncrossing b ↔ a.Tvee ≤ b.kappa ∧ b.Tvee ≤ a.kappa := by
  rw [← not_block_iff_le,← not_block_iff_le]
  rcases lt_trichotomy a.finish b.finish with h | h | h
  · exact ⟨fun hn => (no_blocks_iff_ordered h).mpr (ordered_of_noncrossing_of_lt hn h),
      fun hn => Or.inl ((no_blocks_iff_ordered h).mp hn)⟩
  · constructor
    · intro hn
      exact (finish_ne_of_noncrossing hn h).elim
    · rintro ⟨ha,hb⟩
      have ht : To a b a.finish := ⟨Finset.mem_insert_self _ _,h.symm ▸ Finset.mem_insert_self _ _⟩
      have ht' : To b a b.finish := ⟨Finset.mem_insert_self _ _,h ▸ Finset.mem_insert_self _ _⟩
      rcases leftOf_trichotomy (h ▸ a.start_lt_finish) (h.symm ▸ b.start_lt_finish) with hl | hk | hl
      · exact (no_to_of_no_block ha (Or.inl hl) _ ht).elim
      · exact (no_to_of_no_block ha (Or.inr hk) _ ht).elim
      · exact (no_to_of_no_block hb (Or.inl hl) _ ht').elim
  · exact ⟨fun hn => ((no_blocks_iff_ordered h).mpr
      (ordered_of_noncrossing_of_lt (noncrossing_symm hn) h)).symm,
      fun hn => Or.inr ((no_blocks_iff_ordered h).mp hn.symm)⟩

#print axioms noncrossing_iff_join_bounds

end Permutree.SArc
```

### `SCanonical.lean`

```lean
import CombCompatibility

namespace Permutree

open SArc

variable {n : ℕ} {s : Fin n → ℕ}

attribute [local instance] Classical.decEq

private noncomputable def imageBound (D : Finset (SArc s)) (x : STree s)
    (hx : x ∈ D.image SArc.Tvee) : JoinBound x :=
  (Finset.mem_image.mp hx).choose_spec.2 ▸ (Finset.mem_image.mp hx).choose.joinBound

private theorem imageBound_upper (D : Finset (SArc s)) (a : SArc s)
    (ha : a.Tvee ∈ D.image SArc.Tvee) : (imageBound D a.Tvee ha).upper = a.kappa := by
  unfold imageBound
  let b := (Finset.mem_image.mp ha).choose
  have h : b.Tvee = a.Tvee := (Finset.mem_image.mp ha).choose_spec.2
  have he := Tvee_injective h
  change (h ▸ b.joinBound).upper = a.kappa
  have cast_upper {x y : STree s} (e : x = y) (bound : JoinBound x) :
      (e ▸ bound : JoinBound y).upper = bound.upper := by
    cases e
    rfl
  rw [cast_upper,he]
  rfl

/-- The join half of Proposition 61, with the literal compatibility predicate
of Definition 55 and the literal graft map of Definition 48. -/
theorem canonical_join_iff_noncrossing (D : Finset (SArc s)) :
    let X := D.image SArc.Tvee
    IsCanonicalJoinRep X (X.sup id) ↔ (D : Set (SArc s)).Pairwise SArc.Noncrossing := by
  intro X
  rw [canonical_iff_pairwise_join_bounds (exists_canonical STree.joinSemidistributive)
    X (imageBound D)]
  constructor
  · intro h a ha b hb hne
    have ha' : a.Tvee ∈ X := Finset.mem_image.mpr ⟨a,ha,rfl⟩
    have hb' : b.Tvee ∈ X := Finset.mem_image.mpr ⟨b,hb,rfl⟩
    have he : a.Tvee ≠ b.Tvee := fun he => hne (Tvee_injective he)
    apply (noncrossing_iff_join_bounds _ _).mpr
    exact ⟨by simpa only [imageBound_upper] using h _ ha' _ hb' he,
      by simpa only [imageBound_upper] using h _ hb' _ ha' he.symm⟩
  · intro h x hx y hy hne
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
    rw [imageBound_upper]
    exact ((noncrossing_iff_join_bounds _ _).mp (h ha hb
      (fun he => hne (congrArg SArc.Tvee he)))).1

theorem canonical_faces_surjective (X : CanonicalFaces (STree s)) :
    ∃ D : Finset (SArc s), D.image SArc.Tvee = X.val := by
  let D := X.val.biUnion STree.combsBelow
  have includes {a : SArc s} (x : STree s) (hx : x ∈ X.val) (ha : a.Tvee ≤ x) :
      a ∈ D := Finset.mem_biUnion.mpr ⟨x,hx,STree.mem_combsBelow.mpr ha⟩
  have hJ : (D.image SArc.Tvee).sup id = X.val.sup id := by
    apply le_antisymm
    · apply Finset.sup_le
      intro z hz
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨x,hx,hax⟩ := Finset.mem_biUnion.mp ha
      exact (STree.mem_combsBelow.mp hax).trans (Finset.le_sup (f := id) hx)
    · apply Finset.sup_le
      intro x hx
      rw [← STree.sup_combs_below x]
      exact Finset.sup_le fun a ha => Finset.le_sup (f := id)
        (Finset.mem_image.mpr ⟨a,includes x hx (STree.mem_combsBelow.mp ha),rfl⟩)
  have has_arc (x : STree s) (hx : x ∈ X.val) : ∃ a : SArc s, a.Tvee = x := by
    obtain ⟨z,hz,hxz⟩ := X.property.2.2 _ hJ _ hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y,hy,hay⟩ := Finset.mem_biUnion.mp ha
    have he : x = y := X.property.eq_of_le hx hy (hxz.trans (STree.mem_combsBelow.mp hay))
    exact ⟨a,le_antisymm (he.symm ▸ STree.mem_combsBelow.mp hay) hxz⟩
  let A := Finset.univ.filter (fun a : SArc s => a.Tvee ∈ X.val)
  have he : A.image SArc.Tvee = X.val := by
    ext x
    constructor
    · intro hx
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp ha).2
    · intro hx
      obtain ⟨a,rfl⟩ := has_arc x hx
      exact Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩,rfl⟩
  exact ⟨A,he⟩

/-- The join case of Proposition 59 with the diagram-to-tree map
given by joining the grafted combs. -/
noncomputable def diagramTreeEquiv :
    {D : Finset (SArc s) // (D : Set (SArc s)).Pairwise SArc.Noncrossing} ≃ STree s := by
  let toFace (D : {D : Finset (SArc s) // (D : Set (SArc s)).Pairwise SArc.Noncrossing}) :
      CanonicalFaces (STree s) := ⟨D.val.image Tvee,
        (canonical_join_iff_noncrossing D.val).mpr D.property⟩
  have hinj : Function.Injective toFace := by
    intro D E h
    apply Subtype.ext
    have he : D.val.image Tvee = E.val.image Tvee := congrArg Subtype.val h
    ext a
    constructor
    · intro ha
      have h : a.Tvee ∈ E.val.image Tvee := he ▸ Finset.mem_image.mpr ⟨a,ha,rfl⟩
      obtain ⟨b,hb,hab⟩ := Finset.mem_image.mp h
      exact Tvee_injective hab ▸ hb
    · intro ha
      have h : a.Tvee ∈ D.val.image Tvee := he.symm ▸ Finset.mem_image.mpr ⟨a,ha,rfl⟩
      obtain ⟨b,hb,hab⟩ := Finset.mem_image.mp h
      exact Tvee_injective hab ▸ hb
  have hsurj : Function.Surjective toFace := by
    intro X
    obtain ⟨D,hD⟩ := canonical_faces_surjective X
    have hCanon : IsCanonicalJoinRep (D.image Tvee) ((D.image Tvee).sup id) := by
      rw [hD]
      exact X.property
    exact ⟨⟨D,(canonical_join_iff_noncrossing D).mp hCanon⟩, Subtype.ext hD⟩
  exact (Equiv.ofBijective toFace ⟨hinj,hsurj⟩).trans
    (canonicalJoinEquiv (exists_canonical STree.joinSemidistributive))

#check canonical_join_iff_noncrossing
#check diagramTreeEquiv
#print axioms diagramTreeEquiv
#print axioms canonical_faces_surjective
#print axioms canonical_join_iff_noncrossing

end Permutree
```

### `Forcing.lean`

```lean
import SPermutree
import CanonicalQuotient
import Mathlib.Logic.Relation

namespace Permutree

open Relation

variable {L : Type*} [Lattice L]

/-- Congruence generated by all relations from the family. -/
def congruenceJoin {I : Type*} (C : I → LatticeCon L) : LatticeCon L where
  r := ReflTransGen fun x y => ∃ i, (C i).r x y
  iseqv.refl _ := .refl
  iseqv.symm h := by
    induction h with
    | refl => exact .refl
    | tail _ h ih => obtain ⟨i,hi⟩ := h; exact (ReflTransGen.single (r := fun a b => ∃ i, (C i).r a b) ⟨i,(C i).symm hi⟩).trans ih
  iseqv.trans := ReflTransGen.trans
  inf := by
    intro w x y z h₁ h₂
    have h₁' : ReflTransGen (fun a b => ∃ i, (C i).r a b) (w ⊓ y) (x ⊓ y) :=
      h₁.lift (fun t => t ⊓ y) (by
        rintro a b ⟨i,hi⟩
        exact ⟨i,(C i).inf hi ((C i).refl y)⟩)
    have h₂' : ReflTransGen (fun a b => ∃ i, (C i).r a b) (x ⊓ y) (x ⊓ z) :=
      h₂.lift (fun t => x ⊓ t) (by
        rintro a b ⟨i,hi⟩
        exact ⟨i,(C i).inf ((C i).refl x) hi⟩)
    exact h₁'.trans h₂'
  sup := by
    intro w x y z h₁ h₂
    have h₁' : ReflTransGen (fun a b => ∃ i, (C i).r a b) (w ⊔ y) (x ⊔ y) :=
      h₁.lift (fun t => t ⊔ y) (by
        rintro a b ⟨i,hi⟩
        exact ⟨i,(C i).sup hi ((C i).refl y)⟩)
    have h₂' : ReflTransGen (fun a b => ∃ i, (C i).r a b) (x ⊔ y) (x ⊔ z) :=
      h₂.lift (fun t => x ⊔ t) (by
        rintro a b ⟨i,hi⟩
        exact ⟨i,(C i).sup ((C i).refl x) hi⟩)
    exact h₁'.trans h₂'

theorem congruenceJoin_of_rel {I : Type*} {C : I → LatticeCon L} {x y : L}
    (i : I) (h : (C i).r x y) : (congruenceJoin C).r x y :=
  ReflTransGen.single ⟨i,h⟩

theorem congruenceJoin_le {I : Type*} {C : I → LatticeCon L} (c : LatticeCon L)
    (h : ∀ i x y, (C i).r x y → c.r x y) {x y : L} (hc : (congruenceJoin C).r x y) : c.r x y := by
  change ReflTransGen _ _ _ at hc
  induction hc with
  | refl => exact c.refl _
  | tail _ h' ih => obtain ⟨i,hi⟩ := h'; exact c.trans ih (h i _ _ hi)

/-- Contraction of a cover by a join of congruences is witnessed by a
single member. Clamp every step of the chain to the two-element interval. -/
theorem contract_cover_congruenceJoin {I : Type*} {C : I → LatticeCon L} {x y : L}
    (hxy : x ⋖ y) (h : (congruenceJoin C).r x y) : ∃ i, (C i).r x y := by
  let t (z : L) := (z ⊔ x) ⊓ y
  have both (z : L) : t z = x ∨ t z = y :=
    hxy.eq_or_eq (le_inf le_sup_right hxy.le) inf_le_right
  have hx : t x = x := by simp [t, inf_eq_left.mpr hxy.le]
  have hy : t y = y := by simp [t, sup_eq_left.mpr hxy.le]
  by_contra hn
  have hstep {a b : L} (hab : ∃ i, (C i).r a b) : t a = t b := by
    obtain ⟨i,hi⟩ := hab
    have h' : (C i).r (t a) (t b) :=
      (C i).inf ((C i).sup hi ((C i).refl x)) ((C i).refl y)
    rcases both a with ha | ha <;> rcases both b with hb | hb
    · exact ha.trans hb.symm
    · exact (hn ⟨i,ha ▸ hb ▸ h'⟩).elim
    · exact (hn ⟨i,hb ▸ ha ▸ (C i).symm h'⟩).elim
    · exact ha.trans hb.symm
  change ReflTransGen _ _ _ at h
  have respects {a b : L} (h : ReflTransGen (fun a b => ∃ i, (C i).r a b) a b) : t a = t b := by
    induction h with
    | refl => rfl
    | tail _ hh ih => exact ih.trans (hstep hh)
  exact hxy.ne (hx.symm.trans ((respects h).trans hy))

variable {n : ℕ} {s : Fin n → ℕ}

namespace SArc

/-- Definition 70 of the source. -/
def IsSubarc (a b : SArc s) : Prop :=
  b.start ≤ a.start ∧ a.finish ≤ b.finish ∧
  a.right ⊆ b.right ∧ a.left ⊆ b.left ∧
  (s a.finish = 0 → a.finish = b.finish) ∧
  (a.start = b.start → a.r = b.r) ∧
  (b.start < a.start → (a.start ∈ b.right ∧ a.r = 1) ∨
    (a.start ∈ b.left ∧ a.r = s a.start))

theorem allowed_of_subarc {d : Decoration s} {a b : SArc s} (h : a.IsSubarc b)
    (hb : Allowed d b) : Allowed d a :=
  fun i => ⟨fun hi => (hb i).1 (h.2.2.1 hi), fun hi => (hb i).2 (h.2.2.2.1 hi)⟩

/-- The principal congruence associated to the lower cover(s) of the join comb.
Proposition 51 of the source supplies existence and uniqueness of the cover. -/
noncomputable def principal (a : SArc s) : LatticeCon (STree s) :=
  generatedCongruence fun x y => x = a.Tvee ∧ y ⋖ x

end SArc

theorem permutreeCon_eq_join (d : Decoration s) :
    ∀ x y, (permutreeCon s d).r x y ↔
      (congruenceJoin (fun a : {a : SArc s // ¬Allowed d a} => a.val.principal)).r x y := by
  intro x y
  constructor
  · apply generated_le
    intro x y h
    obtain ⟨a,ha,hxy,hy⟩ := h
    exact congruenceJoin_of_rel ⟨a,ha⟩ (generated_contains _ ⟨hxy,hy⟩)
  · apply congruenceJoin_le
    intro a x y
    apply generated_le
    intro x y h
    exact generated_contains _ ⟨a.val,a.property,h.1,h.2⟩

/-- The forward direction of Theorem 72, stated in terms of generated congruences. -/
def SourceForcingForward (s : Fin n → ℕ) : Prop :=
  ∀ (a b : SArc s) (x : STree s), x ⋖ b.Tvee → a.principal.r x b.Tvee → a.IsSubarc b

theorem uncontracted_of_allowed (h72 : SourceForcingForward s) (d : Decoration s)
    (b : SArc s) (hb : Allowed d b) : ConQuot.IsUncontracted (permutreeCon s d) b.Tvee := by
  intro x hx he
  have h := (permutreeCon_eq_join d x _).mp ((ConQuot.mk_eq_mk _).mp he)
  obtain ⟨a,ha⟩ := contract_cover_congruenceJoin hx h
  exact a.property (SArc.allowed_of_subarc (h72 a.val b x hx ha) hb)

theorem uncontracted_iff_allowed (h72 : SourceForcingForward s)
    (hcover : ∀ a : SArc s, ∃ x : STree s, x ⋖ a.Tvee) (d : Decoration s) (b : SArc s) :
    ConQuot.IsUncontracted (permutreeCon s d) b.Tvee ↔ Allowed d b := by
  constructor
  · intro hu
    by_contra hf
    obtain ⟨x,hx⟩ := hcover b
    exact hu x hx (forbidden_contracts hf hx)
  · exact uncontracted_of_allowed h72 d b

#print axioms contract_cover_congruenceJoin
#print axioms uncontracted_iff_allowed

end Permutree
```

### `SourceForcingForward.lean`

```lean
import Forcing
import CombBounds
import Mathlib.Order.Atoms.Finite

namespace Permutree

open SArc TreePrefix SPosition

variable {n : ℕ} {s : Fin n → ℕ}

namespace SArc

theorem IsSubarc.refl (a : SArc s) : a.IsSubarc a :=
  ⟨le_rfl,le_rfl,fun _ h => h,fun _ h => h,fun _ => rfl,fun _ => rfl,fun h => (lt_irrefl _ h).elim⟩

theorem IsSubarc.trans {a b c : SArc s} (ab : a.IsSubarc b) (bc : b.IsSubarc c) :
    a.IsSubarc c := by
  obtain ⟨ab₁,ab₂,abR,abL,abZ,abE,abS⟩ := ab
  obtain ⟨bc₁,bc₂,bcR,bcL,bcZ,bcE,bcS⟩ := bc
  refine ⟨bc₁.trans ab₁,ab₂.trans bc₂,abR.trans bcR,abL.trans bcL,?_,?_,?_⟩
  · intro hs
    have he := abZ hs
    exact he.trans (bcZ (he ▸ hs))
  · intro h
    have e₁ := ab₁.antisymm (h.symm ▸ bc₁)
    have e₂ := e₁.trans h
    exact (abE e₁.symm).trans (bcE e₂)
  · intro h
    rcases ab₁.eq_or_lt with e | hlt
    · have h' := bcS (e ▸ h)
      have er := abE e.symm
      rcases h' with ⟨hr,hr'⟩ | ⟨hl,hl'⟩
      · exact Or.inl ⟨e.symm ▸ hr,er.trans hr'⟩
      · exact Or.inr ⟨e.symm ▸ hl,er.trans (e.symm ▸ hl')⟩
    · exact (abS hlt).imp (fun h => ⟨bcR h.1,h.2⟩) (fun h => ⟨bcL h.1,h.2⟩)

end SArc

namespace STree

variable {a : SArc s} {z : STree s}

/-- A join walk which improves a threshold must traverse the distinguished
edge. Its prefix and suffix are already available in the old tree. -/
structure CrossesComb (a : SArc s) (z : STree s) (u v : Fin n) (t : ℕ) : Prop where
  start_le : u ≤ a.start
  finish_le : a.finish ≤ v
  prefix_bound : u < a.start → t ≤ z.pos u a.start
  first_threshold : u = a.start → t = a.r
  suffix : a.finish < v → 0 < z.pos a.finish v

private theorem new_comb_edge (hl : a.lowerTree ≤ z) {u v : Fin n} {t : ℕ}
    (hr : t ≤ max (z.pos u v) (a.Tvee.pos u v)) (hn : ¬ t ≤ z.pos u v) :
    u = a.start ∧ v = a.finish ∧ t = a.r := by
  have ht := (le_max_iff.mp hr).resolve_left hn
  by_cases he : u = a.start ∧ v = a.finish
  · obtain ⟨rfl,rfl⟩ := he
    have hlo := hl a.start a.finish
    change a.lowerTree.pos a.start a.finish ≤ z.pos a.start a.finish at hlo
    simp [pos_lowerTree] at hlo
    rw [Tvee_pos_start_finish] at ht
    exact ⟨rfl,rfl,by omega⟩
  · have hlo := hl u v
    change a.lowerTree.pos u v ≤ z.pos u v at hlo
    rw [pos_lowerTree,ite_eq_right he] at hlo
    exact (hn (ht.trans hlo)).elim

private theorem walk_crosses_comb (hl : a.lowerTree ≤ z)
    {u v : Fin n} {t : ℕ}
    (w : Walk (fun x y => max (z.pos x y) (a.Tvee.pos x y)) u t v) :
    t ≤ z.pos u v ∨ CrossesComb a z u v t := by
  induction w with
  | @single u v t _ hr =>
    by_cases h : t ≤ z.pos u v
    · exact Or.inl h
    · obtain ⟨rfl,rfl,rfl⟩ := new_comb_edge hl hr h
      exact Or.inr ⟨le_rfl,le_rfl,fun h => (lt_irrefl _ h).elim,fun _ => rfl,
        fun h => (lt_irrefl _ h).elim⟩
  | @cons u k v t huk hr tail ih =>
    rcases ih with htail | htail
    · by_cases h : t ≤ z.pos u k
      · exact Or.inl (h.trans (z.toPosition.transitive huk tail.increasing htail))
      · obtain ⟨rfl,rfl,rfl⟩ := new_comb_edge hl hr h
        exact Or.inr ⟨le_rfl,tail.increasing.le,fun h => (lt_irrefl _ h).elim,fun _ => rfl,fun _ => htail⟩
    · have hu : u < a.start := huk.trans_le htail.start_le
      have hpre : t ≤ z.pos u k := by
        by_contra hn
        exact hu.ne (new_comb_edge hl hr hn).1
      refine Or.inr ⟨hu.le,htail.finish_le,fun _ => ?_,fun h => (hu.ne h).elim,htail.suffix⟩
      rcases htail.start_le.eq_or_lt with e | hlt
      · exact e ▸ hpre
      · exact hpre.trans (z.toPosition.transitive huk hlt (htail.prefix_bound hlt))

theorem new_join_threshold (hl : a.lowerTree ≤ z) {u v : Fin n} {t : ℕ}
    (hnew : t ≤ (z ⊔ a.Tvee).pos u v) (hold : ¬ t ≤ z.pos u v) :
    CrossesComb a z u v t := by
  have ht : 0 < t := Nat.pos_of_ne_zero (fun e => hold (e.symm ▸ Nat.zero_le _))
  have hpos : (z ⊔ a.Tvee).toPosition = SPosition.join z.toPosition a.Tvee.toPosition :=
    STree.positionEquiv.apply_symm_apply _
  change t ≤ (z ⊔ a.Tvee).toPosition.pos u v at hnew
  rw [hpos] at hnew
  obtain w := walk_of_le_closure ht hnew
  exact (walk_crosses_comb hl w).resolve_left hold

private theorem left_buffer (hl : a.lowerTree ≤ z) {h : Fin n} (hh : h ∈ a.left) :
    s h ≤ z.pos h a.finish := by
  obtain ⟨hstart,hfinish,_⟩ := mem_positiveInterior.mp (mem_left.mp hh).1
  have hle : a.lowerTree.pos h a.finish ≤ z.pos h a.finish := hl _ _
  rwa [pos_lowerTree,ite_eq_right (fun h => hstart.ne h.1.symm),
    pos_Tvee a h a.finish hfinish,ite_eq_left (show a.finish ∈ a.graftNodes from Finset.mem_insert_self _ _),
    ite_eq_right hstart.ne.symm,ite_eq_left hh] at hle

private theorem right_buffer (hl : a.lowerTree ≤ z) {h : Fin n} (hh : h ∈ a.right) :
    a.r ≤ z.pos a.start h := by
  obtain ⟨hstart,hfinish,_⟩ := mem_positiveInterior.mp (a.right_subset hh)
  have hle : a.lowerTree.pos a.start h ≤ z.pos a.start h := hl _ _
  rwa [pos_lowerTree,ite_eq_right (fun h => hfinish.ne h.2),
    pos_Tvee a a.start h hstart,ite_eq_left (show h ∈ a.graftNodes from Finset.mem_insert_of_mem hh),ite_eq_left rfl] at hle

/-- A newly visible comb can only extend the arc of the threshold change. -/
theorem forcing_steps_extend_arcs (hl : a.lowerTree ≤ z) {b : SArc s}
    (hb : b.Tvee ≤ z ⊔ a.Tvee) (hn : ¬ b.Tvee ≤ z) : a.IsSubarc b := by
  change ¬ ∀ u v, b.Tvee.pos u v ≤ z.pos u v at hn
  push Not at hn
  obtain ⟨u,v,hn⟩ := hn
  let t := b.Tvee.pos u v
  have hold : ¬ t ≤ z.pos u v := not_le_of_gt hn
  have ht : 0 < t := (Nat.zero_le _).trans_lt hn
  have huv : u < v := by
    by_contra h
    exact ht.ne' (pos_zero_of_not_lt b.Tvee u v h)
  have hcross : CrossesComb a z u v t := new_join_threshold hl (hb u v) hold
  have hv : v ∈ b.graftNodes := by
    by_contra h
    have e : t = 0 := by simp [t,pos_Tvee b u v huv,h]
    exact ht.ne' e
  have hu : u = b.start ∨ u ∈ b.left := by
    by_contra h
    have e : t = 0 := by
      change b.Tvee.pos u v = 0
      rw [pos_Tvee b u v huv,ite_eq_left hv,ite_eq_right (fun e => h (Or.inl e)),
        ite_eq_right (fun e => h (Or.inr e))]
    exact ht.ne' e
  have u_bound : b.start ≤ u := hu.elim (fun e => e.ge)
    (fun h => (mem_positiveInterior.mp (mem_left.mp h).1).1.le)
  have v_bound : v ≤ b.finish := (Finset.mem_insert.mp hv).elim
    (fun e => e.le) (fun h => (mem_positiveInterior.mp (b.right_subset h)).2.1.le)
  have hstart := u_bound.trans hcross.start_le
  have hfinish := hcross.finish_le.trans v_bound
  have sameRow {w : Fin n} (hw : w ∈ b.graftNodes) (huw : u < w) :
      t ≤ (z ⊔ a.Tvee).pos u w := by
    have e : b.Tvee.pos u v = b.Tvee.pos u w := by
      rw [pos_Tvee b u v huv, pos_Tvee b u w huw,ite_eq_left hv,ite_eq_left hw]
    change b.Tvee.pos u v ≤ _
    rw [e]
    exact hb u w
  have extendTail {h : Fin n} (hh : h < a.finish) (hp : 0 < z.pos h a.finish) :
      0 < z.pos h v := by
    rcases hcross.finish_le.eq_or_lt with e | hlt
    · exact e ▸ hp
    · exact hp.trans_le (z.toPosition.transitive hh hlt (hcross.suffix hlt))
  have contradictOld {h : Fin n} (h₁ : u < h) (h₂ : h < v)
      (h₃ : t ≤ z.pos u h) (h₄ : 0 < z.pos h v) : False :=
    hold (h₃.trans (z.toPosition.transitive h₁ h₂ h₄))
  have interiors {h : Fin n} (hh : h ∈ positiveInterior s a.start a.finish) :
      h ∈ positiveInterior s b.start b.finish := by
    obtain ⟨hs,hf,hp⟩ := mem_positiveInterior.mp hh
    exact mem_positiveInterior.mpr ⟨hstart.trans_lt hs,hf.trans_le hfinish,hp⟩
  refine ⟨hstart,hfinish,?_,?_,?_,?_,?_⟩
  · intro h hh
    by_contra hnot
    have hbL := mem_left.mpr ⟨interiors (a.right_subset hh),hnot⟩
    obtain ⟨hph,hq,hpos⟩ := mem_positiveInterior.mp (a.right_subset hh)
    have huv' := hcross.start_le.trans_lt hph
    have hv' := hq.trans_le hcross.finish_le
    have hreach : t ≤ z.pos u h := by
      rcases hcross.start_le.eq_or_lt with e | hlt
      · have et := hcross.first_threshold e
        rw [e,et]
        exact right_buffer hl hh
      · exact (hcross.prefix_bound hlt).trans (z.toPosition.transitive hlt hph
          (a.r_pos.trans_le (right_buffer hl hh)))
    have hle : s h ≤ (z ⊔ a.Tvee).pos h v := by
      have hle : b.Tvee.pos h v ≤ (z ⊔ a.Tvee).pos h v := hb h v
      rwa [pos_Tvee b h v hv' ,ite_eq_left hv,ite_eq_right
        (mem_positiveInterior.mp (mem_left.mp hbL).1).1.ne.symm,ite_eq_left hbL] at hle
    have hOld : s h ≤ z.pos h v := by
      by_contra hn'
      exact (not_le_of_gt hph) (new_join_threshold hl hle hn').start_le
    exact contradictOld huv' hv' hreach ((Nat.pos_of_ne_zero hpos).trans_le hOld)
  · intro h hh
    have hin := interiors (mem_left.mp hh).1
    refine mem_left.mpr ⟨hin,?_⟩
    intro hbR
    obtain ⟨hph,hq,hpos⟩ := mem_positiveInterior.mp (mem_left.mp hh).1
    have huv' := hcross.start_le.trans_lt hph
    have hnew := sameRow (Finset.mem_insert_of_mem hbR) huv'
    have hOld : t ≤ z.pos u h := by
      by_contra hn'
      exact (not_le_of_gt hq) (new_join_threshold hl hnew hn').finish_le
    exact contradictOld huv' (hq.trans_le hcross.finish_le) hOld
      (extendTail hq ((Nat.pos_of_ne_zero hpos).trans_le (left_buffer hl hh)))
  · intro hzero
    have e : a.finish = v := by
      apply hcross.finish_le.eq_of_not_lt
      intro hlt
      have hp := hcross.suffix hlt
      have hle := z.pos_bound a.finish v
      omega
    rcases Finset.mem_insert.mp hv with hf | hr
    · exact e.trans hf
    · exact ((mem_positiveInterior.mp (b.right_subset hr)).2.2 (e ▸ hzero)).elim
  · intro he
    have eu : u = b.start := (hcross.start_le.trans he.le).antisymm u_bound
    have et : t = b.r := by
      change b.Tvee.pos u v = _
      rw [pos_Tvee b u v huv,ite_eq_left hv,ite_eq_left eu]
    exact (hcross.first_threshold (eu.trans he.symm)).symm.trans et
  · intro hbstart
    have hin : a.start ∈ positiveInterior s b.start b.finish :=
      mem_positiveInterior.mpr ⟨hbstart,a.start_lt_finish.trans_le hfinish,a.start_pos⟩
    by_cases hr : a.start ∈ b.right
    · refine Or.inl ⟨hr,?_⟩
      have hu' : u < a.start := lt_of_le_of_ne hcross.start_le (fun e => by
        rcases hu with h | h
        · exact hbstart.ne (h.symm.trans e)
        · exact (mem_left.mp h).2 (e.symm ▸ hr))
      by_contra hnot
      have hp : 0 < z.pos a.start a.finish := by
        have hlo : a.lowerTree.pos a.start a.finish ≤ z.pos a.start a.finish := hl _ _
        rw [pos_lowerTree] at hlo
        simp only [and_self,ite_true] at hlo
        have := a.r_pos
        omega
      exact contradictOld hu' (a.start_lt_finish.trans_le hcross.finish_le)
        (hcross.prefix_bound hu') (extendTail a.start_lt_finish hp)
    · have hL := mem_left.mpr ⟨hin,hr⟩
      refine Or.inr ⟨hL,?_⟩
      have hpv := a.start_lt_finish.trans_le hcross.finish_le
      have hle : s a.start ≤ (z ⊔ a.Tvee).pos a.start v := by
        have h : b.Tvee.pos a.start v ≤ (z ⊔ a.Tvee).pos a.start v := hb a.start v
        rwa [pos_Tvee b a.start v hpv,ite_eq_left hv,ite_eq_right hbstart.ne.symm,ite_eq_left hL] at h
      rcases hcross.start_le.eq_or_lt with e | hlt
      · have h₁ : (if u = b.start then b.r else if u ∈ b.left then s u else 0) = t := by
          change _ = b.Tvee.pos u v
          rw [pos_Tvee b u v huv,ite_eq_left hv]
        rw [e,ite_eq_right hbstart.ne.symm,ite_eq_left hL] at h₁
        exact (hcross.first_threshold e).symm.trans h₁.symm
      · by_contra hne
        have hOld : s a.start ≤ z.pos a.start v := by
          by_contra hn'
          exact hne ((new_join_threshold hl hle hn').first_threshold rfl).symm
        exact contradictOld hlt hpv (hcross.prefix_bound hlt)
          ((Nat.pos_of_ne_zero a.start_pos).trans_le hOld)

/-- The least comb of a cover is already present up to its own lower cover. -/
theorem edge_label_of_cover {x y : STree s} (hxy : x ⋖ y) :
    ∃ a : SArc s, x ⊔ a.Tvee = y ∧ a.lowerTree ≤ x ∧ ¬ a.Tvee ≤ x := by
  obtain ⟨a,ha,hmin⟩ := cover_least_comb hxy
  refine ⟨a,ha,?_,fun h => hxy.ne ((sup_eq_left.mpr h).symm.trans ha)⟩
  have hu : x ⊔ a.lowerTree ≤ y := ha ▸ sup_le_sup_left a.lowerTree_lt.le x
  rcases hxy.eq_or_eq le_sup_left hu with he | he
  · exact le_sup_right.trans he.le
  · exact (not_le_of_gt a.lowerTree_lt (hmin _ he)).elim

/-- Visibility excludes combs whose arcs extend the contracted arc. -/
def SameVisible (a : SArc s) (x y : STree s) : Prop :=
  ∀ b : SArc s, ¬ a.IsSubarc b → (b.Tvee ≤ x ↔ b.Tvee ≤ y)

theorem SameVisible.join_right_cover {a : SArc s} {x y : STree s}
    (hxy : x ⋖ y) (h : SameVisible a x y) (z : STree s) :
    SameVisible a (x ⊔ z) (y ⊔ z) := by
  obtain ⟨e,he,hl,hn⟩ := edge_label_of_cover hxy
  have hext : a.IsSubarc e := by
    by_contra hnot
    exact hn ((h e hnot).mpr (he ▸ le_sup_right))
  intro b hb
  refine ⟨fun hw => hw.trans (sup_le_sup_right hxy.le z),fun hw => ?_⟩
  by_contra hnot
  have hjoin : y ⊔ z = (x ⊔ z) ⊔ e.Tvee := by rw [← he]; ac_rfl
  rw [hjoin] at hw
  exact hb (hext.trans (forcing_steps_extend_arcs (hl.trans le_sup_left) hw hnot))

theorem SameVisible.join_right_of_le {a : SArc s} {x y : STree s}
    (hxy : x ≤ y) (h : SameVisible a x y) (z : STree s) :
    SameVisible a (x ⊔ z) (y ⊔ z) := by
  revert x
  induction y using WellFoundedLT.induction with
  | ind y ih =>
    intro x hxy h
    rcases hxy.eq_or_lt with rfl | hlt
    · exact fun _ _ => Iff.rfl
    obtain ⟨u,huy,hxu⟩ := exists_covBy_le_of_lt (α := (STree s)ᵒᵈ) hlt
    have huy' : OrderDual.ofDual u ⋖ y := CovBy.ofDual huy
    have hxu' : x ≤ OrderDual.ofDual u := hxu
    have h₁ : SameVisible a x u := fun b hb =>
      ⟨fun h => h.trans hxu',fun h' => (h b hb).mpr (h'.trans huy'.le)⟩
    have h₂ : SameVisible a u y := fun b hb =>
      ⟨fun h => h.trans huy'.le,fun h' => ((h b hb).mpr h').trans hxu'⟩
    exact fun b hb => (ih (OrderDual.ofDual u) huy'.lt hxu' h₁ b hb).trans ((h₂.join_right_cover huy' z) b hb)

theorem SameVisible.join_right {a : SArc s} {x y : STree s}
    (h : SameVisible a x y) (z : STree s) : SameVisible a (x ⊔ z) (y ⊔ z) := by
  have hx : SameVisible a (x ⊓ y) x := fun b hb => by
    rw [le_inf_iff]
    exact ⟨And.left,fun h' => ⟨h',(h b hb).mp h'⟩⟩
  have hy : SameVisible a (x ⊓ y) y := fun b hb => by
    rw [le_inf_iff]
    exact ⟨And.right,fun h' => ⟨(h b hb).mpr h',h'⟩⟩
  exact fun b hb => ((hx.join_right_of_le inf_le_left z) b hb).symm.trans
    ((hy.join_right_of_le inf_le_right z) b hb)

/-- For each arc, observing all combs outside its extensions gives a
lattice congruence that contracts its principal cover. -/
def visibleCongruence (a : SArc s) : LatticeCon (STree s) where
  r := SameVisible a
  iseqv.refl _ _ _ := Iff.rfl
  iseqv.symm h _ hb := (h _ hb).symm
  iseqv.trans h k _ hb := (h _ hb).trans (k _ hb)
  inf h k b hb := by rw [le_inf_iff,le_inf_iff,h b hb,k b hb]
  sup {x y z w} h k b hb := by
    have h₁ := (h.join_right z) b hb
    have h₂ := (k.join_right y) b hb
    rw [sup_comm z y,sup_comm w y] at h₂
    exact h₁.trans h₂

theorem visibleCongruence_contracts (a : SArc s) :
    (visibleCongruence a).r a.Tvee a.lowerTree := by
  intro b hb
  refine ⟨fun h => ?_,fun h => h.trans a.lowerTree_lt.le⟩
  rcases h.eq_or_lt with he | hlt
  · have hba := Tvee_injective he
    subst b
    exact (hb (IsSubarc.refl a)).elim
  · exact a.le_lowerTree_of_lt hlt

end STree

theorem source_forcing_forward : SourceForcingForward s := by
  intro a b x hx ha
  let c := STree.visibleCongruence a
  have hcont (u v : STree s) (h : u = a.Tvee ∧ v ⋖ u) : c.r u v := by
    obtain ⟨rfl,hv⟩ := h
    have he : v = a.lowerTree := by
      exact ((hv.eq_or_eq (a.le_lowerTree_of_lt hv.lt) a.lowerTree_lt.le).resolve_right a.lowerTree_lt.ne).symm
    subst v
    exact STree.visibleCongruence_contracts a
  have he : c.r x b.Tvee := ha c hcont
  by_contra hnot
  exact hx.lt.not_ge ((he b hnot).mpr le_rfl)

#check source_forcing_forward
#print axioms SArc.IsSubarc.trans
#print axioms STree.new_join_threshold
#print axioms STree.forcing_steps_extend_arcs
#print axioms STree.edge_label_of_cover
#print axioms source_forcing_forward

end Permutree
```

### `ConditionalInvariance.lean`

```lean
import SweepInverse
import Forcing
import SCanonical

namespace Permutree

variable {n : ℕ} {s : Fin n → ℕ}

/-- Paper sweep reconstruction, isolated from the published lattice results. -/
def MarkedSweepBridge (s : Fin n → ℕ) : Prop :=
  ∀ (d : Decoration s) (m : ℕ), Nonempty (MarkedOfSize d m ≃ Sweep (levels d) 0 m)

/-- Conditional on the graded realization of the ordered-list sweep.
The diagram on either side uses Definition 55. -/
theorem diagram_invariance_of_marked_sweep (hSweep : MarkedSweepBridge s)
    (d : Decoration s) (k : {i // s i ≠ 0}) (hk : d k = .up) (m : ℕ) :
    Fintype.card (DiagramOfSize d m) =
      Fintype.card (DiagramOfSize (Function.update d k .down) m) := by
  let d' := Function.update d k .down
  calc
    Fintype.card (DiagramOfSize d m) = Fintype.card (Sweep (levels d) 0 m) :=
      Fintype.card_congr ((groupEquiv d m).trans (Classical.choice (hSweep d m)))
    _ = Fintype.card (Sweep (levels d') 0 m) := up_to_down_sweep_card d k hk m
    _ = Fintype.card (DiagramOfSize d' m) :=
      (Fintype.card_congr ((groupEquiv d' m).trans (Classical.choice (hSweep d' m)))).symm

theorem marked_sweep_bridge : MarkedSweepBridge s :=
  fun d m => ⟨SweepStep.encode_marked_sweep_inverse d m⟩

/-- Orientation invariance for the graded literal diagrams of Definition 55. -/
theorem diagram_invariance (d : Decoration s) (k : {i // s i ≠ 0})
    (hk : d k = .up) (m : ℕ) :
    Fintype.card (DiagramOfSize d m) =
      Fintype.card (DiagramOfSize (Function.update d k .down) m) :=
  diagram_invariance_of_marked_sweep marked_sweep_bridge d k hk m

attribute [local instance] Classical.decEq

noncomputable def quotientFacesEquivDiagrams
    (h72 : SourceForcingForward s)
    (d : Decoration s) (m : ℕ) :
    CanonicalFaceOfSize (PermutreeLattice s d) m ≃ DiagramOfSize d m := by
  let c := permutreeCon s d
  let f : SArc s ↪ STree s := ⟨SArc.Tvee,SArc.Tvee_injective⟩
  have hemb : ∀ D : Finset (SArc s), D.map f = D.image SArc.Tvee := fun D => by
    ext z
    simp [f]
  have hdec (D : Finset (SArc s)) :
      (∀ a ∈ D, Allowed d a) ↔ ∀ x ∈ D.map f, ConQuot.IsUncontracted c x := by
    simp only [Finset.mem_map]
    constructor
    · rintro h x ⟨a,ha,rfl⟩
      exact (uncontracted_iff_allowed h72 SArc.Tvee_has_lower_cover d a).mpr (h a ha)
    · intro h a ha
      exact (uncontracted_iff_allowed h72 SArc.Tvee_has_lower_cover d a).mp (h _ ⟨a,ha,rfl⟩)
  refine (ConQuot.canonicalQuotientEquiv c m).trans (Equiv.ofBijective (fun D => ?_) ⟨?_,?_⟩).symm
  · refine ⟨⟨D.val.map f, ?_, (Finset.card_map f).trans D.property.2⟩, (hdec _).mp D.property.1.1⟩
    rw [hemb]
    exact (canonical_join_iff_noncrossing _).mpr D.property.1.2
  · intro D E h
    have hm := congrArg (fun X : {X : CanonicalFaceOfSize (STree s) m // ∀ a ∈ X.val,
      ConQuot.IsUncontracted c a} => X.val.val) h
    exact Subtype.ext ((Finset.map_injective f) hm)
  · intro X
    obtain ⟨D,hD⟩ := canonical_faces_surjective ⟨X.val.val,X.val.property.1⟩
    have hh : D.map f = X.val.val := (hemb D).trans hD
    have hd : IsDiagram d D := by
      refine ⟨(hdec D).mpr (hh ▸ X.property), (canonical_join_iff_noncrossing D).mp ?_⟩
      rw [← hemb,hh]
      exact X.val.property.1
    have hn : D.card = m := by rw [← Finset.card_map (f := f), hh, X.val.property.2]
    exact ⟨⟨D,hd,hn⟩, Subtype.ext (Subtype.ext hh)⟩

/-- Conditional transfer of the diagram enumeration to the literal lattice.
It assumes the forward direction of Theorem 72. It also assumes the explicitly named paper sweep bridge. -/
theorem orientation_invariance_conditional
    (hSweep : MarkedSweepBridge s)
    (h72 : SourceForcingForward s)
    (d : Decoration s) (k : {i // s i ≠ 0}) (hk : d k = .up) :
    let d' := Function.update d k .down
    Fintype.card (PermutreeLattice s d) = Fintype.card (PermutreeLattice s d') ∧
    ∀ m : ℕ, Fintype.card (CanonicalFaceOfSize (PermutreeLattice s d) m) =
      Fintype.card (CanonicalFaceOfSize (PermutreeLattice s d') m) := by
  intro d'
  have faces (m : ℕ) : Fintype.card (CanonicalFaceOfSize (PermutreeLattice s d) m) =
      Fintype.card (CanonicalFaceOfSize (PermutreeLattice s d') m) :=
    (Fintype.card_congr (quotientFacesEquivDiagrams h72 d m)).trans
      ((diagram_invariance_of_marked_sweep hSweep d k hk m).trans
        (Fintype.card_congr (quotientFacesEquivDiagrams h72 d' m)).symm)
  have existsInQuotient (e : Decoration s) (x : PermutreeLattice s e) :
      ∃ X : Finset (PermutreeLattice s e), IsCanonicalJoinRep X x := by
    exact exists_canonical (ConQuot.joinSemidistributive_quotient
      (permutreeCon s e) STree.joinSemidistributive) x
  exact ⟨card_eq_of_canonical_counts (existsInQuotient d) (existsInQuotient d') faces, faces⟩

/-- Orientation invariance for the literal quotient, conditional only on
the forward direction of the source's forcing theorem. -/
theorem orientation_invariance_of_source_forcing (h72 : SourceForcingForward s)
    (d : Decoration s) (k : {i // s i ≠ 0}) (hk : d k = .up) :
    let d' := Function.update d k .down
    Fintype.card (PermutreeLattice s d) = Fintype.card (PermutreeLattice s d') ∧
    ∀ m : ℕ, Fintype.card (CanonicalFaceOfSize (PermutreeLattice s d) m) =
      Fintype.card (CanonicalFaceOfSize (PermutreeLattice s d') m) :=
  orientation_invariance_conditional marked_sweep_bridge h72 d k hk

#check diagram_invariance
#check orientation_invariance_of_source_forcing
#print axioms marked_sweep_bridge
#print axioms diagram_invariance
#print axioms orientation_invariance_of_source_forcing

#check diagram_invariance_of_marked_sweep
#check quotientFacesEquivDiagrams
#check orientation_invariance_conditional
#print axioms diagram_invariance_of_marked_sweep
#print axioms quotientFacesEquivDiagrams
#print axioms orientation_invariance_conditional

end Permutree
```

### `OrientationInvariance.lean`

```lean
import ConditionalInvariance
import SourceForcingForward

namespace Permutree

variable {n : ℕ} {s : Fin n → ℕ}
attribute [local instance] Classical.decEq

/-- The graded canonical join faces of the literal quotient are the allowed
noncrossing diagrams. -/
noncomputable def quotient_faces_equiv_diagrams (d : Decoration s) (m : ℕ) :
    CanonicalFaceOfSize (PermutreeLattice s d) m ≃ DiagramOfSize d m :=
  quotientFacesEquivDiagrams source_forcing_forward d m

/-- Philippe and Pilaud, Conjecture 76. Changing one up decoration to down
preserves the lattice cardinality and every entry of the canonical join f-vector. -/
theorem philippe_pilaud_conj76 (d : Decoration s) (k : {i // s i ≠ 0})
    (hk : d k = .up) :
    let d' := Function.update d k .down
    Fintype.card (PermutreeLattice s d) = Fintype.card (PermutreeLattice s d') ∧
    ∀ m : ℕ, Fintype.card (CanonicalFaceOfSize (PermutreeLattice s d) m) =
      Fintype.card (CanonicalFaceOfSize (PermutreeLattice s d') m) :=
  orientation_invariance_of_source_forcing source_forcing_forward d k hk

#check quotient_faces_equiv_diagrams
#check philippe_pilaud_conj76
#print axioms quotient_faces_equiv_diagrams
#print axioms philippe_pilaud_conj76

end Permutree
```

