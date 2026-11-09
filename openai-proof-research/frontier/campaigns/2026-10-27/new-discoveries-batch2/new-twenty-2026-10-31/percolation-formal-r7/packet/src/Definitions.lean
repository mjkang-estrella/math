import Std
namespace Percolation
set_option autoImplicit false
abbrev size (q : Nat) := q*q+q+1
abbrev Points (q : Nat) := Fin (size q)
abbrev Infection (q : Nat) := Points q → Bool
def card {α : Type} (xs : List α) (p : α → Bool) : Nat := (xs.filter p).length
structure Plane (q : Nat) where
  nontrivial : 2 ≤ q
  inc : Points q → Points q → Bool
  line_degree : ∀ l, card (List.finRange (size q)) (fun p => inc p l) = q+1
  point_degree : ∀ p, card (List.finRange (size q)) (fun l => inc p l) = q+1
  join : ∀ p p', p ≠ p' → card (List.finRange (size q)) (fun l => inc p l && inc p' l) = 1
  meet : ∀ l l', l ≠ l' → card (List.finRange (size q)) (fun p => inc p l && inc p l') = 1
  quadrangle : ∃ a b c d : Points q,
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    ∀ l, card [a,b,c,d] (fun p => inc p l) ≤ 2

def Subset {q : Nat} (a b : Infection q) : Prop := ∀ p, a p = true → b p = true
def Full {q : Nat} (a : Infection q) : Prop := ∀ p, a p = true
def countOn {q : Nat} (P : Plane q) (a : Infection q) (l : Points q) : Nat :=
  card (List.finRange (size q)) (fun p => a p && P.inc p l)
def step {q : Nat} (P : Plane q) (r : Nat) (a : Infection q) : Infection q := fun p =>
  a p || (List.finRange (size q)).any (fun l => P.inc p l && decide (r ≤ countOn P a l))
def rounds {q : Nat} (P : Plane q) (r : Nat) (a : Infection q) (n : Nat) : Infection q :=
  Nat.rec a (fun _ state => step P r state) n
def Percolates {q : Nat} (P : Plane q) (r : Nat) (a : Infection q) : Prop := ∃ n, Full (rounds P r a n)
def Minimal {q : Nat} (P : Plane q) (r : Nat) (a : Infection q) : Prop :=
  Percolates P r a ∧ ∀ b, Subset b a → b ≠ a → ¬ Percolates P r b
def TimeIs {q : Nat} (P : Plane q) (r : Nat) (a : Infection q) (t : Nat) : Prop :=
  Full (rounds P r a t) ∧ ∀ k, k < t → ¬ Full (rounds P r a k)
theorem exists_time {q : Nat} (P : Plane q) (r : Nat) (a : Infection q)
    (h : Percolates P r a) : ∃ t, TimeIs P r a t := by
  classical
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases he : ∃ k, k < n ∧ Full (rounds P r a k)
    · obtain ⟨k, hk, hf⟩ := he
      exact ih k hk hf
    · exact ⟨n, hn, fun k hk hf => he ⟨k, hk, hf⟩⟩
noncomputable def time {q : Nat} (P : Plane q) (r : Nat) (a : Infection q)
    (h : Percolates P r a) : Nat := Classical.choose (exists_time P r a h)
theorem time_is_least {q : Nat} (P : Plane q) (r : Nat) (a : Infection q)
    (h : Percolates P r a) : TimeIs P r a (time P r a h) :=
  Classical.choose_spec (exists_time P r a h)
theorem time_unique {q : Nat} (P : Plane q) (r : Nat) (a : Infection q)
    (hp : Percolates P r a) (t : Nat) (ht : TimeIs P r a t) : time P r a hp = t := by
  have hl := time_is_least P r a hp
  have h1 : ¬ time P r a hp < t := fun h => ht.2 _ h hl.1
  have h2 : ¬ t < time P r a hp := fun h => hl.2 _ h ht.1
  omega

theorem step_of_full {q : Nat} (P : Plane q) (r : Nat) (a : Infection q)
    (h : Full a) : step P r a = a := by
  funext p
  simp [step, h p]

theorem percolates_iff_full_stable {q : Nat} (P : Plane q) (r : Nat) (a : Infection q) :
    Percolates P r a ↔ ∃ n, Full (rounds P r a n) ∧
      rounds P r a n = rounds P r a (n+1) := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, hn, (step_of_full P r _ hn).symm⟩
  · rintro ⟨n, hn, _⟩
    exact ⟨n, hn⟩
def Conjecture20 : Prop := ∀ (q : Nat) (P : Plane q) (r : Nat),
  4 ≤ r → r ≤ q → ∃ a, Minimal P r a ∧ TimeIs P r a 2

theorem card_mono {α : Type} (xs : List α) (f g : α → Bool)
    (h : ∀ x, f x = true → g x = true) : card xs f ≤ card xs g := by
  induction xs with
  | nil => simp [card]
  | cons x xs ih =>
    have hx := h x
    simp only [card, List.filter_cons] at *
    cases hf : f x <;> cases hg : g x <;> simp_all
    omega

theorem step_mono {q : Nat} (P : Plane q) (r : Nat) {a b : Infection q}
    (h : Subset a b) : Subset (step P r a) (step P r b) := by
  intro p hp
  simp only [step, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at *
  rcases hp with hp | ⟨l, hl, hi, hn⟩
  · exact Or.inl (h p hp)
  · right
    refine ⟨l, hl, hi, Nat.le_trans hn ?_⟩
    apply card_mono
    intro x hx
    simp only [Bool.and_eq_true] at *
    exact ⟨h x hx.1, hx.2⟩

theorem rounds_mono {q : Nat} (P : Plane q) (r : Nat) {a b : Infection q}
    (h : Subset a b) (n : Nat) : Subset (rounds P r a n) (rounds P r b n) := by
  induction n with
  | zero => exact h
  | succ n ih => exact step_mono P r ih

theorem rounds_fixed {q : Nat} (P : Plane q) (r : Nat) (b : Infection q)
    (h : step P r b = b) (n : Nat) : rounds P r b n = b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change step P r (rounds P r b n) = b
    rw [ih, h]

theorem separator_blocks {q : Nat} (P : Plane q) (r : Nat) (a b : Infection q)
    (hab : Subset a b) (hfix : step P r b = b) (v : Points q) (hv : b v = false) :
    ¬ Percolates P r a := by
  rintro ⟨n, hn⟩
  have hm := rounds_mono P r hab n v (hn v)
  rw [rounds_fixed P r b hfix n, hv] at hm
  contradiction

theorem minimal_from_separators {q : Nat} (P : Plane q) (r : Nat) (a : Infection q)
    (hp : Percolates P r a)
    (hs : ∀ v, a v = true → ∃ b : Infection q,
      (∀ p, p ≠ v → a p = true → b p = true) ∧ step P r b = b ∧ b v = false) :
    Minimal P r a := by
  refine ⟨hp, ?_⟩
  intro c hca hne hc
  have hv : ∃ v, a v = true ∧ c v = false := by
    classical
    apply Classical.byContradiction
    intro h
    apply hne
    funext p
    have hh := hca p
    have hn : ¬ (a p = true ∧ c p = false) := fun hp => h ⟨p, hp⟩
    cases ha : a p <;> cases hb : c p <;> simp_all
  obtain ⟨v, ha, hv⟩ := hv
  obtain ⟨b, hb, hfix, hvb⟩ := hs v ha
  apply separator_blocks P r c b ?_ hfix v hvb hc
  intro p hp
  apply hb p
  · intro heq
    subst p
    simp_all
  · exact hca p hp
end Percolation
