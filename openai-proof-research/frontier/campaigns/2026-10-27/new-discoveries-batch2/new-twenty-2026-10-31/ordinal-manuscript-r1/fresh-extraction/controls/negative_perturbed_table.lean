import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# A six-point counterexample to the majorization conjecture for ordinal spaces (MathDB 366371)

Source: K. Keller and E. Petrov, *Ordinal spaces*, arXiv:2412.17391v1: Definition 1.1 (ordinal
space), the embedding conditions (7.1)–(7.3), Definition 7.1 (majorization property) and
Conjecture 7.4:

> Let `(X, δ)` be an ordinal space with `|X| = n ∈ ℕ⁺` and let there exist an enumeration
> `x₁, …, xₙ` of the points of `X` satisfying the majorization property. Then `X ↪ ℝ¹`.

We give an ordinal space on six points, whose identity enumeration has the majorization property,
which is not embeddable in `ℝ¹`.
-/

open Finset

namespace OrdinalSpaces366371

/-! ### Definitions from the source -/

/-- Definition 1.1: `δ x y z w` records whether `δ(x,y) <, =, > δ(z,w)`. -/
structure IsOrdinalSpace {X : Type} (δ : X → X → X → X → Ordering) : Prop where
  ax_i : ∀ x y, δ x y x y = .eq
  ax_ii : ∀ x y z w, δ x y z w = δ y x z w ∧ δ x y z w = δ x y w z
  ax_iii : ∀ x y z w, δ x y z w = (δ z w x y).swap
  ax_iv : ∀ x y u v z w, δ x y u v = .eq → δ u v z w = .eq → δ x y z w = .eq
  ax_v : ∀ x y u v z w, δ x y u v = .lt → δ u v z w ≠ .gt → δ x y z w = .lt
  ax_vi : ∀ x y u v z w, δ x y u v ≠ .gt → δ u v z w = .lt → δ x y z w = .lt
  ax_vii : ∀ x z w, (z ≠ w → δ x x z w = .lt) ∧ (z = w → δ x x z w = .eq)

/-- Embeddability `X ↪ ℝ¹`, conditions (7.1)–(7.3), with the Euclidean metric `|s - t|` on `ℝ`. -/
def EmbeddableInLine {X : Type} (δ : X → X → X → X → Ordering) : Prop :=
  ∃ Φ : X → ℝ, ∀ x y z w : X,
    (δ x y z w = .lt ↔ |Φ x - Φ y| < |Φ z - Φ w|) ∧
    (δ x y z w = .eq ↔ |Φ x - Φ y| = |Φ z - Φ w|) ∧
    (δ x y z w = .gt ↔ |Φ x - Φ y| > |Φ z - Φ w|)

section Majorization

variable {X : Type} (δ : X → X → X → X → Ordering) {n : ℕ} (e : Fin n → X)

/-- `(i₀,…,iₖ) ≺ (j₀,…,jₖ)` of Definition 7.1, for the enumeration `e`. -/
def Prec {k : ℕ} (I J : Fin (k + 1) → Fin n) : Prop :=
  ∃ π : Equiv.Perm (Fin k),
    (∀ l : Fin k, δ (e (I l.castSucc)) (e (I l.succ)) (e (J (π l).castSucc)) (e (J (π l).succ)) ≠ .gt) ∧
    ¬ (∀ l : Fin k, δ (e (I l.castSucc)) (e (I l.succ)) (e (J (π l).castSucc)) (e (J (π l).succ)) = .eq)

/-- `(i₀,…,iₖ) ∼ (j₀,…,jₖ)` of Definition 7.1, for the enumeration `e`. -/
def Sim {k : ℕ} (I J : Fin (k + 1) → Fin n) : Prop :=
  ∃ π : Equiv.Perm (Fin k),
    ∀ l : Fin k, δ (e (I l.castSucc)) (e (I l.succ)) (e (J (π l).castSucc)) (e (J (π l).succ)) = .eq

/-- The majorization property of Definition 7.1: for all `k ∈ ℕ⁺` and all nondecreasing index
tuples `(i₀ ≤ ⋯ ≤ iₖ)`, `(j₀ ≤ ⋯ ≤ jₖ)` in `𝓘ₙ`. -/
def HasMajorization : Prop :=
  ∀ k : ℕ, 0 < k → ∀ I J : Fin (k + 1) → Fin n, Monotone I → Monotone J →
    (Prec δ e I J → δ (e (I 0)) (e (I (Fin.last k))) (e (J 0)) (e (J (Fin.last k))) = .lt) ∧
    (Sim δ e I J → δ (e (I 0)) (e (I (Fin.last k))) (e (J 0)) (e (J (Fin.last k))) = .eq)

end Majorization

/-- Conjecture 7.4 of arXiv:2412.17391. -/
def MajorizationConjecture : Prop :=
  ∀ (X : Type) (δ : X → X → X → X → Ordering) (n : ℕ) (e : Fin n → X),
    0 < n → IsOrdinalSpace δ → Function.Bijective e → HasMajorization δ e → EmbeddableInLine δ

/-! ### The witness

Pairs of `Fin 6` ranked from smallest (`1`) to largest (`15`); the diagonal has value `0`. -/

/-- Values of the witness ordinal space. -/
def D (a b : Fin 6) : ℕ :=
  [[0, 5, 10, 13, 12, 15],
   [5, 0, 3, 6, 7, 14],
   [10, 3, 0, 1, 4, 11],
   [13, 6, 1, 0, 2, 9],
   [12, 7, 4, 2, 0, 8],
   [15, 14, 11, 9, 8, 0]].getD a.val [] |>.getD b.val 0

/-- The witness relation `δ(x,y) ? δ(z,w)`. -/
def δW (x y z w : Fin 6) : Ordering := compare (D x y) (D z w)

theorem D_symm : ∀ a b : Fin 6, D a b = D b a := by decide
theorem D_zero_iff : ∀ a b : Fin 6, D a b = 0 ↔ a = b := by decide
theorem D_le : ∀ a b : Fin 6, D a b ≤ 15 := by decide

theorem isOrdinalSpace_W : IsOrdinalSpace δW where
  ax_i x y := by simp [δW]
  ax_ii x y z w := ⟨by unfold δW; rw [D_symm x y], by unfold δW; rw [D_symm z w]⟩
  ax_iii x y z w := by simp only [δW]; exact (Nat.compare_swap _ _).symm
  ax_iv x y u v z w h1 h2 := by
    simp only [δW, compare_eq_iff_eq] at *; omega
  ax_v x y u v z w h1 h2 := by
    simp only [δW, compare_lt_iff_lt, ne_eq, compare_gt_iff_gt, not_lt] at *; omega
  ax_vi x y u v z w h1 h2 := by
    simp only [δW, compare_lt_iff_lt, ne_eq, compare_gt_iff_gt, not_lt] at *; omega
  ax_vii x z w := by
    simp only [δW]
    have h0 : D x x = 0 := (D_zero_iff x x).2 rfl
    rw [h0]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have : D z w ≠ 0 := fun h' => h ((D_zero_iff z w).1 h')
      exact compare_lt_iff_lt.2 (Nat.pos_of_ne_zero this)
    · subst h; rw [(D_zero_iff z z).2 rfl]; rfl

/-! ### Reduction of chains to strictly increasing lists -/

/-- Adjacent-pair count of `a :: l` (defined with the list recursor, so no compiler auxiliaries). -/
noncomputable def adjFrom (t : ℕ) (a : Fin 6) (l : List (Fin 6)) : ℕ :=
  List.rec (motive := fun _ => Fin 6 → ℕ) (fun _ => 0)
    (fun b _ ih a => (if t ≤ D a b then 1 else 0) + ih b) l a

/-- Number of adjacent pairs of a list whose `D`-value is at least `t`. -/
noncomputable def adj (t : ℕ) (l : List (Fin 6)) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a l _ => adjFrom t a l) l

theorem adj_cons_cons (t : ℕ) (a b : Fin 6) (l : List (Fin 6)) :
    adj t (a :: b :: l) = (if t ≤ D a b then 1 else 0) + adj t (b :: l) := rfl

theorem adj_single (t : ℕ) (a : Fin 6) : adj t [a] = 0 := rfl

/-- Removal of repeated consecutive entries from `a :: l`. -/
noncomputable def dd (a : Fin 6) (l : List (Fin 6)) : List (Fin 6) :=
  List.rec (motive := fun _ => Fin 6 → List (Fin 6)) (fun a => [a])
    (fun b _ ih a => if a = b then ih a else a :: ih b) l a

/-- Last entry of `a :: l`. -/
noncomputable def lastD (a : Fin 6) (l : List (Fin 6)) : Fin 6 :=
  List.rec (motive := fun _ => Fin 6 → Fin 6) (fun a => a) (fun b _ ih _ => ih b) l a

theorem dd_nil (a : Fin 6) : dd a [] = [a] := rfl
theorem dd_cons_eq (a b : Fin 6) (l : List (Fin 6)) :
    dd a (b :: l) = if a = b then dd a l else a :: dd b l := rfl
theorem dd_same (a : Fin 6) (l : List (Fin 6)) : dd a (a :: l) = dd a l := by
  simp [dd_cons_eq]
theorem dd_ne {a b : Fin 6} (h : ¬ a = b) (l : List (Fin 6)) : dd a (b :: l) = a :: dd b l := by
  simp [dd_cons_eq, h]
theorem lastD_nil (a : Fin 6) : lastD a [] = a := rfl
theorem lastD_cons (a b : Fin 6) (l : List (Fin 6)) : lastD a (b :: l) = lastD b l := rfl

theorem dd_cons (a : Fin 6) (l : List (Fin 6)) : ∃ r, dd a l = a :: r := by
  induction l generalizing a with
  | nil => exact ⟨[], rfl⟩
  | cons b l ih =>
    by_cases h : a = b
    · subst h; rw [dd_same]; exact ih a
    · rw [dd_ne h]; exact ⟨_, rfl⟩

theorem adj_dd (t : ℕ) (ht : 1 ≤ t) (a : Fin 6) (l : List (Fin 6)) :
    adj t (dd a l) = adj t (a :: l) := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
    by_cases h : a = b
    · subst h
      have hdd : dd a (a :: l) = dd a l := by rw [dd_same]
      have : ¬ t ≤ D a a := by rw [(D_zero_iff a a).2 rfl]; omega
      rw [hdd, ih, adj_cons_cons]; simp [this]
    · have hdd : dd a (b :: l) = a :: dd b l := by rw [dd_ne h]
      obtain ⟨r, hr⟩ := dd_cons b l
      rw [hdd, hr, adj_cons_cons, ← hr, ih, adj_cons_cons]

theorem lastD_dd (a : Fin 6) (l : List (Fin 6)) :
    ∀ r, dd a l = a :: r → lastD a r = lastD a l := by
  induction l generalizing a with
  | nil => intro r hr; rw [dd_nil, List.cons.injEq] at hr; rw [← hr.2]
  | cons b l ih =>
    intro r hr
    by_cases h : a = b
    · subst h; rw [dd_same] at hr; rw [ih a r hr, lastD_cons]
    · rw [dd_ne h, List.cons.injEq] at hr
      obtain ⟨r', hr'⟩ := dd_cons b l
      rw [← hr.2, hr', lastD_cons, ih b r' hr', lastD_cons]

theorem mem_dd (a : Fin 6) (l : List (Fin 6)) : ∀ x ∈ dd a l, x ∈ a :: l := by
  induction l generalizing a with
  | nil => intro x hx; rwa [dd_nil] at hx
  | cons b l ih =>
    intro x hx
    by_cases h : a = b
    · subst h; rw [dd_same] at hx
      rcases List.mem_cons.1 (ih a x hx) with h' | h'
      · exact List.mem_cons.2 (Or.inl h')
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h')
    · rw [dd_ne h] at hx
      rcases List.mem_cons.1 hx with h' | h'
      · exact List.mem_cons.2 (Or.inl h')
      · exact List.mem_cons_of_mem _ (ih b x h')

theorem pairwise_dd (a : Fin 6) (l : List (Fin 6)) :
    (a :: l).Pairwise (· ≤ ·) → (dd a l).Pairwise (· < ·) := by
  induction l generalizing a with
  | nil => intro _; rw [dd_nil]; exact List.pairwise_singleton _ _
  | cons b l ih =>
    intro hp
    by_cases h : a = b
    · subst h; rw [dd_same]
      apply ih
      exact List.Pairwise.sublist (List.Sublist.cons_cons _ (List.sublist_cons_self _ _)) hp
    · rw [dd_ne h]
      have hab : a < b := lt_of_le_of_ne (List.rel_of_pairwise_cons hp (List.mem_cons_self ..)) h
      refine List.Pairwise.cons (fun x hx => ?_) (ih b hp.of_cons)
      rcases List.mem_cons.1 (mem_dd b l x hx) with h' | h'
      · rw [h']; exact hab
      · exact lt_of_lt_of_le hab (List.rel_of_pairwise_cons hp.of_cons h')

/-- Counting chain pieces of value at least `t` equals counting adjacent pairs of `List.ofFn`. -/
theorem sum_pieces_eq_adj (t : ℕ) : ∀ (k : ℕ) (I : Fin (k + 1) → Fin 6),
    (∑ l : Fin k, if t ≤ D (I l.castSucc) (I l.succ) then 1 else 0) = adj t (List.ofFn I)
  | 0, I => by simp; rfl
  | k + 1, I => by
    have ih := sum_pieces_eq_adj t k (fun i => I i.succ)
    rw [Fin.sum_univ_succ, List.ofFn_succ (f := I), List.ofFn_succ (f := fun i => I i.succ),
      adj_cons_cons, ← List.ofFn_succ (f := fun i => I i.succ), ← ih]
    rfl

theorem lastD_ofFn : ∀ (k : ℕ) (I : Fin (k + 1) → Fin 6),
    lastD (I 0) (List.ofFn fun i : Fin k => I i.succ) = I (Fin.last k)
  | 0, I => rfl
  | k + 1, I => by
    rw [List.ofFn_succ, lastD_cons]
    exact lastD_ofFn k (fun i => I i.succ)

/-- The reduced (strictly increasing) list of a chain. -/
noncomputable def red {k : ℕ} (I : Fin (k + 1) → Fin 6) : List (Fin 6) :=
  dd (I 0) (List.ofFn fun i : Fin k => I i.succ)

theorem red_mem_sublists {k : ℕ} (I : Fin (k + 1) → Fin 6) (hI : Monotone I) :
    red I ∈ (List.finRange 6).sublists := by
  have hp : (I 0 :: List.ofFn fun i : Fin k => I i.succ).Pairwise (· ≤ ·) := by
    rw [← List.ofFn_succ (f := I)]
    exact List.pairwise_ofFn.2 (fun i j hij => hI hij.le)
  have hlt := pairwise_dd _ _ hp
  rw [List.mem_sublists]
  have hsub : red I ⊆ List.finRange 6 := fun x _ => List.mem_finRange x
  exact List.sublist_of_subperm_of_pairwise (r := (· ≤ ·))
    (List.subperm_of_subset hlt.nodup hsub)
    (hlt.imp le_of_lt) (List.pairwise_le_finRange 6)

theorem adj_red {k : ℕ} (I : Fin (k + 1) → Fin 6) (t : ℕ) (ht : 1 ≤ t) :
    (∑ l : Fin k, if t ≤ D (I l.castSucc) (I l.succ) then 1 else 0) = adj t (red I) := by
  rw [sum_pieces_eq_adj, red, adj_dd t ht, ← List.ofFn_succ]

/-! ### The finite check over strictly increasing lists -/

/-- Boolean form of the majorization requirement for two reduced lists. -/
noncomputable def okB : List (Fin 6) → List (Fin 6) → Bool
  | a :: r, b :: s =>
    let A := a :: r; let B := b :: s
    !((List.range' 1 15).all fun t => decide (adj t A ≤ adj t B)) ||
      ((!((List.range' 1 15).any fun t => decide (adj t A < adj t B)) ||
          decide (D a (lastD a r) < D b (lastD b s))) &&
       (!((List.range' 1 15).all fun t => decide (adj t A = adj t B)) ||
          decide (D a (lastD a r) = D b (lastD b s))))
  | _, _ => true

theorem finite_check :
    ((List.finRange 6).sublists.all fun A => (List.finRange 6).sublists.all fun B => okB A B) = true := by
  decide +kernel

end OrdinalSpaces366371
