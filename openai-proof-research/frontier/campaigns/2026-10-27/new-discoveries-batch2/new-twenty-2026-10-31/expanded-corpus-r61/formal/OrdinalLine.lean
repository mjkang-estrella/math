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
  [[0, 5, 10, 12, 13, 15],
   [5, 0, 3, 6, 7, 14],
   [10, 3, 0, 1, 4, 11],
   [12, 6, 1, 0, 2, 9],
   [13, 7, 4, 2, 0, 8],
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

/-! ### Majorization for the witness -/

theorem cmp_ne_gt {a b : ℕ} : compare a b ≠ .gt ↔ a ≤ b := by
  rw [ne_eq, compare_gt_iff_gt, not_lt]

/-- Counting comparison obtained from a termwise-dominating permutation. -/
theorem count_le {k : ℕ} (f g : Fin k → ℕ) (π : Equiv.Perm (Fin k)) (h : ∀ l, f l ≤ g (π l))
    (t : ℕ) : (univ.filter fun l => t ≤ f l).card ≤ (univ.filter fun l => t ≤ g l).card := by
  apply card_le_card_of_injOn π
  · intro l hl
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hl ⊢
    exact le_trans hl (h l)
  · exact π.injective.injOn

theorem count_lt {k : ℕ} (f g : Fin k → ℕ) (π : Equiv.Perm (Fin k)) (h : ∀ l, f l ≤ g (π l))
    (l0 : Fin k) (h0 : f l0 < g (π l0)) :
    (univ.filter fun l => g (π l0) ≤ f l).card < (univ.filter fun l => g (π l0) ≤ g l).card := by
  set t := g (π l0)
  have himg : ((univ.filter fun l => t ≤ f l).image π) ⊂ (univ.filter fun l => t ≤ g l) := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨π l0, by simp [t], fun hm => ?_⟩
      obtain ⟨l, hl, hl'⟩ := Finset.mem_image.1 hm
      have := π.injective hl'
      subst this
      simp only [mem_filter, mem_univ, true_and] at hl
      omega
    · intro m hm
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hm
      simp only [mem_filter, mem_univ, true_and] at hl ⊢
      exact le_trans hl (h l)
  have := Finset.card_lt_card himg
  rwa [Finset.card_image_of_injective _ π.injective] at this

theorem card_eq_sum {k : ℕ} (f : Fin k → ℕ) (t : ℕ) :
    (univ.filter fun l => t ≤ f l).card = ∑ l : Fin k, if t ≤ f l then 1 else 0 := by
  rw [Finset.card_filter]

theorem okB_spec (A B : List (Fin 6)) (hA : A ∈ (List.finRange 6).sublists)
    (hB : B ∈ (List.finRange 6).sublists) : okB A B = true := by
  have := finite_check
  rw [List.all_eq_true] at this
  have := this A hA
  rw [List.all_eq_true] at this
  exact this B hB

theorem majorization_W : HasMajorization δW (id : Fin 6 → Fin 6) := by
  intro k _ I J hI hJ
  -- piece values
  set f : Fin k → ℕ := fun l => D (I l.castSucc) (I l.succ) with hf
  set g : Fin k → ℕ := fun l => D (J l.castSucc) (J l.succ) with hg
  have hcI : ∀ t, 1 ≤ t → (univ.filter fun l => t ≤ f l).card = adj t (red I) := by
    intro t ht; rw [card_eq_sum, ← adj_red I t ht]
  have hcJ : ∀ t, 1 ≤ t → (univ.filter fun l => t ≤ g l).card = adj t (red J) := by
    intro t ht; rw [card_eq_sum, ← adj_red J t ht]
  have hok := okB_spec (red I) (red J) (red_mem_sublists I hI) (red_mem_sublists J hJ)
  obtain ⟨rI, hrI⟩ := dd_cons (I 0) (List.ofFn fun i : Fin k => I i.succ)
  obtain ⟨rJ, hrJ⟩ := dd_cons (J 0) (List.ofFn fun i : Fin k => J i.succ)
  have hlI : lastD (I 0) rI = I (Fin.last k) := by
    rw [lastD_dd _ _ rI hrI, lastD_ofFn]
  have hlJ : lastD (J 0) rJ = J (Fin.last k) := by
    rw [lastD_dd _ _ rJ hrJ, lastD_ofFn]
  have hredI : red I = I 0 :: rI := hrI
  have hredJ : red J = J 0 :: rJ := hrJ
  rw [hredI, hredJ] at hok; rw [hredI] at hcI; rw [hredJ] at hcJ
  simp only [okB, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.all_eq_false,
    List.any_eq_false, decide_eq_true_eq, Bool.and_eq_true, List.mem_range'_1,
    hlI, hlJ] at hok
  simp only [id, δW]
  constructor
  · rintro ⟨π, hle, hne⟩
    have hle' : ∀ l, f l ≤ g (π l) := fun l => cmp_ne_gt.1 (hle l)
    simp only [not_forall] at hne
    obtain ⟨l0, hl0⟩ := hne
    have hlt0 : f l0 < g (π l0) := lt_of_le_of_ne (hle' l0) (fun h => hl0 (compare_eq_iff_eq.2 h))
    have hdom : ∀ t, 1 ≤ t ∧ t < 1 + 15 → adj t (I 0 :: rI) ≤ adj t (J 0 :: rJ) := by
      intro t ht; rw [← hcI t ht.1, ← hcJ t ht.1]; exact count_le f g π hle' t
    have hpos : 1 ≤ g (π l0) := by omega
    have hbd : g (π l0) < 1 + 15 := by
      show D (J (π l0).castSucc) (J (π l0).succ) < 1 + 15
      have := D_le (J (π l0).castSucc) (J (π l0).succ); omega
    have hstrict : adj (g (π l0)) (I 0 :: rI) < adj (g (π l0)) (J 0 :: rJ) := by
      rw [← hcI _ hpos, ← hcJ _ hpos]; exact count_lt f g π hle' l0 hlt0
    rcases hok with hok | ⟨hok1, _⟩
    · obtain ⟨t, ht, hbad⟩ := hok; exact absurd (hdom t ht) hbad
    · rcases hok1 with hok1 | hok1
      · exact absurd hstrict (hok1 _ ⟨hpos, hbd⟩)
      · exact compare_lt_iff_lt.2 hok1
  · rintro ⟨π, heq⟩
    have heq' : ∀ l, f l = g (π l) := fun l => compare_eq_iff_eq.1 (heq l)
    have hge : ∀ m, g m = f (π.symm m) := fun m => by rw [heq']; simp
    have hdom : ∀ t, 1 ≤ t ∧ t < 1 + 15 → adj t (I 0 :: rI) ≤ adj t (J 0 :: rJ) := by
      intro t ht; rw [← hcI t ht.1, ← hcJ t ht.1]
      exact count_le f g π (fun l => (heq' l).le) t
    have hall : ∀ t, 1 ≤ t ∧ t < 1 + 15 → adj t (I 0 :: rI) = adj t (J 0 :: rJ) := by
      intro t ht
      refine le_antisymm (hdom t ht) ?_
      rw [← hcI t ht.1, ← hcJ t ht.1]
      exact count_le g f π.symm (fun m => (hge m).le) t
    rcases hok with hok | ⟨_, hok2⟩
    · obtain ⟨t, ht, hbad⟩ := hok; exact absurd (hdom t ht) hbad
    · rcases hok2 with hok2 | hok2
      · obtain ⟨t, ht, hbad⟩ := hok2; exact absurd (hall t ht) hbad
      · exact compare_eq_iff_eq.2 hok2

/-! ### Non-embeddability -/

/-- The core linear contradiction once the six points are known to lie in increasing order. -/
theorem core (a : Fin 6 → ℝ) (h05 : a 0 < a 5)
    (hlt : ∀ x y z w : Fin 6, D x y < D z w → |a x - a y| < |a z - a w|) : False := by
  have hd : ∀ {s t : ℝ}, s < t → |s - t| = t - s := fun h => by
    rw [abs_sub_comm, abs_of_pos (by linarith)]
  have h05' : |a 0 - a 5| = a 5 - a 0 := hd h05
  -- every point lies strictly between `a 0` and `a 5`
  have key : ∀ x : Fin 6, x ≠ 0 → x ≠ 5 → D 0 x < D 0 5 ∧ D x 5 < D 0 5 := by decide
  have between : ∀ x : Fin 6, x ≠ 0 → x ≠ 5 → a 0 < a x ∧ a x < a 5 := by
    intro x hx0 hx5
    have h1 := hlt 0 x 0 5 (key x hx0 hx5).1
    have h2 := hlt x 5 0 5 (key x hx0 hx5).2
    rw [h05'] at h1 h2
    have := abs_lt.1 h2
    have := (abs_lt.1 h1)
    constructor <;> linarith
  obtain ⟨b1, c1⟩ := between 1 (by decide) (by decide)
  obtain ⟨b2, c2⟩ := between 2 (by decide) (by decide)
  obtain ⟨b3, c3⟩ := between 3 (by decide) (by decide)
  obtain ⟨b4, c4⟩ := between 4 (by decide) (by decide)
  -- the order is forced by the distances from point 0
  have o12 := hlt 0 1 0 2 (by decide)
  have o23 := hlt 0 2 0 3 (by decide)
  have o34 := hlt 0 3 0 4 (by decide)
  rw [hd b1, hd b2] at o12; rw [hd b2, hd b3] at o23; rw [hd b3, hd b4] at o34
  have e12 : a 1 < a 2 := by linarith
  have e23 : a 2 < a 3 := by linarith
  have e34 : a 3 < a 4 := by linarith
  -- the five comparisons whose sum is `0 < 0`
  have q1 := hlt 2 3 3 4 (by decide)
  have q2 := hlt 1 2 2 4 (by decide)
  have q3 := hlt 0 1 1 3 (by decide)
  have q4 := hlt 1 4 4 5 (by decide)
  have q5 := hlt 3 5 0 2 (by decide)
  rw [hd e23, hd e34] at q1
  rw [hd e12, hd (e23.trans e34)] at q2
  rw [hd b1, hd (e12.trans e23)] at q3
  rw [hd ((e12.trans e23).trans e34), hd c4] at q4
  rw [hd c3, hd b2] at q5
  linarith

theorem not_embeddable_W : ¬ EmbeddableInLine δW := by
  rintro ⟨Φ, hΦ⟩
  have hlt : ∀ x y z w : Fin 6, D x y < D z w → |Φ x - Φ y| < |Φ z - Φ w| :=
    fun x y z w h => ((hΦ x y z w).1).1 (compare_lt_iff_lt.2 h)
  have hne : Φ 0 ≠ Φ 5 := by
    intro h
    have := hlt 0 0 0 5 (by decide)
    simp [h] at this
  rcases lt_or_gt_of_ne hne with h | h
  · exact core Φ h hlt
  · refine core (fun i => - Φ i) (by simpa using h) (fun x y z w hxy => ?_)
    have e : ∀ s t : ℝ, |-s - -t| = |s - t| := fun s t => by rw [neg_sub_neg, abs_sub_comm]
    show |-Φ x - -Φ y| < |-Φ z - -Φ w|
    rw [e, e]; exact hlt x y z w hxy

/-! ### Main result -/

/-- The witness: a six-point ordinal space whose identity enumeration has the majorization
property but which is not embeddable in `ℝ¹`. -/
theorem witness :
    IsOrdinalSpace δW ∧ Function.Bijective (id : Fin 6 → Fin 6) ∧
      HasMajorization δW (id : Fin 6 → Fin 6) ∧ ¬ EmbeddableInLine δW :=
  ⟨isOrdinalSpace_W, Function.bijective_id, majorization_W, not_embeddable_W⟩

/-- Conjecture 7.4 of arXiv:2412.17391 is false. -/
theorem not_majorizationConjecture : ¬ MajorizationConjecture := fun h =>
  not_embeddable_W (h (Fin 6) δW 6 id (by decide) isOrdinalSpace_W Function.bijective_id
    majorization_W)

end OrdinalSpaces366371
