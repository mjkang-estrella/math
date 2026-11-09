set_option autoImplicit false
set_option warningAsError true

/-!
# Literal source definitions for Conjecture 8.8 of MathDB 364119

Primary source: Cerbai, Claesson, Ernst, Golab, *Pattern-avoiding Cayley
permutations via combinatorial species*, Australasian Journal of Combinatorics
94(2) (2026), 267-299. Definition p.280: a Cayley permutation `w` contains a
Cayley permutation `p` if some strictly increasing tuple of distinct positions
of `w` extracts a subsequence that is order-isomorphic to `p`, i.e. for every
pair of pattern positions `a < b` both the strict comparison and the equality
(tie) of the extracted letters agree with the corresponding pattern letters in
both directions. Conjecture 8.8, p.296: if `max(p) <= max(q)` then the number
of packed length-n words avoiding `p` is at least the number avoiding `q`.

The counted universe uses the explicit finite alphabet `{1, ..., n}`. Every
packed word of length n has all letters at most n (`maxL_le_length`), so the
finite-alphabet enumeration `allWords n n` captures exactly the source Cayley
words of length n (`allWords_sound`, `allWords_complete`), and
`CayAvoiderList n p` captures exactly the source avoiders with no duplicates
(`nodup_CayAvoiderList`, `mem_CayAvoiderList_iff`). No translation step is
left unproved: the computational predicates `packedB` and `containsB` are
proved equivalent to the literal source predicates `Packed` and `Contains` in
`packedB_iff` and `containsB_iff`.
-/

namespace Cayley

/-! ## Source-literal predicates -/

/-- Largest letter of a word, 0 for the empty word. -/
def maxL (w : List Nat) : Nat := w.foldr max 0

/-- Packed positive word: nonempty, all letters at least 1, and every value
from 1 up to the largest letter occurs; the letter set is `{1, ..., max}`. -/
def Packed (w : List Nat) : Prop :=
  w ≠ [] ∧ (∀ x ∈ w, 1 ≤ x) ∧ ∀ k, 1 ≤ k → k ≤ maxL w → k ∈ w

/-- Literal strict-index order-isomorphic containment. The witness maps pattern
positions to strictly increasing (hence distinct) word positions; for every
pair of pattern positions `a < b` both the strict order and the equality of the
extracted letters match the pattern in both directions. -/
def Contains (p w : List Nat) : Prop :=
  ∃ f : Fin p.length → Fin w.length,
    (∀ a b : Fin p.length, a < b → f a < f b) ∧
    ∀ a b : Fin p.length, a < b →
      ((p.getD a.val 0 < p.getD b.val 0) ↔ (w.getD (f a).val 0 < w.getD (f b).val 0)) ∧
      ((p.getD a.val 0 = p.getD b.val 0) ↔ (w.getD (f a).val 0 = w.getD (f b).val 0))

/-- Avoidance in the literal source sense. -/
def Avoids (p w : List Nat) : Prop := ¬ Contains p w

/-! ## Computations -/

/-- All length-n lists with letters in `{1, ..., m}`. -/
def allWords : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | _ + 1, 0 => []
  | n + 1, m + 1 => (allWords n (m + 1)).flatMap
      fun w => (List.range (m + 1)).map fun a => (a + 1) :: w

/-- All position subsequences (as value lists) of a word. -/
def subseqsOf : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => subseqsOf xs ++ (subseqsOf xs).map fun s => x :: s

/-- Pairwise order-and-tie agreement of two words of equal length. -/
def isoCheck (p s : List Nat) : Bool :=
  p.length == s.length &&
    ((List.range p.length).all fun i =>
      (List.range p.length).all fun j =>
        decide (i < j →
          ((p.getD i 0 < p.getD j 0) ↔ (s.getD i 0 < s.getD j 0)) ∧
          ((p.getD i 0 = p.getD j 0) ↔ (s.getD i 0 = s.getD j 0))))

/-- Decidable containment by subsequence enumeration. -/
def containsB (p w : List Nat) : Bool := (subseqsOf w).any (isoCheck p)

/-- Decidable packedness. -/
def packedB (w : List Nat) : Bool :=
  decide (w ≠ []) && w.all (fun x => decide (1 ≤ x)) &&
    (List.range (maxL w)).all (fun k => w.contains (k + 1))

/-- Single-pass duplicate removal with an accumulator. -/
def dedupAux {α : Type} [BEq α] (acc : List α) : List α → List α
  | [] => acc
  | x :: xs => if acc.contains x then dedupAux acc xs else dedupAux (x :: acc) xs

def dedup {α : Type} [BEq α] (l : List α) : List α := dedupAux [] l

/-- Packed length-n avoiders of `p` over the explicit finite alphabet
`{1, ..., n}`, as a duplicate-free list. -/
def CayAvoiderList (n : Nat) (p : List Nat) : List (List Nat) :=
  dedup ((allWords n n).filter (fun W => packedB W && !(containsB p W)))

/-- The literal count `|Cay_n(p)|` over the explicit finite alphabet. -/
def CayCount (n : Nat) (p : List Nat) : Nat := (CayAvoiderList n p).length

/-- Literal scope of Conjecture 8.8: for all packed patterns `p`, `q` of equal
length with `max(p) <= max(q)`, and every word length `n`, the packed length-n
avoiders of `p` are at least as many as those of `q`. -/
def SourceClaim : Prop :=
  ∀ p q : List Nat, Packed p → Packed q → p.length = q.length → maxL p ≤ maxL q →
    ∀ n : Nat, CayCount n p ≥ CayCount n q

/-! ## Small `Fin` helpers -/

theorem fin_zero_lt_succ {k : Nat} (j : Fin k) : (⟨0, by omega⟩ : Fin (k + 1)) < j.succ := by
  refine Fin.lt_def.mpr ?_
  show (0 : Nat) < j.val + 1
  omega

theorem fin_zero_lt_of_val_pos {k : Nat} {i : Fin k} (h : 0 < i.val) :
    (⟨0, by omega⟩ : Fin k) < i := by
  refine Fin.lt_def.mpr ?_
  show (0 : Nat) < i.val
  omega

theorem fin_succ_lt_succ {k : Nat} {a b : Fin k} (h : a < b) : a.succ < b.succ := by
  refine Fin.lt_def.mpr ?_
  rw [Fin.val_succ, Fin.val_succ]
  exact Nat.succ_lt_succ (Fin.lt_def.mp h)

/-! ## Basic list and maximum lemmas -/

theorem maxL_cons (x : Nat) (xs : List Nat) : maxL (x :: xs) = max x (maxL xs) := rfl

theorem le_maxL {x : Nat} {w : List Nat} (hx : x ∈ w) : x ≤ maxL w := by
  induction w with
  | nil => exact absurd hx (List.not_mem_nil (a := x))
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hys
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hys) (Nat.le_max_right _ _)

theorem getD_of_lt {l : List Nat} (i : Nat) (h : i < l.length) : l.getD i 0 = l[i]'h := by
  induction l generalizing i with
  | nil => exact absurd h (Nat.not_lt_zero i)
  | cons x xs ih =>
    cases i with
    | zero => rw [List.getD_cons_zero, List.getElem_cons_zero]
    | succ i =>
      have hi : i < xs.length := by
        have := h
        simp only [List.length_cons] at this
        omega
      rw [List.getD_cons_succ, List.getElem_cons_succ x xs i (by simpa using h)]
      exact ih i hi

theorem filter_congr_pointwise {p q : Nat → Bool} {xs : List Nat}
    (h : ∀ y ∈ xs, p y = q y) : xs.filter p = xs.filter q := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.filter_cons, List.filter_cons,
      h x (List.mem_cons_self ..),
      ih fun y hy => h y (List.mem_cons_of_mem x hy)]

/[-- Filter at the head of a cons, by the head value. -]/
theorem filter_cons_true {α : Type} {p : α → Bool} {x : α} {xs : List α} (h : p x = true) :
    List.filter p (x :: xs) = x :: List.filter p xs := by
  rw [List.filter_cons, h]

theorem filter_cons_false {α : Type} {p : α → Bool} {x : α} {xs : List α} (h : p x = false) :
    List.filter p (x :: xs) = List.filter p xs := by
  rw [List.filter_cons, h]

/-- On a duplicate-free index list, a predicate that differs from `p` at one
point at most contributes at most one extra element to the filter. -/
theorem filter_extra_le {p q : Nat → Bool} {c : Nat} {l : List Nat} (hn : l.Nodup)
    (hagree : ∀ x ∈ l, (p x = q x) ∨ x = c) :
    (l.filter q).length ≤ (l.filter p).length + 1 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hxn, hxs⟩ := List.nodup_cons.mp hn
    have hagree' : ∀ y ∈ xs, (p y = q y) ∨ y = c := fun y hy =>
      hagree y (List.mem_cons_of_mem x hy)
    cases hp : p x with
    | false =>
      rw [filter_cons_false hp]
      cases hq : q x with
      | false =>
        rw [filter_cons_false hq]
        have h1 := ih hxs hagree'
        omega
      | true =>
        rcases hagree x (List.mem_cons_self ..) with heq | hxc
        · rw [heq] at hp; exact absurd hp (by simp)
        · have hpt : ∀ y ∈ xs, p y = q y := fun y hy => by
            rcases hagree y (List.mem_cons_of_mem x hy) with h1 | h2
            · exact h1
            · exact absurd ((hxc.trans h2.symm) ▸ hy) hxn
          rw [filter_cons_true hq, filter_congr_pointwise hpt]
          simp only [List.length_cons]
          exact Nat.le_refl _
    | true =>
      rw [filter_cons_true hp]
      cases hq : q x with
      | false =>
        rw [filter_cons_false hq]
        have h1 := ih hxs hagree'
        omega
      | true =>
        rw [filter_cons_true hq]
        simp only [List.length_cons]
        have h1 := ih hxs hagree'
        omega

/-- If `w` contains every value in `[1, m]` then `m ≤ w.length`. -/
theorem count_le_length (m : Nat) (w : List Nat) (h : ∀ j, 1 ≤ j → j ≤ m → j ∈ w) :
    m ≤ w.length := by
  have hbound : ∀ u : List Nat,
      ((List.range m).filter (fun j => u.contains (j + 1))).length ≤ u.length := by
    intro u
    induction u with
    | nil =>
      rw [List.filter_eq_nil_iff.mpr fun j _ => by simp]
      exact Nat.le_refl _
    | cons y ys ih =>
      have hnod : (List.range m).Nodup := List.nodup_range
      have hag : ∀ j ∈ List.range m,
          ((fun j => ys.contains (j + 1)) j =
            (fun j => (y :: ys).contains (j + 1)) j) ∨ j = y - 1 := by
        intro j hjm0
        have hjm : j < m := List.mem_range.mp hjm0
        by_cases hyj : j + 1 = y
        · exact Or.inr (by omega)
        · refine Or.inl ?_
          have hby : ((j + 1) == y) = false := by simpa using hyj
          simp only [List.contains_cons, hby, Bool.false_or]
      calc ((List.range m).filter (fun j => (y :: ys).contains (j + 1))).length
            ≤ ((List.range m).filter (fun j => ys.contains (j + 1))).length + 1 :=
            filter_extra_le hnod hag
        _ ≤ ys.length + 1 := by omega
  have hA : ((List.range m).filter (fun j => w.contains (j + 1))).length = m := by
    have hself := List.filter_eq_self.mpr fun j hj => by
      have hjm : j < m := List.mem_range.mp hj
      exact List.contains_iff_mem.mpr (h (j + 1) (by omega) (by omega))
    rw [hself, List.length_range]
  have hb := hbound w
  omega

/-- Every packed word has largest letter at most its length. -/
theorem maxL_le_length {w : List Nat} (hP : Packed w) : maxL w ≤ w.length := by
  obtain ⟨_, _, hsub⟩ := hP
  exact count_le_length (maxL w) w hsub

/-! ## The finite-alphabet enumeration -/

theorem allWords_sound {n m : Nat} {W : List Nat} (h : W ∈ allWords n m) :
    W.length = n ∧ ∀ x ∈ W, 1 ≤ x ∧ x ≤ m := by
  induction n generalizing m W with
  | zero =>
    simp only [allWords] at h
    obtain hW : W = [] := List.mem_singleton.mp h
    subst hW
    exact ⟨rfl, fun x hx => absurd hx (List.not_mem_nil (a := x))⟩
  | succ n ih =>
    cases m with
    | zero => simp [allWords] at h
    | succ m =>
      simp only [allWords] at h
      obtain ⟨w, hw, hW⟩ := List.mem_flatMap.mp h
      obtain ⟨a, ha, hWa⟩ := List.mem_map.mp hW
      obtain rfl : W = (a + 1) :: w := hWa.symm
      obtain ⟨hlen, hlet⟩ := ih hw
      refine ⟨?_, ?_⟩
      · show w.length + 1 = n + 1; rw [hlen]
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact ⟨by omega, by have := List.mem_range.mp ha; omega⟩
        · exact hlet x hx'

theorem allWords_complete {n m : Nat} {W : List Nat}
    (hlet : ∀ x ∈ W, 1 ≤ x ∧ x ≤ m) (hlen : W.length = n) : W ∈ allWords n m := by
  induction n generalizing m W with
  | zero =>
    cases W with
    | nil => simp [allWords]
    | cons x xs => simp at hlen
  | succ n ih =>
    cases W with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons x xs =>
      cases m with
      | zero =>
        obtain ⟨h1, h2⟩ := hlet x (List.mem_cons_self ..)
        omega
      | succ m =>
        obtain ⟨hx1, hxm⟩ := hlet x (List.mem_cons_self ..)
        have hxs : xs.length = n := by
          have := hlen
          simp only [List.length_cons] at this
          omega
        refine List.mem_flatMap.mpr ⟨xs, ih (m := m + 1)
          (fun y hy => hlet y (List.mem_cons_of_mem x hy)) hxs, ?_⟩
        refine List.mem_map.mpr ⟨x - 1, ?_, ?_⟩
        · simp only [List.mem_range]; omega
        · rw [show x - 1 + 1 = x by omega]

/-! ## Decidable packedness -/

theorem packedB_iff (w : List Nat) : packedB w = true ↔ Packed w := by
  constructor
  · intro h
    simp only [packedB, Bool.and_eq_true] at h
    obtain ⟨hne, hall, hrange⟩ := h
    refine ⟨decide_eq_true_iff.mp hne, List.all_eq_true.mp hall, ?_⟩
    intro k hk1 hk2
    exact List.contains_iff_mem.mp (hrange (k - 1) (List.mem_range.mpr (by omega)))
  · intro h
    obtain ⟨hne, h1, h2⟩ := h
    simp only [packedB, Bool.and_eq_true]
    refine ⟨decide_eq_true hne, ?_, ?_⟩
    · exact List.all_eq_true.mpr fun x hx => decide_eq_true (h1 x hx)
    · refine List.all_eq_true.mpr fun k hk => ?_
      have hk1 : k < maxL w := List.mem_range.mp hk
      exact List.contains_iff_mem.mpr (h2 (k + 1) (by omega) (by omega))

/-! ## Subsequences and decidable containment -/

theorem nil_mem_subseqsOf (w : List Nat) : [] ∈ subseqsOf w := by
  induction w with
  | nil => simp [subseqsOf]
  | cons x xs ih => simp only [subseqsOf]; exact List.mem_append.mpr (Or.inl ih)

theorem ofFn_length_zero {α : Type} {g : Fin 0 → α} : List.ofFn g = [] := by
  refine List.length_eq_zero_iff.mp ?_
  rw [List.length_ofFn]

theorem ofFn_congr {α : Type} {k : Nat} {g1 g2 : Fin k → α} (h : ∀ i, g1 i = g2 i) :
    List.ofFn g1 = List.ofFn g2 := by
  apply List.ext_getElem
  · rw [List.length_ofFn, List.length_ofFn]
  · intro i _ _
    rw [List.getElem_ofFn, List.getElem_ofFn, h]

/-- Front decomposition of `List.ofFn` over `Fin (k + 1)`. -/
theorem ofFn_front {α : Type} {k : Nat} (E : Fin (k + 1) → α) :
    List.ofFn E = E ⟨0, by omega⟩ :: List.ofFn (fun j : Fin k => E (Fin.succ j)) := by
  apply List.ext_getElem
  · rw [List.length_ofFn, List.length_cons, List.length_ofFn]
  · intro i h1 h2
    rw [List.getElem_ofFn, List.getElem_ofFn]
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi; simp
    · have hget := List.getElem_ofFn (α := α)
        (f := fun j : Fin k => E (Fin.succ j)) (i := i - 1)
        (by rw [List.length_ofFn]; omega)
      rw [hget]
      congr 1
      exact (Fin.succ_mk (i - 1) (i - 1 + 1) (by omega)).symm.trans
        (by congr 1; omega)

/-- Every member of `subseqsOf w` admits a strictly increasing position
witness with pointwise extraction. -/
theorem subseqsOf_extractable : ∀ (w s : List Nat), s ∈ subseqsOf w →
    ∃ f : Fin s.length → Fin w.length,
      (∀ a b : Fin s.length, a < b → (f a : Nat) < (f b : Nat)) ∧
      ∀ i : Fin s.length, w.getD (f i).val 0 = s.getD i.val 0 := by
  intro w
  induction w with
  | nil =>
    intro s h
    obtain hs : s = [] := by
      simp only [subseqsOf] at h
      exact List.mem_singleton.mp h
    subst hs
    exact ⟨fun i => i.elim0, fun a _ => a.elim0, fun i => i.elim0⟩
  | cons x xs ih =>
    intro s h
    simp only [subseqsOf] at h
    rcases List.mem_append.mp h with h1 | h1
    · obtain ⟨f, hmono, hval⟩ := ih s h1
      refine ⟨fun i => Fin.succ (f i), fun a b hab => fin_succ_lt_succ (hmono a b hab),
        fun i => by rw [List.getD_cons_succ]; exact hval i⟩
    · obtain ⟨s', hs', hEq⟩ := List.mem_map.mp h1
      obtain rfl : x :: s' = s := hEq
      refine ⟨Fin.cases (0 : Fin (xs.length + 1)) (fun j => Fin.succ (f j)), ?_, ?_⟩
      · intro a b hab
        rcases a with ⟨_ | i, _⟩
        · rcases b with ⟨_ | j, _⟩
          · exact absurd hab (by exact fun h => (Nat.lt_irrefl 0) h)
          · show ((Fin.cases (0 : Fin (xs.length + 1)) (fun j => Fin.succ (f j)) ⟨0, _⟩ :
                Fin (xs.length + 1)) : Nat) <
              ((Fin.cases (0 : Fin (xs.length + 1)) (fun j => Fin.succ (f j)) ⟨j + 1, _⟩ :
                Fin (xs.length + 1)) : Nat)
            rw [Fin.cases_zero, Fin.cases_succ, Fin.val_succ]
            exact Nat.succ_pos _
        · rcases b with ⟨_ | j, _⟩
          · exact absurd hab (by
              refine Fin.lt_def.mp ?_
              show (⟨i + 1, _⟩ : Fin (s'.length + 1)).val < (⟨0, _⟩ : Fin (s'.length + 1)).val
              omega)
          · show ((Fin.cases (0 : Fin (xs.length + 1)) (fun j => Fin.succ (f j)) ⟨i + 1, _⟩ :
                Fin (xs.length + 1)) : Nat) <
              ((Fin.cases (0 : Fin (xs.length + 1)) (fun j => Fin.succ (f j)) ⟨j + 1, _⟩ :
                Fin (xs.length + 1)) : Nat)
            rw [Fin.cases_succ, Fin.cases_succ, Fin.val_succ, Fin.val_succ]
            X using hmono (a := ⟨i + 1, by omega⟩) (b := ⟨j + 1, by omega⟩) hab)
      · intro i
        rcases i with ⟨_ | j, _⟩
        · show (x :: xs).getD _ 0 = (x :: s').getD _ 0
          rw [Fin.cases_zero, Fin.val_zero, List.getD_cons_zero, List.getD_cons_zero]
        · show (x :: xs).getD _ 0 = (x :: s').getD _ 0
          rw [Fin.cases_succ, Fin.val_succ, List.getD_cons_succ, List.getD_cons_succ]
          exact hval ⟨j, by omega⟩

/-- Every strictly-increasing extraction is a member of `subseqsOf w`. -/
theorem extract_mem_subseqsOf : ∀ (w : List Nat) (k : Nat) (f : Fin k → Fin w.length),
    (∀ a b : Fin k, a < b → (f a : Nat) < (f b : Nat)) →
    (List.ofFn fun i : Fin k => w.getD (f i).val 0) ∈ subseqsOf w := by
  intro w
  induction w with
  | nil =>
    intro k f _
    cases k with
    | zero => rw [ofFn_length_zero]; exact nil_mem_subseqsOf []
    | succ k => exact absurd (f ⟨0, Nat.succ_pos k⟩) fun x => (Fin.elim0 x : False)
  | cons x xs ih =>
    intro k f hmono
    by_cases h0 : (f ⟨0, Nat.succ_pos xs.length⟩).val = 0
    · cases k with
      | zero => rw [ofFn_length_zero]; exact nil_mem_subseqsOf xs
      | succ k' =>
        have hE : (List.ofFn fun i : Fin (k' + 1) => (x :: xs).getD (f i).val 0)
            = x :: List.ofFn (fun j : Fin k' => xs.getD ((f j.succ).val - 1) 0) := by
          rw [ofFn_front]
          refine congrArg _ ?_
          refine congr 1
          · show (x :: xs).getD (f ⟨0, _⟩).val 0 = x
            rw [h0, List.getD_cons_zero]
          · refine ofFn_congr fun j => ?_
            have hge1 : 1 ≤ (f j.succ).val := by
              have := hmono ⟨0, by omega⟩ j.succ (fin_zero_lt_succ j)
              rw [h0] at this
              omega
            show (x :: xs).getD (f j.succ).val 0 = xs.getD ((f j.succ).val - 1) 0
            rw [show (f j.succ).val = (f j.succ).val - 1 + 1 from by omega,
              List.getD_cons_succ]
        rw [hE]
        refine List.mem_append.mpr (Or.inr ?_)
        refine List.mem_map.mpr ⟨_, ?_, rfl⟩
        refine ih k' (fun j => ⟨(f j.succ).val - 1, ?_⟩) ?_
        · have := (f j.succ).isLt
          omega
        · intro a b hab
          show ((⟨(f a.succ).val - 1, _⟩ : Fin xs.length) : Nat) <
            ((⟨(f b.succ).val - 1, _⟩ : Fin xs.length) : Nat)
          have h2 := hmono a.succ b.succ (fin_succ_lt_succ hab)
          omega
    · have hall1 : ∀ i : Fin k, 1 ≤ (f i).val := by
        intro i
        rcases Nat.eq_zero_or_pos i.val with hi | hi
        · rw [hi] at h0; exact absurd rfl h0
        · have := hmono ⟨0, by omega⟩ i (fin_zero_lt_of_val_pos hi)
          omega
      have hE : (List.ofFn fun i : Fin k => (x :: xs).getD (f i).val 0)
          = List.ofFn (fun i : Fin k => xs.getD ((f i).val - 1) 0) := by
        refine ofFn_congr fun i => ?_
        show (x :: xs).getD (f i).val 0 = xs.getD ((f i).val - 1) 0
        rw [show (f i).val = (f i).val - 1 + 1 from by have := hall1 i; omega,
          List.getD_cons_succ]
      rw [hE]
      refine List.mem_append.mpr (Or.inl ?_)
      refine ih k (fun i => ⟨(f i).val - 1, by have := (f i).isLt; omega⟩) ?_
      intro a b hab
      show ((⟨(f a).val - 1, _⟩ : Fin xs.length) : Nat) <
        ((⟨(f b).val - 1, _⟩ : Fin xs.length) : Nat)
      have := hmono a b hab
      omega

/-- Pointwise extraction value of an `ofFn` list. -/
theorem ofFn_getD {α : Type} {k : Nat} (g : Fin k → α) {i : Nat} (h : i < k) :
    (List.ofFn g).getD i 0 = g ⟨i, h⟩ := by
  rw [getD_of_lt (i := i) (by rw [List.length_ofFn]; exact h),
    List.getElem_ofFn (by rw [List.length_ofFn]; exact h)]

/-- `isoCheck` accepts the canonical extraction of a strict position witness. -/
theorem isoCheck_ofFn {p w : List Nat} {f : Fin p.length → Fin w.length}
    (hcond : ∀ a b : Fin p.length, a < b →
      ((p.getD a.val 0 < p.getD b.val 0) ↔ (w.getD (f a).val 0 < w.getD (f b).val 0)) ∧
      ((p.getD a.val 0 = p.getD b.val 0) ↔ (w.getD (f a).val 0 = w.getD (f b).val 0))) :
    isoCheck p (List.ofFn fun i : Fin p.length => w.getD (f i).val 0) = true := by
  refine Bool.and_eq_true.mpr ⟨?_, ?_⟩
  · show p.length == (List.ofFn fun i : Fin p.length => w.getD (f i).val 0).length
    rw [List.length_ofFn]; exact beq_self_eq_true _
  · show ((List.range p.length).all fun i =>
        (List.range p.length).all fun j =>
          decide (i < j →
            ((p.getD i 0 < p.getD j 0) ↔
              (List.ofFn (fun i : Fin p.length => w.getD (f i).val 0)).getD i 0 <
                (List.ofFn (fun i : Fin p.length => w.getD (f i).val 0)).getD j 0) ∧
            ((p.getD i 0 = p.getD j 0) ↔
              (List.ofFn (fun i : Fin p.length => w.getD (f i).val 0)).getD i 0 =
                (List.ofFn (fun i : Fin p.length => w.getD (f i).val 0)).getD j 0)) = true
    refine List.all_eq_true.mpr fun i hi => List.all_eq_true.mpr fun j hj => ?_
    have hiL : i < p.length := List.mem_range.mp hi
    have hjL : j < p.length := List.mem_range.mp hj
    obtain ⟨hc1, hc2⟩ := hcond ⟨i, hiL⟩ ⟨j, hjL⟩ (by exact hiL ▸ hjL ▸ by omega)
    refine decide_eq_true ⟨?_, ?_⟩
    · intro _
      rw [ofFn_getD _ hiL, ofFn_getD _ hjL]
      exact hc1
    · intro _
      rw [ofFn_getD _ hiL, ofFn_getD _ hjL]
      exact hc2

/-- `containsB` decides the literal containment predicate. -/
theorem containsB_iff (p w : List Nat) : containsB p w = true ↔ Contains p w := by
  constructor
  · intro h
    obtain ⟨s, hs, hiso⟩ := List.any_eq_true.mp h
    obtain ⟨hlen, hpair⟩ := Bool.and_eq_true.mp hiso
    have hpl : p.length = s.length := by
      have := hlen
      simpa using this
    obtain ⟨f, hmono, hval⟩ := subseqsOf_extractable w s hs
    refine ⟨fun i => f ⟨i.val, by rw [hpl]; exact i.isLt⟩, ?_, ?_⟩
    · intro a b hab
      show ((f ⟨a.val, _⟩ : Fin s.length) : Nat) < ((f ⟨b.val, _⟩ : Fin s.length) : Nat)
      refine hmono ⟨a.val, _⟩ ⟨b.val, _⟩ ?_
      show (a : Nat) < (b : Nat)
      exact hab
    · intro a b hab
      obtain ⟨hp1, hp2⟩ := hpair a.val (List.mem_range.mpr a.isLt) b.val
        (List.mem_range.mpr b.isLt) (decide_eq_true (by omega))
      refine ⟨?_, ?_⟩
      · show (p.getD a.val 0 < p.getD b.val 0) ↔
            (w.getD (f ⟨a.val, _⟩).val 0 < w.getD (f ⟨b.val, _⟩).val 0)
        rw [← hval ⟨a.val, _⟩, ← hval ⟨b.val, _⟩]
        exact hp1
      · show (p.getD a.val 0 = p.getD b.val 0) ↔
            (w.getD (f ⟨a.val, _⟩).val 0 = w.getD (f ⟨b.val, _⟩).val 0)
        rw [← hval ⟨a.val, _⟩, ← hval ⟨b.val, _⟩]
        exact hp2
  · intro h
    obtain ⟨f, hmono, hcond⟩ := h
    exact List.any_eq_true.mpr ⟨List.ofFn (fun i : Fin p.length => w.getD (f i).val 0),
      extract_mem_subseqsOf w p.length f hmono, isoCheck_ofFn hcond⟩

/-! ## Duplicate removal -/

theorem mem_dedupAux_of_acc {x : Nat} : ∀ {acc l : List Nat}, x ∈ acc →
    x ∈ dedupAux acc l := by
  intro acc l
  induction l with
  | nil => intro h; exact h
  | cons y ys ih =>
    intro h
    by_cases hc : acc.contains y = true
    · exact ih h
    · refine ih ?_
      exact List.mem_cons_of_mem y h

theorem mem_dedupAux {x : Nat} : ∀ (acc l : List Nat),
    x ∈ dedupAux acc l ↔ (x ∈ acc ∨ x ∈ l) := by
  intro acc
  induction l with
  | nil => intro x; exact ⟨Or.inl, fun h => h.elim id (absurd · (List.not_mem_nil (a := x)))⟩
  | cons y ys ih =>
    intro x
    by_cases hc : acc.contains y = true
    · rw [dedupAux, if_pos hc]
      exact ih x
    · rw [dedupAux, if_neg hc]
      constructor
      · intro h
        obtain h' := ih (y :: acc) x |>.mp h
        rcases h' with h' | h'
        · rcases List.mem_cons.mp h' with rfl | h''
          · exact Or.inr (List.mem_cons_self ..)
          · exact Or.inl h''
        · exact Or.inr (List.mem_cons_of_mem y h')
      · intro h
        rcases h with h' | h'
        · refine mem_dedupAux_of_acc ?_
        · exact ih (y :: acc) x |>.mpr (Or.inr h')

theorem nodup_dedupAux : ∀ (l acc : List Nat), acc.Nodup → (dedupAux acc l).Nodup := by
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons y ys ih =>
    intro acc h
    by_cases hc : acc.contains y = true
    · exact ih acc h
    · refine ih (y :: acc) (List.nodup_cons.mpr ⟨?_, h⟩)
      intro hm
      exact hc (List.contains_iff_mem.mp hm)

theorem mem_dedup {x : Nat} {l : List Nat} : x ∈ dedupNat l ↔ x ∈ l := by
  constructor
  · intro h
    have := (mem_dedupAux [] l x).mp h
    rcases this with h' | h'
    · exact absurd h' (List.not_mem_nil (a := x))
    · exact h'
  · intro h
    exact (mem_dedupAux [] l x).mpr (Or.inr h)

/-! ## The bridge to the literal source count -/

theorem nodup_CayAvoiderList (n : Nat) (p : List Nat) : (CayAvoiderList n p).Nodup := by
  unfold CayAvoiderList
  exact nodup_dedup _ _ List.nodup_nil

theorem mem_CayAvoiderList_iff (n : Nat) (p : List Nat) (W : List Nat) :
    W ∈ CayAvoiderList n p ↔ (Packed W ∧ W.length = n ∧ Avoids p W) := by
  unfold CayAvoiderList
  constructor
  · intro h
    have h1 := (mem_dedupAux [] _ W).mp h
    obtain h1 : W ∈ (allWords n n).filter (fun W => packedB W && !(containsB p W)) := by
      rcases h1 with h' | h'
      · exact absurd h' (List.not_mem_nil W)
      · exact h'
    obtain ⟨hmem, hpb⟩ := List.mem_filter.mp h1
    obtain ⟨hpk, hc⟩ := Bool.and_eq_true.mp hpb
    have hcb : containsB p W = false := by
      cases hh : containsB p W with
      | false => rfl
      | true => exact absurd hh (by rw [hc] at hh; simp at hh)
    obtain ⟨hlenW, hlet⟩ := allWords_sound hmem
    refine ⟨packedB_iff.mp hpk, hlenW, ?_⟩
    intro hcon
    have hct : containsB p W = true := (containsB_iff p W).mpr hcon
    rw [hcb] at hct
    exact Bool.noConfusion hct
  · intro ⟨hP, hlen, hAv⟩
    refine (mem_dedupAux [] _ W).mpr (Or.inr ?_)
    refine List.mem_filter.mpr ⟨?_, ?_⟩
    · refine allWords_complete ?_ hlen
      intro x hx
      have hx1 : x ≤ maxL W := le_maxL hx
      have hx2 : maxL W ≤ W.length := maxL_le_length hP
      exact ⟨hP.2.1 x hx, by omega⟩
    · refine Bool.and_eq_true.mpr ⟨packedB_iff.mpr hP, ?_⟩
      have hcbf : containsB p W = false := by
        cases hh : containsB p W with
        | false => rfl
        | true => exact absurd ((containsB_iff p W).mp hh) hAv
      show (!(containsB p W)) = true
      rw [hcbf]; rfl

end Cayley
