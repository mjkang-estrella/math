import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Tauto
set_option autoImplicit false
set_option warningAsError true
namespace Cayley

def maxL (w : List ℕ) : ℕ := w.foldr max 0
/-- Positive letters whose set is an initial interval, including the empty word. -/
def Packed (w : List ℕ) : Prop :=
  (∀ x ∈ w, 1 ≤ x) ∧ ∀ k, 1 ≤ k → k ≤ maxL w → k ∈ w

def Iso (p s : List ℕ) : Prop :=
  p.length = s.length ∧ ∀ i ∈ List.range p.length, ∀ j ∈ List.range p.length,
    i < j → ((p.getD i 0 < p.getD j 0 ↔ s.getD i 0 < s.getD j 0) ∧
    (p.getD i 0 = p.getD j 0 ↔ s.getD i 0 = s.getD j 0))
/-- Sublist means distinct positions in order; strict_indices below supplies the literal witness. -/
def Contains (p w : List ℕ) : Prop := ∃ s, s.Sublist w ∧ Iso p s

theorem strict_indices (p w : List ℕ) : Contains p w ↔
    ∃ s, Iso p s ∧ ∃ f : Fin s.length ↪o Fin w.length,
      ∀ i, s.get i = w.get (f i) := by
  simp only [Contains, List.sublist_iff_exists_fin_orderEmbedding_get_eq]
  aesop

def packedB (w : List ℕ) : Bool :=
  w.all (fun x => decide (1 ≤ x)) &&
    (List.range (maxL w)).all (fun k => w.contains (k+1))
def isoB (p s : List ℕ) : Bool :=
  p.length == s.length && (List.range p.length).all (fun i =>
    (List.range p.length).all (fun j => decide (i < j →
      ((p.getD i 0 < p.getD j 0 ↔ s.getD i 0 < s.getD j 0) ∧
       (p.getD i 0 = p.getD j 0 ↔ s.getD i 0 = s.getD j 0)))))
def containsB (p w : List ℕ) : Bool := w.sublists.any (isoB p)

theorem packedB_iff (w : List ℕ) : packedB w = true ↔ Packed w := by
  simp only [packedB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    List.contains_iff_mem, List.mem_range, Packed]
  constructor
  · rintro ⟨h, h'⟩
    refine ⟨h, fun k hk hm => ?_⟩
    have := h' (k-1) (by omega)
    simpa [Nat.sub_add_cancel hk] using this
  · rintro ⟨h, h'⟩
    exact ⟨h, fun k hk => h' (k+1) (by omega) (by omega)⟩
theorem isoB_iff (p s : List ℕ) : isoB p s = true ↔ Iso p s := by
  simp only [isoB, Iso, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
theorem containsB_iff (p w : List ℕ) : containsB p w = true ↔ Contains p w := by
  simp [containsB, List.any_eq_true, isoB_iff, Contains]

def allWords : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | n+1, m => (List.range m).flatMap fun a => (allWords n m).map ((a+1) :: ·)

theorem mem_allWords (n m : ℕ) (w : List ℕ) :
    w ∈ allWords n m ↔ w.length = n ∧ ∀ x ∈ w, 1 ≤ x ∧ x ≤ m := by
  induction n generalizing w with
  | zero => cases w <;> simp [allWords]
  | succ n ih =>
    cases w with
    | nil => simp [allWords]
    | cons x xs =>
      simp only [allWords, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨a, ha, u, hu, he⟩
        cases he
        obtain ⟨hl, hb⟩ := (ih xs).mp hu
        refine ⟨by simp [hl], ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · have := List.mem_range.mp ha; omega
        · exact hb y hy
      · rintro ⟨hl, hb⟩
        obtain ⟨hx, hxm⟩ := hb x (by simp)
        refine ⟨x-1, List.mem_range.mpr (by omega), xs, ?_, by simp [Nat.sub_add_cancel hx]⟩
        apply (ih xs).mpr
        exact ⟨by simpa using hl, fun y hy => hb y (by simp [hy])⟩

theorem nodup_allWords (n m : ℕ) : (allWords n m).Nodup := by
  induction n with
  | zero => simp [allWords]
  | succ n ih =>
    apply List.nodup_flatMap.mpr
    constructor
    · intro a _
      exact ih.map (by intro u v h; exact List.cons.inj h |>.2)
    · apply List.nodup_range.imp
      intro a b hab
      apply List.disjoint_left.mpr
      intro u hu hv
      obtain ⟨v, _, he⟩ := List.mem_map.mp hu
      obtain ⟨z, _, he'⟩ := List.mem_map.mp hv
      have := List.cons.inj (he.trans he'.symm) |>.1
      exact hab (by omega)

theorem le_maxL {x : ℕ} {w : List ℕ} (h : x ∈ w) : x ≤ maxL w := by
  induction w with
  | nil => simp at h
  | cons y ys ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact (ih h).trans (Nat.le_max_right _ _)

/-- Generic bound, independent of the witness and the enumeration. -/
theorem maxL_le_length {w : List ℕ} (h : Packed w) : maxL w ≤ w.length := by
  have hs : Finset.Icc 1 (maxL w) ⊆ w.toFinset := by
    intro k hk
    exact List.mem_toFinset.mpr (h.2 k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2)
  have hc := Finset.card_le_card hs
  have hl := List.toFinset_card_le w
  simp only [Nat.card_Icc] at hc
  omega

def wordUniverse (n : ℕ) : Finset (List ℕ) :=
  ((allWords n n).filter packedB).toFinset

theorem mem_wordUniverse (n : ℕ) (w : List ℕ) :
    w ∈ wordUniverse n ↔ Packed w ∧ w.length = n := by
  simp only [wordUniverse, List.mem_toFinset, List.mem_filter, mem_allWords, packedB_iff]
  constructor
  · rintro ⟨⟨hl, _⟩, hp⟩; exact ⟨hp, hl⟩
  · rintro ⟨hp, hl⟩
    refine ⟨⟨hl, fun x hx => ⟨hp.1 x hx, ?_⟩⟩, hp⟩
    have := (le_maxL hx).trans (maxL_le_length hp)
    omega

/-- Explicit generic bijection: finite alphabet enumeration versus all Nat-valued source words. -/
def wordUniverseEquiv (n : ℕ) : {w // w ∈ wordUniverse n} ≃ {w // Packed w ∧ w.length = n} where
  toFun w := ⟨w.val, (mem_wordUniverse n w.val).mp w.property⟩
  invFun w := ⟨w.val, (mem_wordUniverse n w.val).mpr w.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def avoiders (n : ℕ) (p : List ℕ) : Finset (List ℕ) :=
  (wordUniverse n).filter (fun w => containsB p w = false)

theorem mem_avoiders (n : ℕ) (p w : List ℕ) :
    w ∈ avoiders n p ↔ Packed w ∧ w.length = n ∧ ¬ Contains p w := by
  simp only [avoiders, Finset.mem_filter, mem_wordUniverse]
  have hb : containsB p w = false ↔ ¬ Contains p w := by
    rw [← containsB_iff]; cases containsB p w <;> simp
  rw [hb]; tauto

def avoiderEquiv (n : ℕ) (p : List ℕ) :
    {w // w ∈ avoiders n p} ≃ {w // Packed w ∧ w.length = n ∧ ¬ Contains p w} where
  toFun w := ⟨w.val, (mem_avoiders n p w.val).mp w.property⟩
  invFun w := ⟨w.val, (mem_avoiders n p w.val).mpr w.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def avoiderList (n : ℕ) (p : List ℕ) : List (List ℕ) :=
  (allWords n n).filter (fun w => packedB w && !(containsB p w))
theorem card_eq_length (n : ℕ) (p : List ℕ) :
    (avoiders n p).card = (avoiderList n p).length := by
  have he : avoiders n p = (avoiderList n p).toFinset := by
    ext w
    simp only [avoiders, wordUniverse, avoiderList, Finset.mem_filter,
      List.mem_toFinset, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true']
    tauto
  rw [he]
  exact List.toFinset_card_of_nodup ((nodup_allWords n n).filter _)

/-- Source count is the cardinality of all Nat-valued source avoiders. -/
noncomputable def SourceCount (n : ℕ) (p : List ℕ) : ℕ :=
  Nat.card {w : List ℕ // Packed w ∧ w.length = n ∧ ¬ Contains p w}
theorem sourceCount_eq (n : ℕ) (p : List ℕ) : SourceCount n p = (avoiders n p).card := by
  rw [SourceCount, ← Nat.card_congr (avoiderEquiv n p), Nat.card_eq_fintype_card]
  simp

def SourceClaim : Prop := ∀ p q : List ℕ, Packed p → Packed q →
  p.length = q.length → maxL p ≤ maxL q → ∀ n, SourceCount n p ≥ SourceCount n q
end Cayley
