import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Basic
set_option autoImplicit false
set_option warningAsError true
namespace Das
inductive Sign where
  | zero | plus | minus
  deriving DecidableEq
abbrev Pattern (n : ℕ) := Fin n → Fin n → Sign
def positive {n : ℕ} (A : Pattern n) (i j : Fin n) : ℤ :=
  if A i j = Sign.plus then 1 else 0
def negative {n : ℕ} (A : Pattern n) (i j : Fin n) : ℤ :=
  if A i j = Sign.minus then -1 else 0
def B {n : ℕ} (A : Pattern n) (i j : Fin n) : ℤ := positive A i j - negative A j i
theorem B_support {n : ℕ} (A : Pattern n) (i j : Fin n) :
    B A i j ≠ 0 ↔ A i j = Sign.plus ∨ A j i = Sign.minus := by
  unfold B positive negative
  split_ifs <;> simp_all
theorem B_overlap {n : ℕ} (A : Pattern n) (i j : Fin n)
    (h : A i j = Sign.plus) (g : A j i = Sign.minus) : B A i j = 2 := by
  simp [B, positive, negative, h, g]
def Support {n : ℕ} (A : Pattern n) (i j : Fin n) : Prop := A i j ≠ Sign.zero
instance {n : ℕ} (A : Pattern n) (i j : Fin n) : Decidable (Support A i j) :=
  inferInstanceAs (Decidable (A i j ≠ Sign.zero))
def CutIrreducible {n : ℕ} (R : Fin n → Fin n → Prop) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ →
    ∃ i ∈ S, ∃ j ∉ S, R i j
instance {n : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R] :
    Decidable (CutIrreducible R) := inferInstanceAs (Decidable (∀ S : Finset (Fin n),
      S.Nonempty → S ≠ Finset.univ → ∃ i ∈ S, ∃ j ∉ S, R i j))
-- A block decomposition uses a nonempty set of row/column indices and its
-- nonempty complement; the entire outgoing off-diagonal rectangular block is zero.
def BlockReducible {n : ℕ} (R : Fin n → Fin n → Prop) : Prop :=
  ∃ S : Set (Fin n), S.Nonempty ∧ Sᶜ.Nonempty ∧ ∀ i ∈ S, ∀ j ∈ Sᶜ, ¬ R i j
theorem cut_iff_no_block {n : ℕ} (R : Fin n → Fin n → Prop) :
    CutIrreducible R ↔ ¬ BlockReducible R := by
  classical
  constructor
  · intro h ⟨S, ⟨a, ha⟩, ⟨b, hb⟩, hz⟩
    have hn : S.toFinset ≠ Finset.univ := by
      intro he
      have : b ∈ S.toFinset := he.symm ▸ Finset.mem_univ b
      exact hb (Set.mem_toFinset.mp this)
    obtain ⟨i, hi, j, hj, hij⟩ := h S.toFinset ⟨a, Set.mem_toFinset.mpr ha⟩ hn
    exact hz i (Set.mem_toFinset.mp hi) j (by simpa using hj) hij
  · intro h S hs hp
    by_contra hn
    apply h
    refine ⟨(S : Set (Fin n)), ?_, ?_, ?_⟩
    · simpa using hs
    · obtain ⟨b, hb⟩ := (show ∃ b, b ∉ S from by simpa [Finset.eq_univ_iff_forall] using hp)
      exact ⟨b, hb⟩
    · intro i hi j hj hij
      exact hn ⟨i, hi, j, hj, hij⟩
def StronglyConnected {n : ℕ} (R : Fin n → Fin n → Prop) : Prop :=
  ∀ i j, Relation.ReflTransGen R i j
theorem cut_iff_strong {n : ℕ} (R : Fin n → Fin n → Prop) :
    CutIrreducible R ↔ StronglyConnected R := by
  classical
  constructor
  · intro h i j
    let S := Finset.univ.filter (fun k => Relation.ReflTransGen R i k)
    have hi : i ∈ S := by simp [S, Relation.ReflTransGen.refl]
    by_contra hj
    have hp : S ≠ Finset.univ := by
      intro he
      have : j ∈ S := he.symm ▸ Finset.mem_univ j
      exact hj (Finset.mem_filter.mp this).2
    obtain ⟨a, ha, b, hb, hab⟩ := h S ⟨i, hi⟩ hp
    apply hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2.tail hab⟩
  · intro h S hs hp
    obtain ⟨i, hi⟩ := hs
    obtain ⟨j, hj⟩ := (show ∃ b, b ∉ S from by simpa [Finset.eq_univ_iff_forall] using hp)
    by_contra hn
    have closed : ∀ a ∈ S, ∀ b, R a b → b ∈ S := by
      intro a ha b hab
      by_contra hb
      exact hn ⟨a, ha, b, hb, hab⟩
    have reach : ∀ b, Relation.ReflTransGen R i b → b ∈ S := by
      intro b hb
      induction hb with
      | refl => exact hi
      | @tail b c _ hbc ih => exact closed b ih c hbc
    exact hj (reach j (h i j))
def APIrreducible {n : ℕ} (A : Pattern n) : Prop :=
  CutIrreducible (Support A) ∧
  (∀ i, ∃ j, A i j = Sign.plus) ∧ (∀ j, ∃ i, A i j = Sign.plus) ∧
  CutIrreducible (fun i j => B A i j ≠ 0)
instance {n : ℕ} (A : Pattern n) : Decidable (APIrreducible A) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
def erase {n : ℕ} (A : Pattern n) (r c : Fin n) : Pattern n :=
  fun i j => if i = r ∧ j = c then Sign.zero else A i j
def MinimalAP {n : ℕ} (A : Pattern n) : Prop :=
  APIrreducible A ∧ ∀ i j, A i j ≠ Sign.zero → ¬ APIrreducible (erase A i j)
instance {n : ℕ} (A : Pattern n) : Decidable (MinimalAP A) :=
  inferInstanceAs (Decidable (APIrreducible A ∧ ∀ i j, A i j ≠ Sign.zero → ¬ APIrreducible (erase A i j)))
def ZeroDiagonal {n : ℕ} (A : Pattern n) : Prop := ∀ i, A i i = Sign.zero
def nonzeros {n : ℕ} (A : Pattern n) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => A p.1 p.2 ≠ Sign.zero)).card
def SourceConjecture : Prop := ∀ n : ℕ, 0 < n → ∀ A : Pattern n,
  ZeroDiagonal A → MinimalAP A → nonzeros A ≤ 2*n-2
end Das
