import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Logic.Relation
import Mathlib.Order.Nat
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
namespace Polyomino57
abbrev GridPoint := ℤ × ℤ
-- The four possibilities are exactly Manhattan distance one.
def Adj (p q : GridPoint) : Prop :=
  (q.1 = p.1 + 1 ∧ q.2 = p.2) ∨ (q.1 = p.1 - 1 ∧ q.2 = p.2) ∨
  (q.1 = p.1 ∧ q.2 = p.2 + 1) ∨ (q.1 = p.1 ∧ q.2 = p.2 - 1)
instance (p q : GridPoint) : Decidable (Adj p q) := inferInstanceAs (Decidable (_ ∨ _))
def Step (P : Finset GridPoint) (p q : GridPoint) : Prop := p ∈ P ∧ q ∈ P ∧ Adj p q
def EdgeConnected (P : Finset GridPoint) : Prop :=
  P.Nonempty ∧ ∀ p ∈ P, ∀ q ∈ P, Relation.ReflTransGen (Step P) p q
def translate (t : GridPoint) (P : Finset GridPoint) : Finset GridPoint :=
  P.image (fun p => (p.1 + t.1, p.2 + t.2))
def UniversalContainer (n : ℕ) (C : Finset GridPoint) : Prop :=
  EdgeConnected C ∧ ∀ P : Finset GridPoint, EdgeConnected P → P.card = n →
    ∃ t : GridPoint, translate t P ⊆ C
def EligibleSize (n m : ℕ) : Prop :=
  ∃ C : Finset GridPoint, C.card = m ∧ UniversalContainer n C
noncomputable def minimumSize (n : ℕ) : ℕ := by
  classical
  exact
  if h : ∃ m, EligibleSize n m then Nat.find h else 0
def SourceFormula : Prop := ∀ n : ℕ, 4 ≤ n → minimumSize n = (n*n-n+6)/2

theorem adj_symm {p q : GridPoint} (h : Adj p q) : Adj q p := by
  rcases h with h | h | h | h <;> simp only [Adj] <;> omega

theorem adj_manhattan (p q : GridPoint) :
    Adj p q ↔ (q.1-p.1).natAbs + (q.2-p.2).natAbs = 1 := by
  simp only [Adj]
  omega

theorem translate_card (t : GridPoint) (P : Finset GridPoint) :
    (translate t P).card = P.card := by
  apply Finset.card_image_of_injective
  intro a b h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (by omega) (by omega)

-- Translation changes neither orientation nor adjacency.
theorem adj_translate (t p q : GridPoint) :
    Adj (p.1+t.1,p.2+t.2) (q.1+t.1,q.2+t.2) ↔ Adj p q := by
  simp only [Adj]; omega

theorem boundary {P Q : Finset GridPoint} (hP : EdgeConnected P)
    (hne : Q.Nonempty) (hsub : Q ⊆ P) (hlt : Q ≠ P) :
    ∃ a ∈ Q, ∃ b ∈ P, b ∉ Q ∧ Adj a b := by
  obtain ⟨a,ha⟩ := hne
  have hex : ∃ b ∈ P, b ∉ Q := by
    by_contra! h
    exact hlt (Finset.Subset.antisymm hsub h)
  obtain ⟨b,hb,hbQ⟩ := hex
  have path := hP.2 a (hsub ha) b hb
  have cross : ∀ {x : GridPoint}, Relation.ReflTransGen (Step P) a x →
      x ∈ Q ∨ ∃ u ∈ Q, ∃ v ∈ P, v ∉ Q ∧ Adj u v := by
    intro x hx
    induction hx with
    | refl => exact Or.inl ha
    | @tail x y _ hxy ih =>
      rcases ih with hxQ | hdone
      · by_cases hyQ : y ∈ Q
        · exact Or.inl hyQ
        · exact Or.inr ⟨x,hxQ,y,hxy.2.1,hyQ,hxy.2.2⟩
      · exact Or.inr hdone
  exact (cross path).resolve_left hbQ

inductive Grown : Finset GridPoint → Prop
  | singleton (p : GridPoint) : Grown {p}
  | insert {Q : Finset GridPoint} {a b : GridPoint} :
      Grown Q → a ∈ Q → b ∉ Q → Adj a b → Grown (insert b Q)

-- Complete unbounded growth coverage: no finite box or normalization premise.
theorem growth_complete {P : Finset GridPoint} (hP : EdgeConnected P) : Grown P := by
  have extend : ∀ k : ℕ, ∀ Q : Finset GridPoint, Q ⊆ P → Q.Nonempty →
      Grown Q → P.card - Q.card = k → Grown P := by
    intro k
    induction k with
    | zero =>
      intro Q hsub _ hg hk
      have heq : Q = P := Finset.eq_of_subset_of_card_le hsub (by omega)
      simpa [heq] using hg
    | succ k ih =>
      intro Q hsub hne hg hk
      have hneP : Q ≠ P := by intro h; subst Q; simp at hk
      obtain ⟨a,ha,b,hb,hbQ,hab⟩ := boundary hP hne hsub hneP
      apply ih (insert b Q) (Finset.insert_subset hb hsub) (Finset.insert_nonempty _ _)
        (Grown.insert hg ha hbQ hab)
      rw [Finset.card_insert_of_notMem hbQ]
      have hle := Finset.card_le_card hsub
      omega
  obtain ⟨p,hp⟩ := hP.1
  exact extend _ {p} (Finset.singleton_subset_iff.mpr hp) (Finset.singleton_nonempty p)
    (Grown.singleton p) rfl
end Polyomino57
