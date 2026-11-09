import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.GroupTheory.Perm.ClosureSwap
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

set_option linter.unnecessarySeqFocus false

namespace Amoeba
open Equiv
variable {V : Type*}
-- An elementary edge replacement, allowing a neutral move.
def Edit (G H : SimpleGraph V) : Prop := G = H ∨
  ∃ a b c d : V, G.Adj a b ∧ ¬G.Adj c d ∧ c ≠ d ∧
    ∀ x y, H.Adj x y ↔
      (G.Adj x y ∧ ¬((x = a ∧ y = b) ∨ (x = b ∧ y = a))) ∨
      (x = c ∧ y = d) ∨ (x = d ∧ y = c)

def Step (G H : SimpleGraph V) : Prop := Nonempty (G ≃g H) ∧ Edit G H
inductive Reach : SimpleGraph V → SimpleGraph V → Prop
  | refl (G) : Reach G G
  | next {G H K} : Reach G H → Step H K → Reach G K

theorem Reach.trans {G H K : SimpleGraph V} (h : Reach G H) (k : Reach H K) : Reach G K := by
  induction k with
  | refl => exact h
  | next _ hs ih => exact .next ih hs

def rel (p : Perm V) (G : SimpleGraph V) : SimpleGraph V := G.comap p
@[simp] theorem rel_adj (p : Perm V) (G : SimpleGraph V) (x y) :
    (rel p G).Adj x y ↔ G.Adj (p x) (p y) := Iff.rfl
@[simp] theorem rel_one (G : SimpleGraph V) : rel 1 G = G := by ext; rfl
@[simp] theorem rel_mul (p q : Perm V) (G : SimpleGraph V) :
    rel q (rel p G) = rel (p*q) G := by ext; rfl

def relIso (p : Perm V) (G : SimpleGraph V) : rel p G ≃g G :=
  { toEquiv := p, map_rel_iff' := by intros; rfl }

theorem edit_rel {G H : SimpleGraph V} (h : Edit G H) (p : Perm V) :
    Edit (rel p G) (rel p H) := by
  rcases h with rfl | ⟨a,b,c,d,hab,hcd,hne,h⟩
  · exact Or.inl rfl
  right
  refine ⟨p.symm a,p.symm b,p.symm c,p.symm d,?_,?_,?_,?_⟩
  · simpa using hab
  · simpa using hcd
  · exact fun he => hne (p.symm.injective he)
  · intro x y
    simpa only [rel_adj, Equiv.eq_symm_apply] using h (p x) (p y)

theorem reach_rel {G H : SimpleGraph V} (h : Reach G H) (p : Perm V) :
    Reach (rel p G) (rel p H) := by
  induction h with
  | refl => exact .refl _
  | @next H K _ hs ih =>
    apply Reach.next ih
    refine ⟨?_,edit_rel hs.2 p⟩
    exact ⟨(relIso p H).trans (hs.1.some.trans (relIso p K).symm)⟩

def moves (G : SimpleGraph V) : Submonoid (Perm V) where
  carrier := {p | Reach G (rel p G)}
  one_mem' := by simpa using Reach.refl G
  mul_mem' := by
    intro p q hp hq
    exact hq.trans (by simpa using reach_rel hp q)

theorem feasible {G : SimpleGraph V} (p : Perm V) (h : Edit G (rel p G)) : p ∈ moves G :=
  Reach.next (.refl G) ⟨⟨(relIso p G).symm⟩,h⟩



def base : SimpleGraph (Fin 5) where
  Adj x y := (x.val,y.val) ∈ ([(0,1),(1,0),(1,3),(3,1),(1,4),(4,1),
    (2,3),(3,2),(2,4),(4,2),(3,4),(4,3)] : List (Nat × Nat))
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩
instance : DecidableRel base.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ (_ : List (Nat × Nat))))

instance (p : Perm (Fin 5)) : DecidableRel (rel p base).Adj := fun _ _ => inferInstanceAs (Decidable (base.Adj _ _))

abbrev sw (x y : Fin 5) := Equiv.swap x y

theorem move12 : sw 1 2 ∈ moves base := by
  apply feasible
  right
  exact ⟨0,1,0,2,by decide,by decide,by decide,by decide⟩
theorem move23 : sw 2 3 ∈ moves base := by
  apply feasible
  right
  exact ⟨1,3,1,2,by decide,by decide,by decide,by decide⟩
theorem move34 : sw 3 4 ∈ moves base := by
  apply feasible
  left
  ext x y
  change base.Adj x y ↔ base.Adj _ _
  revert x y
  decide

theorem moveA : sw 0 2 * sw 1 4 ∈ moves base := by
  apply feasible
  right
  exact ⟨2,3,0,3,by decide,by decide,by decide,by decide⟩

theorem move14 : sw 1 4 ∈ moves base :=
  SubmonoidClass.swap_mem_trans (moves base)
    (SubmonoidClass.swap_mem_trans (moves base) move12 move23) move34

theorem move02 : sw 0 2 ∈ moves base := by
  have h := (moves base).mul_mem moveA move14
  have eq : (sw 0 2 * sw 1 4) * sw 1 4 = sw 0 2 := by simp [mul_assoc]
  rwa [eq] at h

theorem all_base_swaps (x y : Fin 5) : sw x y ∈ moves base := by
  have root (z : Fin 5) : sw 2 z ∈ moves base := by
    fin_cases z
    · simpa [Equiv.swap_comm] using move02
    · simpa [Equiv.swap_comm] using move12
    · convert (moves base).one_mem using 1 <;> decide
    · exact move23
    · exact SubmonoidClass.swap_mem_trans (moves base) move23 move34
  exact SubmonoidClass.swap_mem_trans (moves base)
    (by simpa [Equiv.swap_comm] using root x) (root y)

-- Adjoining an arbitrary finite set of isolated vertices.
def pad {W : Type*} (G : SimpleGraph (Fin 5)) : SimpleGraph (Fin 5 ⊕ W) where
  Adj x y := match x,y with | .inl a,.inl b => G.Adj a b | _,_ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> simp_all [G.adj_comm]⟩
  loopless := ⟨by intro x; cases x <;> simp⟩

def padIso {W : Type*} {G H : SimpleGraph (Fin 5)} (i : G ≃g H) :
    (pad G : SimpleGraph (Fin 5 ⊕ W)) ≃g (pad H : SimpleGraph (Fin 5 ⊕ W)) where
  toEquiv := Equiv.sumCongr i.toEquiv (Equiv.refl W)
  map_rel_iff' := by intro x y; cases x <;> cases y <;> simp [pad, i.map_adj_iff]

theorem pad_edit {W : Type*} {G H : SimpleGraph (Fin 5)} (h : Edit G H) :
    Edit (pad G : SimpleGraph (Fin 5 ⊕ W)) (pad H) := by
  rcases h with rfl | ⟨a,b,c,d,hab,hcd,hne,h⟩
  · exact .inl rfl
  right
  refine ⟨.inl a,.inl b,.inl c,.inl d,hab,hcd,by simpa using hne,?_⟩
  intro x y
  cases x <;> cases y <;> simp_all [pad]

theorem pad_reach {W : Type*} {G H : SimpleGraph (Fin 5)} (h : Reach G H) :
    Reach (pad G : SimpleGraph (Fin 5 ⊕ W)) (pad H) := by
  induction h with
  | refl => exact .refl _
  | next _ hs ih => exact .next ih ⟨⟨padIso hs.1.some⟩,pad_edit hs.2⟩

theorem lift_swap {W : Type*} [DecidableEq W] (a b : Fin 5) :
    Equiv.swap (Sum.inl a : Fin 5 ⊕ W) (.inl b) ∈ moves (pad base) := by
  have h := pad_reach (W := W) (all_base_swaps a b)
  have eq : pad (rel (sw a b) base) = rel (Equiv.swap (.inl a) (.inl b))
      (pad base : SimpleGraph (Fin 5 ⊕ W)) := by
    ext x y
    cases x <;> cases y <;> simp [pad, rel, Equiv.swap_apply_def] <;> split_ifs <;> simp_all [pad]
  change Reach _ _
  rwa [eq] at h



theorem outside_swap {W : Type*} [DecidableEq W] (w : W) :
    Equiv.swap (Sum.inl (0 : Fin 5)) (Sum.inr w) ∈ moves (pad base) := by
  apply feasible
  right
  refine ⟨.inl 0,.inl 1,.inr w,.inl 1,by change base.Adj 0 1; decide,by simp [pad],by simp,?_⟩
  intro x y
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      fin_cases a <;> fin_cases b <;>
        simp [rel, pad, Equiv.swap_apply_def, base]
    | inr b =>
      fin_cases a <;> by_cases h : b = w <;>
        simp_all [rel, pad, Equiv.swap_apply_def, base]
  | inr a =>
    cases y with
    | inl b =>
      fin_cases b <;> by_cases h : a = w <;>
        simp_all [rel, pad, Equiv.swap_apply_def, base]
    | inr b =>
      by_cases h : a = w <;> by_cases k : b = w <;>
        simp_all [rel, pad, Equiv.swap_apply_def, base]

theorem pad_swaps {W : Type*} [DecidableEq W] (x y : Fin 5 ⊕ W) :
    Equiv.swap x y ∈ moves (pad base) := by
  have star (z : Fin 5 ⊕ W) : Equiv.swap (.inl 0) z ∈ moves (pad base) := by
    cases z with
    | inl a => exact lift_swap 0 a
    | inr w => exact outside_swap w
  exact SubmonoidClass.swap_mem_trans (moves (pad base))
    (by simpa [Equiv.swap_comm] using star x) (star y)

def Local (G : SimpleGraph V) : Prop := ∀ H : SimpleGraph V,
    Nonempty (G ≃g H) → Reach G H

theorem padded_local (t : Nat) : Local (pad base : SimpleGraph (Fin 5 ⊕ Fin t)) := by
  intro H ⟨i⟩
  have all (p : Perm (Fin 5 ⊕ Fin t)) : p ∈ moves (pad base) := by
    induction p using Equiv.Perm.swap_induction_on with
    | one => exact (moves (pad base)).one_mem
    | swap_mul p x y _ ih => exact (moves (pad base)).mul_mem (pad_swaps x y) ih
  have h := all i.symm.toEquiv
  change Reach _ _ at h
  have eq : rel i.symm.toEquiv (pad base) = H := by
    ext x y
    exact i.symm.map_adj_iff
  rwa [eq] at h

-- The based definition gives the source's pairwise formulation as well.
theorem local_between {G F H : SimpleGraph V} (h : Local G)
    (i : G ≃g F) (j : G ≃g H) : Reach F H := by
  have hh := h (rel i.toEquiv H)
    ⟨j.trans (relIso i.toEquiv H).symm⟩
  have hh' := reach_rel hh i.symm.toEquiv
  have a : rel i.symm.toEquiv G = F := by
    ext x y
    exact i.symm.map_adj_iff
  have b : rel i.symm.toEquiv (rel i.toEquiv H) = H := by
    ext x y
    simp
  rwa [a,b] at hh'

-- Literal eventual-locality definition, with t added isolated vertices.
def Global (G : SimpleGraph (Fin 5)) : Prop :=
  ∃ t0 : Nat, ∀ t ≥ t0, Local (pad G : SimpleGraph (Fin 5 ⊕ Fin t))

theorem base_global : Global base := ⟨0, fun t _ => padded_local t⟩

def hn5 : SimpleGraph (Fin 5) where
  Adj x y := x ≠ y ∧ ((2 ≤ x.val ∧ 2 ≤ y.val) ∨
    (x.val < 2 ∧ 2 ≤ y.val ∧ y.val - 2 ≤ x.val) ∨
    (y.val < 2 ∧ 2 ≤ x.val ∧ x.val - 2 ≤ y.val))
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩
instance : DecidableRel hn5.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
def HasUniversal (G : SimpleGraph V) : Prop := ∃ x, ∀ y, y ≠ x → G.Adj x y

theorem no_universal : ¬HasUniversal base := by unfold HasUniversal; decide

theorem hn_universal : HasUniversal hn5 := by
  exact ⟨2, by decide⟩

theorem base_not_iso : ¬ Nonempty (base ≃g hn5) := by
  rintro ⟨i⟩
  obtain ⟨x,hx⟩ := hn_universal
  apply no_universal
  refine ⟨i.symm x, fun y hy => ?_⟩
  apply i.map_adj_iff.mp
  simpa using hx (i y) (fun he => hy (i.injective (by simpa using he)))


theorem base_edges : base.edgeFinset.card = 6 := by decide

theorem base_min_degree : base.minDegree = 1 := by decide

-- Exact witness to the negation of the source's proposed characterization.
theorem source_counterexample : Global base ∧ base.minDegree = 1 ∧
    base.edgeFinset.card = Fintype.card (Fin 5) ^ 2 / 4 ∧
    ¬Nonempty (base ≃g hn5) := by
  exact ⟨base_global,base_min_degree,by simpa using base_edges,base_not_iso⟩


def CharacterizationAtFive : Prop := ∀ G : SimpleGraph (Fin 5),
  [DecidableRel G.Adj] → Global G → G.minDegree = 1 →
  (G.edgeFinset.card = Fintype.card (Fin 5) ^ 2 / 4 ↔ Nonempty (G ≃g hn5))

theorem source_refutation : ¬CharacterizationAtFive := by
  intro h
  exact base_not_iso ((h base base_global base_min_degree).mp (by simpa using base_edges))

#print axioms source_counterexample
#print axioms source_refutation
end Amoeba
