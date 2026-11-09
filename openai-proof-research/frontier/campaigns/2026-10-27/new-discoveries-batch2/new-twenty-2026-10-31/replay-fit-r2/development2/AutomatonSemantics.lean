import TraceAction
import Mathlib.Data.Finset.Card
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace RACGNormal330264
open RACGSemantics330264
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Exact set of letters movable to the front, represented finitely. -/
def frontState : List V → Finset V
  | [] => ∅
  | a :: w => insert a ((frontState w).filter (fun b => G.Adj b a))

 theorem mem_frontState (a : V) (w : List V) : a ∈ frontState G w ↔ Movable G a w := by
  induction w with
  | nil => simp [frontState]
  | cons b w ih => simp only [frontState, Finset.mem_insert, Finset.mem_filter, ih, movable_cons]; tauto

 theorem frontState_clique (w : List V) {a b : V} (ha : a ∈ frontState G w)
    (hb : b ∈ frontState G w) (hne : a ≠ b) : G.Adj a b :=
  movable_clique G w ((mem_frontState G a w).mp ha) ((mem_frontState G b w).mp hb) hne

/-- The actual movable suffix letters of a word. -/
def suffixState (w : List V) : Finset V := frontState G w.reverse

 theorem suffixState_clique (w : List V) {a b : V} (ha : a ∈ suffixState G w)
    (hb : b ∈ suffixState G w) (hne : a ≠ b) : G.Adj a b :=
  frontState_clique G w.reverse ha hb hne

 theorem suffixState_append (w : List V) (a : V) :
    suffixState G (w ++ [a]) = insert a ((suffixState G w).filter (fun b => G.Adj b a)) := by
  simp [suffixState, frontState]

/-- Concrete state tables below must prove this specification, not assume recognition. -/
structure Machine (S : Type*) where
  state : S → Finset V
  next : S → V → Option S
  initial : S
  initial_empty : state initial = ∅
  next_spec : ∀ s a, (a ∈ state s → next s a = none) ∧
    (a ∉ state s → ∃ t, next s a = some t ∧
      state t = insert a ((state s).filter (fun b => G.Adj b a)))

namespace Machine
variable {G} {S : Type*} (M : Machine G S)

def Accept : S → List V → Prop
  | _, [] => True
  | s, a :: w => ∃ t, M.next s a = some t ∧ Accept t w

instance (s : S) (w : List V) [Fintype S] [DecidableEq S] : Decidable (M.Accept s w) := by
  induction w generalizing s with
  | nil => exact isTrue trivial
  | cons a w ih => unfold Accept; infer_instance

 theorem accept_context (s : S) (u w : List V) (hu : Clean G u)
    (hs : M.state s = frontState G u) : M.Accept s w ↔ Clean G (w.reverse ++ u) := by
  induction w generalizing s u with
  | nil => simpa [Accept] using hu
  | cons a w ih =>
    have ha : a ∈ M.state s ↔ Movable G a u := by rw [hs, mem_frontState]
    by_cases hm : Movable G a u
    · have hn := (M.next_spec s a).1 (ha.mpr hm)
      have hc : ¬ Clean G (w.reverse ++ a :: u) := by
        intro h; exact (clean_append_right G h).2 hm
      simp only [Accept, hn, Option.noConfusion, false_and, exists_false,
        List.reverse_cons, List.append_assoc, List.singleton_append]
      constructor
      · rintro ⟨t, ht, _⟩; cases ht
      · intro h; exact False.elim (hc h)
    · obtain ⟨t, ht, hst⟩ := (M.next_spec s a).2 (fun h => hm (ha.mp h))
      have hu' : Clean G (a :: u) := ⟨hu, hm⟩
      have hs' : M.state t = frontState G (a :: u) := by rw [hst, hs]; rfl
      simp only [Accept, ht, Option.some.injEq, exists_eq_left,
        List.reverse_cons, List.append_assoc, List.singleton_append]
      constructor
      · rintro ⟨t', he, hw⟩; subst t'; exact (ih t (a :: u) hu' hs').mp hw
      · intro hw; exact ⟨t, rfl, (ih t (a :: u) hu' hs').mpr hw⟩

 theorem accepts_iff_reduced (w : List V) : M.Accept M.initial w ↔ (system G).IsReduced w := by
  have h := M.accept_context M.initial [] w (clean_nil G) (by simpa [frontState] using M.initial_empty)
  simpa only [List.append_nil, ← reduced_iff_clean, CoxeterSystem.isReduced_reverse_iff] using h

#print axioms accepts_iff_reduced
end Machine
end RACGNormal330264
